use core::sync::atomic::{self, Ordering};

pub struct AtomicUsize(atomic::AtomicUsize);

impl AtomicUsize { // Relaxed
    /// Creates a new atomic integer.
    #[inline]
    pub const fn new(value: usize) -> AtomicUsize {
        AtomicUsize(atomic::AtomicUsize::new(value))
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    #[inline]
    pub fn get_mut(&mut self) -> &mut usize {
        self.0.get_mut()
    }

    /// Loads a value from the atomic integer.
    #[inline]
    pub fn into_inner(self) -> usize {
        self.0.into_inner()
    }

    /// Release data that is written by this thread to another thread. This is the first part of
    /// what needs to be a release/acquire pair on this atomic, where the receiving thread must use
    /// `acquire`.
    ///
    /// Intended to be used with one of the methods of [`NeedsStore`] as `method chaining`.
    ///
    /// # Example
    /// ```
    /// let atomic = AtomicUsize::new(42);
    /// atomic.release().store(15);
    /// ```
    #[must_use]
    #[inline]
    pub fn release(&self) -> NeedsStore {
        NeedsStore {
            atomic: self,
            ordering: Ordering::Release,
        }
    }

    /// Acquire data that is written by another thread. This is the second part of what needs to be
    /// a release/acquire pair on this atomic, where the sending thread must use `release`.
    ///
    /// Intended to be used with one of the methods of [`NeedsLoad`] as `method chaining`.
    ///
    /// # Example
    /// ```
    /// let atomic = AtomicUsize::new(42);
    /// let value = atomic.acquire().load();
    /// ```
    #[must_use]
    #[inline]
    pub fn acquire(&self) -> NeedsLoad {
        NeedsLoad {
            atomic: self,
            ordering: Ordering::Acquire,
        }
    }

    /// Acquire data that is written by another thread, and release data written by this thread to
    /// others.
    ///
    /// Intended to be used with one of the methods of [`NeedsRmw`] as `method chaining`.
    ///
    /// # Example
    /// ```
    /// let atomic = AtomicUsize::new(42);
    /// let value = atomic.acquire_and_release().swap();
    /// ```
    #[must_use]
    #[inline]
    pub fn acquire_and_release(&self) -> NeedsRmw {
        NeedsRmw {
            atomic: self,
            ordering: Ordering::AcqRel,
        }
    }

    /// Stores a value into the atomic integer if the current value is the same as
    /// the `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and
    /// containing the previous value. On success this value is guaranteed to be equal to
    /// `current`.
    ///
    /// # Example
    /// ```
    /// // Order matters!
    /// // This will always acquire, and only set the value if the comparison succeeds.
    /// atomic.acquire().compare(current).weak().set(new);
    /// // This will do the comparison, and only acquire and set the value on success.
    /// atomic.compare(current).acquire().weak().set(new);
    /// // Equal to:
    /// atomic.compare_exchange_weak(current, new, Ordering::Acquire, Ordering::Acquire);
    /// ```
    #[must_use]
    #[inline]
    pub fn compare_exchange(&self, current: usize, new: usize) -> NeedsComparedOp {
        NeedsComparedOp {
            atomic: self,
            current,
            new,
            ordering_success: Ordering::Relaxed,
            ordering_failure: Ordering::Relaxed,
            weak: false,
        }
    }

    /// Loads a value from the atomic integer.
    #[inline]
    pub fn load(&self) -> usize {
        self.0.load(Ordering::Relaxed)
    }

    /// Stores a value into the atomic integer.
    #[inline]
    pub fn store(&self, value: usize) {
        self.0.store(value, Ordering::Relaxed)
    }

    /// Stores a value into the atomic integer, returning the previous value.
    #[inline]
    pub fn swap(&self, value: usize) -> usize {
        self.0.swap(value, Ordering::Relaxed)
    }

    /// Stores a value into the atomic integer if the current value is the same as the `current`
    /// value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    #[inline]
    pub fn compare_and_swap(&self, current: usize, new: usize) -> usize {
        match self.0.compare_exchange(current, new, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(x) => x,
            Err(x) => x,
        }
    }

    /// Adds to the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_add(&self, value: usize) -> usize {
        self.0.fetch_add(value, Ordering::Relaxed)
    }

    /// Subtracts from the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_sub(&self, value: usize) -> usize {
        self.0.fetch_sub(value, Ordering::Relaxed)
    }

    /// Bitwise "and" with the current value.
    ///
    /// Performs a bitwise "and" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_and(&self, value: usize) -> usize {
        self.0.fetch_and(value, Ordering::Relaxed)
    }

    /// Bitwise "nand" with the current value.
    ///
    /// Performs a bitwise "nand" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_nand(&self, value: usize) -> usize {
        self.0.fetch_nand(value, Ordering::Relaxed)
    }

    /// Bitwise "or" with the current value.
    ///
    /// Performs a bitwise "or" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_or(&self, value: usize) -> usize {
        self.0.fetch_or(value, Ordering::Relaxed)
    }

    /// Bitwise "xor" with the current value.
    ///
    /// Performs a bitwise "xor" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_xor(&self, value: usize) -> usize {
        self.0.fetch_xor(value, Ordering::Relaxed)
    }
}

pub struct NeedsLoad<'a> {
    atomic: &'a AtomicUsize,
    ordering: Ordering,
}

impl NeedsLoad<'_> {
    /// Stores a value into the atomic integer.
    #[inline]
    pub fn load(self) -> usize {
        self.atomic.0.load(self.ordering)
    }

    /// Stores a value into the atomic integer, returning the previous value.
    #[inline]
    pub fn swap(self, value: usize) -> usize {
        self.atomic.0.swap(value, self.ordering)
    }

    /// Stores a value into the atomic integer if the current value is the same as the `current`
    /// value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    #[inline]
    pub fn compare_and_swap(&self, current: usize, new: usize) -> usize {
        match self.atomic.0.compare_exchange(current, new, self.ordering, self.ordering) {
            Ok(x) => x,
            Err(x) => x,
        }
    }

    /// Stores a value into the atomic integer if the current value is the same as
    /// the `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and
    /// containing the previous value. On success this value is guaranteed to be equal to
    /// `current`.
    #[must_use]
    #[inline]
    pub fn compare_exchange(&self, current: usize, new: usize) -> NeedsComparedAcqOp {
        NeedsComparedAcqOp {
            atomic: self,
            current,
            new,
            ordering_success: self.ordering,
            ordering_failure: self.ordering,
            weak: false,
        }
    }

    /// Adds to the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_add(&self, value: usize) -> usize {
        self.atomic.0.fetch_add(value, self.ordering)
    }

    /// Subtracts from the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_sub(&self, value: usize) -> usize {
        self.atomic.0.fetch_sub(value, self.ordering)
    }

    /// Bitwise "and" with the current value.
    ///
    /// Performs a bitwise "and" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_and(&self, value: usize) -> usize {
        self.atomic.0.fetch_and(value, self.ordering)
    }

    /// Bitwise "nand" with the current value.
    ///
    /// Performs a bitwise "nand" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_nand(&self, value: usize) -> usize {
        self.atomic.0.fetch_nand(value, self.ordering)
    }

    /// Bitwise "or" with the current value.
    ///
    /// Performs a bitwise "or" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_or(&self, value: usize) -> usize {
        self.atomic.0.fetch_or(value, self.ordering)
    }

    /// Bitwise "xor" with the current value.
    ///
    /// Performs a bitwise "xor" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_xor(&self, value: usize) -> usize {
        self.atomic.0.fetch_xor(value, self.ordering)
    }

    #[inline]
    pub fn sequential_consistency(&mut self) {
        self.ordering = Ordering::SeqCst;
    }
}

pub struct NeedsStore<'a> {
    atomic: &'a AtomicUsize,
    ordering: Ordering,
}

impl NeedsStore<'_> {
    /// Stores a value into the atomic integer.
    #[inline]
    pub fn store(self, value: usize) {
        self.atomic.0.store(value, self.ordering)
    }

    /// Stores a value into the atomic integer, returning the previous value.
    #[inline]
    pub fn swap(self, value: usize) -> usize {
        self.atomic.0.swap(value, self.ordering)
    }

    /// Adds to the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_add(&self, value: usize) -> usize {
        self.atomic.0.fetch_add(value, self.ordering)
    }

    /// Subtracts from the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_sub(&self, value: usize) -> usize {
        self.atomic.0.fetch_sub(value, self.ordering)
    }

    /// Bitwise "and" with the current value.
    ///
    /// Performs a bitwise "and" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_and(&self, value: usize) -> usize {
        self.atomic.0.fetch_and(value, self.ordering)
    }

    /// Bitwise "nand" with the current value.
    ///
    /// Performs a bitwise "nand" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_nand(&self, value: usize) -> usize {
        self.atomic.0.fetch_nand(value, self.ordering)
    }

    /// Bitwise "or" with the current value.
    ///
    /// Performs a bitwise "or" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_or(&self, value: usize) -> usize {
        self.atomic.0.fetch_or(value, self.ordering)
    }

    /// Bitwise "xor" with the current value.
    ///
    /// Performs a bitwise "xor" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_xor(&self, value: usize) -> usize {
        self.atomic.0.fetch_xor(value, self.ordering)
    }

    #[inline]
    pub fn sequential_consistency(&mut self) {
        self.ordering = Ordering::SeqCst;
    }
}

pub struct NeedsRmw<'a> {
    atomic: &'a AtomicUsize,
    ordering: Ordering,
}

impl NeedsRmw<'_> {
    /// Stores a value into the atomic integer, returning the previous value.
    #[inline]
    pub fn swap(self, value: usize) -> usize {
        self.atomic.0.swap(value, self.ordering)
    }

    /// Adds to the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_add(&self, value: usize) -> usize {
        self.atomic.0.fetch_add(value, self.ordering)
    }

    /// Subtracts from the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_sub(&self, value: usize) -> usize {
        self.atomic.0.fetch_sub(value, self.ordering)
    }

    /// Bitwise "and" with the current value.
    ///
    /// Performs a bitwise "and" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_and(&self, value: usize) -> usize {
        self.atomic.0.fetch_and(value, self.ordering)
    }

    /// Bitwise "nand" with the current value.
    ///
    /// Performs a bitwise "nand" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_nand(&self, value: usize) -> usize {
        self.atomic.0.fetch_nand(value, self.ordering)
    }

    /// Bitwise "or" with the current value.
    ///
    /// Performs a bitwise "or" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_or(&self, value: usize) -> usize {
        self.atomic.0.fetch_or(value, self.ordering)
    }

    /// Bitwise "xor" with the current value.
    ///
    /// Performs a bitwise "xor" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_xor(&self, value: usize) -> usize {
        self.atomic.0.fetch_xor(value, self.ordering)
    }
}

pub struct NeedsComparedOp<'a> {
    atomic: &'a AtomicUsize,
    current: usize,
    new: usize,
    ordering_success: Ordering,
    ordering_failure: Ordering,
    weak: bool,
}

impl NeedsComparedOp<'_> {
    #[inline]
    pub fn acquire(mut self) -> Result<usize, usize> {
        self.ordering_success = Ordering::AcqRel;
        self.compare_and_swap()
    }

    #[inline]
    pub fn release(mut self) -> Result<usize, usize> {
        self.ordering_success = Ordering::Release;
        self.compare_and_swap()
    }

    #[inline]
    pub fn acquire_and_release(mut self) -> Result<usize, usize> {
        self.ordering_success = Ordering::AcqRel;
        self.compare_and_swap()
    }

    /// Allow the compare-and-exchange to spuriously fail even when the comparison succeeds. This
    /// will yield better performance on some platforms.
    ///
    /// When to prefer `weak`? If you would have to introduce a loop only because of spurious
    /// failure, don't use it. But if you have a loop anyway, `weak` is the better choice.
    #[inline]
    pub fn weak(&mut self) {
        self.weak = true;
    }

    #[inline]
    pub fn sequential_consistency(&mut self) {
        self.ordering_success = Ordering::SeqCst;
        // TODO: figure out failure case
    }

    /// Stores a value into the atomic integer if the current value is the same as the `current`
    /// value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    #[inline]
    fn compare_and_swap(&self) -> Result<usize, usize> {
        match self.weak {
            false => self.atomic.0.compare_exchange(self.current,
                                                     self.new,
                                                     self.ordering_success,
                                                     self.ordering_failure),
            true => self.atomic.0.compare_exchange_weak(self.current,
                                                        self.new,
                                                        self.ordering_success,
                                                        self.ordering_failure),
        }
    }
}

pub struct NeedsComparedAcqOp<'a> {
    atomic: &'a AtomicUsize,
    current: usize,
    new: usize,
    ordering_success: Ordering, // Acquire, AcqRel or SeqCst
    ordering_failure: Ordering, // Acquire or SeqCst
    weak: bool,
}

impl NeedsComparedAcqOp<'_> {
    /// ```
    /// atomic.acquire().compare_exchange(current, new).weak().release();
    /// // Equal to:
    /// atomic.compare_exchange_weak(current, new, Ordering::AcqRel, Ordering::Acquire);
    /// ```
    #[inline]
    pub fn release(mut self) -> Result<usize, usize> {
        if self.ordering_success != Ordering::SeqCst {
            self.ordering_success = Ordering::AcqRel;
        }
        self.compare_and_swap()
    }

    /// Allow the compare-and-exchange to spuriously fail even when the comparison succeeds. This
    /// will yield better performance on some platforms.
    ///
    /// When to prefer `weak`? If you would have to introduce a loop only because of spurious
    /// failure, don't use it. But if you have a loop anyway, `weak` is the better choice.
    ///
    /// ```
    /// atomic.acquire().compare_exchange(current, new).weak().TODO();
    /// // Equal to:
    /// atomic.compare_exchange_weak(current, new, Ordering::Acquire, Ordering::Acquire);
    /// ```
    #[inline]
    pub fn weak(&mut self) {
        self.weak = true;
    }

    /// Stores a value into the atomic integer if the current value is the same as the `current`
    /// value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    #[inline]
    fn compare_and_swap(&self) -> Result<usize, usize> {
        match self.weak {
            false => self.atomic.0.compare_exchange(self.current,
                                                     self.new,
                                                     self.ordering_success,
                                                     self.ordering_failure),
            true => self.atomic.0.compare_exchange_weak(self.current,
                                                        self.new,
                                                        self.ordering_success,
                                                        self.ordering_failure),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::AtomicUsize;

    #[test]
    fn it_works() {
        let atomic = AtomicUsize::new(42);
        atomic.release().store(15);
        atomic.release().sequential_consistency().store(15);
    }
}
