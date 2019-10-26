use core::sync::atomic::{self, Ordering};

pub struct AtomicUsize(atomic::AtomicUsize);

pub mod compare;
use compare::{NeedsCompareOrdering, NeedsCompareAcqOp, CompareExchange};

impl AtomicUsize { // Relaxed
    /// Creates a new atomic integer.
    #[inline]
    pub const fn new(val: usize) -> AtomicUsize {
        AtomicUsize(atomic::AtomicUsize::new(val))
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
    /// [`acquire`].
    ///
    /// Intended to be used with one of the operations that do a store (📥) in ‘method chaining’:
    /// [`store`], [`swap`], or one of the [`fetch_*`] methods.
    ///
    /// # Examples
    /// ```
    /// let atomic = AtomicUsize::new(42);
    /// atomic.release().store(15);
    /// ```
    ///
    /// [`acquire`]: AtomicUsize::acquire
    /// [`store`]: NeedsStore::store
    /// [`swap`]: NeedsStore::swap
    /// [`fetch_*`]: NeedsStore::fetch_add
    #[must_use]
    #[inline]
    pub fn release(&self) -> NeedsStore {
        NeedsStore {
            atomic: self,
            ordering: Ordering::Release,
        }
    }

    /// Acquire data that is written by another thread. This is the second part of what needs to be
    /// a release/acquire pair on this atomic, where the sending thread must use [`release`].
    ///
    /// Intended to be used with one of the operations that do a load (📤) in ‘method chaining’:
    /// [`load`], [`swap`], or one of the [`fetch_*`] methods.
    ///
    /// Can also be combined with [`compare`] to always do an acquire, and conditionally do some
    /// other operations.
    ///
    /// # Examples
    /// ```
    /// let atomic = AtomicUsize::new(42);
    /// let value = atomic.acquire().load();
    /// ```
    ///
    /// [`release`]: AtomicUsize::release
    /// [`load`]: NeedsLoad::load
    /// [`swap`]: NeedsLoad::swap
    /// [`fetch_*`]: NeedsLoad::fetch_add
    /// [`compare`]: NeedsLoad::compare
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
    /// Intended to be used with one of the operations that do both a load and a store (📤 📥) in
    /// ‘method chaining’: [`swap`] or one of the [`fetch_*`] methods.
    ///
    /// # Examples
    /// ```
    /// let atomic = AtomicUsize::new(42);
    /// let value = atomic.acquire_and_release().swap();
    /// ```
    ///
    /// [`swap`]: NeedsRmw::swap
    /// [`fetch_*`]: NeedsRmw::fetch_add
    #[must_use]
    #[inline]
    pub fn acquire_and_release(&self) -> NeedsRmw {
        NeedsRmw {
            atomic: self,
            ordering: Ordering::AcqRel,
        }
    }

    /// Compare the atomic integer to a value, and take some action if successful.
    ///
    /// Every use of `compare` can be followed by multiple options, but must be always finish with
    /// [`swap`] or [`store`].
    ///
    /// `compare` uses the builder pattern to set up an `compare_exchange` with the right flags, and
    /// uses the type system to prevent invalid combinations (this makes the API documentation
    /// harder to navigate though).
    ///
    /// The final return value of the builder is `Result<usize, usize>`: a result indicating whether
    /// the new value was written and containing the previous value. On success this value is
    /// guaranteed to be equal to `current`.
    ///
    /// # Possible invocations
    ///
    /// - [`swap`]: Stores a value into the atomic integer, returning the previous value.
    ///   Must always be present as the final method.
    /// - [`weak`]: Use a weak comparison, that may spuriously fail even when the comparison
    ///   succeeds. TODO. Must be the first option after `compare`.
    /// - One of the release/acquire orderings: [`acquire`], [`release`], or
    ///   [`acquire_and_release`].
    /// - In vary rare cases you may want to combine [`acquire`] or [`release`] with
    ///   [`sequential_consistency`].
    ///
    /// Note: the order of invocation matters.
    ///
    /// ```text
    /// atomic.compare(current).swap(new);
    /// atomic.compare(current).acquire().swap(new);
    /// atomic.compare(current).release().swap(new);
    /// atomic.compare(current).acquire_and_release().swap(new);
    /// atomic.compare(current).acquire().sequential_consistency().swap(new);
    /// atomic.compare(current).release().sequential_consistency().swap(new);
    ///
    /// atomic.compare(current).weak().swap(new);
    /// atomic.compare(current).weak().acquire().swap(new);
    /// atomic.compare(current).weak().release().swap(new);
    /// atomic.compare(current).weak().acquire_and_release().swap(new);
    /// atomic.compare(current).weak().acquire().sequential_consistency().swap(new);
    /// atomic.compare(current).weak().release().sequential_consistency().swap(new);
    /// ```
    ///
    /// # Examples
    /// ```
    /// atomic.compare(current).swap(new);
    /// atomic.compare_and_swap(current, new);
    /// // Equals std_atomic.compare_and_swap(current, new, Ordering::Release);
    ///
    /// // Order matters!
    /// // This will always acquire, and only set the value if the comparison succeeds.
    /// atomic.acquire().compare(current).weak().store(new);
    /// // This will do the comparison, and only acquire and set the value on success.
    /// atomic.compare(current).acquire().weak().store(new);
    /// // Equal to:
    /// atomic.compare_exchange_weak(current, new, Ordering::Acquire, Ordering::Acquire);
    /// ```
    ///
    /// [`swap`]: compare::NeedsCompareOrdering::swap
    /// [`store`]: compare::NeedsCompareOrdering::store
    /// [`weak`]: compare::NeedsCompareOrdering::weak
    /// [`acquire`]: compare::NeedsCompareOrdering::acquire
    /// [`release`]: compare::NeedsCompareOrdering::release
    /// [`acquire_and_release`]: compare::NeedsCompareOrdering::acquire_and_release
    /// [`sequential_consistency`]: compare::NeedsCompareFinalizer::sequential_consistency
    #[must_use]
    #[inline]
    pub fn compare(&self, current: usize) -> NeedsCompareOrdering {
        NeedsCompareOrdering(CompareExchange::new(
            self,
            current,
            Ordering::Relaxed,
            Ordering::Relaxed,
            false,
        ))
    }

    /// 📤 Loads a value from the atomic integer.
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let some_var = AtomicUsize::new(5);
    ///
    /// assert_eq!(some_var.load(), 5);
    /// ```
    #[inline]
    pub fn load(&self) -> usize {
        self.0.load(Ordering::Relaxed)
    }

    /// 📥 Stores a value into the atomic integer.
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let some_var = AtomicUsize::new(5);
    ///
    /// some_var.store(10);
    /// assert_eq!(some_var.load(), 10);
    /// ```
    #[inline]
    pub fn store(&self, val: usize) {
        self.0.store(val, Ordering::Relaxed)
    }

    /// 📤 Stores a value into the atomic integer.
    ///
    /// 📥 Returns the previous value.
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let some_var = AtomicUsize::new(5);
    ///
    /// assert_eq!(some_var.swap(10), 5);
    /// assert_eq!(some_var.load(), 10);
    /// ```
    #[inline]
    pub fn swap(&self, val: usize) -> usize {
        self.0.swap(val, Ordering::Relaxed)
    }

    /// 📤 📥 Adds to the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let foo = AtomicUsize::new(5);
    /// assert_eq!(foo.fetch_add(10), 5);
    /// assert_eq!(foo.load(), 15);
    /// ```
    #[inline]
    pub fn fetch_add(&self, val: usize) -> usize {
        self.0.fetch_add(val, Ordering::Relaxed)
    }

    /// 📤 📥 Subtracts from the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let foo = AtomicUsize::new(20);
    /// assert_eq!(foo.fetch_sub(10), 20);
    /// assert_eq!(foo.load(), 10);
    /// ```
    #[inline]
    pub fn fetch_sub(&self, val: usize) -> usize {
        self.0.fetch_sub(val, Ordering::Relaxed)
    }

    /// 📤 📥 Bitwise "and" with the current value.
    ///
    /// Performs a bitwise "and" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let foo = AtomicUsize::new(0b101101);
    /// assert_eq!(foo.fetch_and(0b110011), 0b101101);
    /// assert_eq!(foo.load(), 0b100001);
    /// ```
    #[inline]
    pub fn fetch_and(&self, val: usize) -> usize {
        self.0.fetch_and(val, Ordering::Relaxed)
    }

    /// 📤 📥 Bitwise "nand" with the current value.
    ///
    /// Performs a bitwise "nand" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let foo = AtomicUsize::new(0x13);
    /// assert_eq!(foo.fetch_nand(0x31), 0x13);
    /// assert_eq!(foo.load(), !(0x13 & 0x31));
    /// ```
    #[inline]
    pub fn fetch_nand(&self, val: usize) -> usize {
        self.0.fetch_nand(val, Ordering::Relaxed)
    }

    /// 📤 📥 Bitwise "or" with the current value.
    ///
    /// Performs a bitwise "or" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let foo = AtomicUsize::new(0b101101);
    /// assert_eq!(foo.fetch_or(0b110011), 0b101101);
    /// assert_eq!(foo.load(), 0b111111);
    /// ```
    #[inline]
    pub fn fetch_or(&self, val: usize) -> usize {
        self.0.fetch_or(val, Ordering::Relaxed)
    }

    /// 📤 📥 Bitwise "xor" with the current value.
    ///
    /// Performs a bitwise "xor" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let foo = AtomicUsize::new(0b101101);
    /// assert_eq!(foo.fetch_xor(0b110011), 0b101101);
    /// assert_eq!(foo.load(), 0b011110);
    /// ```
    #[inline]
    pub fn fetch_xor(&self, val: usize) -> usize {
        self.0.fetch_xor(val, Ordering::Relaxed)
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
    pub fn swap(self, val: usize) -> usize {
        self.atomic.0.swap(val, self.ordering)
    }

    pub fn compare(&self, current: usize) -> NeedsCompareAcqOp {
        NeedsCompareAcqOp(CompareExchange::new(
            self.atomic,
            current,
            self.ordering,
            self.ordering,
            false,
        ))
    }

    /// Adds to the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_add(&self, val: usize) -> usize {
        self.atomic.0.fetch_add(val, self.ordering)
    }

    /// Subtracts from the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_sub(&self, val: usize) -> usize {
        self.atomic.0.fetch_sub(val, self.ordering)
    }

    /// Bitwise "and" with the current value.
    ///
    /// Performs a bitwise "and" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_and(&self, val: usize) -> usize {
        self.atomic.0.fetch_and(val, self.ordering)
    }

    /// Bitwise "nand" with the current value.
    ///
    /// Performs a bitwise "nand" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_nand(&self, val: usize) -> usize {
        self.atomic.0.fetch_nand(val, self.ordering)
    }

    /// Bitwise "or" with the current value.
    ///
    /// Performs a bitwise "or" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_or(&self, val: usize) -> usize {
        self.atomic.0.fetch_or(val, self.ordering)
    }

    /// Bitwise "xor" with the current value.
    ///
    /// Performs a bitwise "xor" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_xor(&self, val: usize) -> usize {
        self.atomic.0.fetch_xor(val, self.ordering)
    }

    #[inline]
    pub fn sequential_consistency(mut self) -> Self {
        self.ordering = Ordering::SeqCst;
        self
    }
}

pub struct NeedsStore<'a> {
    atomic: &'a AtomicUsize,
    ordering: Ordering,
}

impl NeedsStore<'_> {
    /// Stores a value into the atomic integer.
    #[inline]
    pub fn store(self, val: usize) {
        self.atomic.0.store(val, self.ordering)
    }

    /// Stores a value into the atomic integer, returning the previous value.
    #[inline]
    pub fn swap(self, val: usize) -> usize {
        self.atomic.0.swap(val, self.ordering)
    }

    /// Adds to the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_add(&self, val: usize) -> usize {
        self.atomic.0.fetch_add(val, self.ordering)
    }

    /// Subtracts from the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_sub(&self, val: usize) -> usize {
        self.atomic.0.fetch_sub(val, self.ordering)
    }

    /// Bitwise "and" with the current value.
    ///
    /// Performs a bitwise "and" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_and(&self, val: usize) -> usize {
        self.atomic.0.fetch_and(val, self.ordering)
    }

    /// Bitwise "nand" with the current value.
    ///
    /// Performs a bitwise "nand" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_nand(&self, val: usize) -> usize {
        self.atomic.0.fetch_nand(val, self.ordering)
    }

    /// Bitwise "or" with the current value.
    ///
    /// Performs a bitwise "or" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_or(&self, val: usize) -> usize {
        self.atomic.0.fetch_or(val, self.ordering)
    }

    /// Bitwise "xor" with the current value.
    ///
    /// Performs a bitwise "xor" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_xor(&self, val: usize) -> usize {
        self.atomic.0.fetch_xor(val, self.ordering)
    }

    #[inline]
    pub fn sequential_consistency(mut self) -> Self {
        self.ordering = Ordering::SeqCst;
        self
    }
}

pub struct NeedsRmw<'a> {
    atomic: &'a AtomicUsize,
    ordering: Ordering,
}

impl NeedsRmw<'_> {
    /// Stores a value into the atomic integer, returning the previous value.
    #[inline]
    pub fn swap(self, val: usize) -> usize {
        self.atomic.0.swap(val, self.ordering)
    }

    /// Adds to the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_add(&self, val: usize) -> usize {
        self.atomic.0.fetch_add(val, self.ordering)
    }

    /// Subtracts from the current value, returning the previous value.
    ///
    /// This operation wraps around on overflow.
    #[inline]
    pub fn fetch_sub(&self, val: usize) -> usize {
        self.atomic.0.fetch_sub(val, self.ordering)
    }

    /// Bitwise "and" with the current value.
    ///
    /// Performs a bitwise "and" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_and(&self, val: usize) -> usize {
        self.atomic.0.fetch_and(val, self.ordering)
    }

    /// Bitwise "nand" with the current value.
    ///
    /// Performs a bitwise "nand" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_nand(&self, val: usize) -> usize {
        self.atomic.0.fetch_nand(val, self.ordering)
    }

    /// Bitwise "or" with the current value.
    ///
    /// Performs a bitwise "or" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_or(&self, val: usize) -> usize {
        self.atomic.0.fetch_or(val, self.ordering)
    }

    /// Bitwise "xor" with the current value.
    ///
    /// Performs a bitwise "xor" operation on the current value and the argument `value`, and
    /// sets the new value to the result.
    ///
    /// Returns the previous value.
    #[inline]
    pub fn fetch_xor(&self, val: usize) -> usize {
        self.atomic.0.fetch_xor(val, self.ordering)
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

        atomic.compare(15);
    }
}
