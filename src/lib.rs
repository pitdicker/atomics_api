use core::sync::atomic::{self, Ordering};

pub struct AtomicUsize(atomic::AtomicUsize);

pub mod compare;
use compare::{NeedsCompareOrdering, NeedsCompareAcqOp, CompareExchange};

impl AtomicUsize {
    /// Creates a new atomic integer.
    #[inline]
    pub const fn new(val: usize) -> AtomicUsize {
        AtomicUsize(atomic::AtomicUsize::new(val))
    }

    /// Returns a mutable reference to the underlying integer.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    #[inline]
    pub fn get_mut(&mut self) -> &mut usize {
        self.0.get_mut()
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
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
    /// FIXME: mention [`sequential_consistency`]
    ///
    /// # Examples
    /// ```
    /// let atomic = AtomicUsize::new(42);
    /// atomic.release().store(15);
    /// ```
    ///
    /// [`acquire`]: AtomicUsize::acquire
    /// [`store`]: AtomicUsize::store
    /// [`swap`]: AtomicUsize::swap
    /// [`fetch_*`]: AtomicUsize::fetch_add
    /// [`sequential_consistency`]: NeedsStore::sequential_consistency
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
    /// FIXME: mention [`sequential_consistency`]
    ///
    /// # Examples
    /// ```
    /// let atomic = AtomicUsize::new(42);
    /// let value = atomic.acquire().load();
    /// ```
    ///
    /// [`release`]: AtomicUsize::release
    /// [`load`]: AtomicUsize::load
    /// [`swap`]: AtomicUsize::swap
    /// [`fetch_*`]: AtomicUsize::fetch_add
    /// [`compare`]: NeedsLoad::compare
    /// [`sequential_consistency`]: NeedsLoad::sequential_consistency
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
    /// [`swap`]: AtomicUsize::swap
    /// [`fetch_*`]: AtomicUsize::fetch_add
    #[must_use]
    #[inline]
    pub fn acquire_and_release(&self) -> NeedsRmw {
        NeedsRmw {
            atomic: self,
            ordering: Ordering::AcqRel,
        }
    }

    /// 📤 📥 Compare the atomic integer to a value, and take some action if successful.
    ///
    /// Every use of [`compare`] can be followed by multiple options, but must be always finish with
    /// [`swap`].
    ///
    /// [`compare`] uses the builder pattern to set up a `compare_exchange` with the right flags,
    /// and uses the type system to prevent invalid combinations (this makes the API documentation
    /// harder to navigate though).
    ///
    /// The final return value of the builder is `Result<usize, usize>`: a result indicating whether
    /// the new value was written and containing the previous value. On success this value is
    /// guaranteed to be equal to `current`.
    ///
    /// # Possible invocations
    ///
    /// - The first method that can be called after [`compare`] is [`weak`]. This allows the
    ///   compare-and-exchange to spuriously fail even when the comparison succeeds. This will yield
    ///   better performance on some platforms. If you already use [`compare`] in a loop, it is good
    ///   to use [`weak`].
    ///
    /// - Next you can supply release/acquire orderings, if you want to enforce any: [`acquire`],
    ///   [`release`], or [`acquire_and_release`].
    ///
    /// - In vary rare cases you may want to combine [`acquire`] or [`release`] with
    ///   [`sequential_consistency`].
    ///
    /// - Finish with [`swap`], which stores a value into the atomic integer, returning the previous
    ///   value.
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

    /// 📥 Stores the value of `val` into the atomic integer.
    ///
    /// 📤 Returns the previous value.
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

    /// 📥 Adds `val` to the current value, wrapping around on overflow.
    ///
    /// 📤 Returns the previous value.
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

    /// 📥 Subtracts `val` from the current value, wrapping around on overflow.
    ///
    /// 📤 Returns the previous value.
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

    /// 📥 Performs a bitwise "and" with `val` on the current value.
    ///
    /// 📤 Returns the previous value.
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

    /// 📥 Performs a bitwise "nand" with `val` on the current value.
    ///
    /// 📤 Returns the previous value.
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

    /// 📥 Performs a bitwise "or" with `val` on the current value.
    ///
    /// 📤 Returns the previous value.
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

    /// 📥 Performs a bitwise "xor" with `val` on the current value.
    ///
    /// 📤 Returns the previous value.
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
    /// FIXME: add doc comment
    #[inline]
    pub fn compare(&self, current: usize) -> NeedsCompareAcqOp {
        NeedsCompareAcqOp(CompareExchange::new(
            self.atomic,
            current,
            self.ordering,
            self.ordering,
            false,
        ))
    }

    /// FIXME: add doc comment
    #[inline]
    pub fn sequential_consistency(mut self) -> Self {
        self.ordering = Ordering::SeqCst;
        self
    }

    #[inline]
    pub fn load(self) -> usize {
        self.atomic.0.load(self.ordering)
    }

    #[inline]
    pub fn swap(self, val: usize) -> usize {
        self.atomic.0.swap(val, self.ordering)
    }

    #[inline]
    pub fn fetch_add(&self, val: usize) -> usize {
        self.atomic.0.fetch_add(val, self.ordering)
    }

    #[inline]
    pub fn fetch_sub(&self, val: usize) -> usize {
        self.atomic.0.fetch_sub(val, self.ordering)
    }

    #[inline]
    pub fn fetch_and(&self, val: usize) -> usize {
        self.atomic.0.fetch_and(val, self.ordering)
    }

    #[inline]
    pub fn fetch_nand(&self, val: usize) -> usize {
        self.atomic.0.fetch_nand(val, self.ordering)
    }

    #[inline]
    pub fn fetch_or(&self, val: usize) -> usize {
        self.atomic.0.fetch_or(val, self.ordering)
    }

    #[inline]
    pub fn fetch_xor(&self, val: usize) -> usize {
        self.atomic.0.fetch_xor(val, self.ordering)
    }
}

pub struct NeedsStore<'a> {
    atomic: &'a AtomicUsize,
    ordering: Ordering,
}

impl NeedsStore<'_> {
    /// FIXME: add doc comment
    #[inline]
    pub fn sequential_consistency(mut self) -> Self {
        self.ordering = Ordering::SeqCst;
        self
    }

    #[inline]
    pub fn store(self, val: usize) {
        self.atomic.0.store(val, self.ordering)
    }

    #[inline]
    pub fn swap(self, val: usize) -> usize {
        self.atomic.0.swap(val, self.ordering)
    }

    #[inline]
    pub fn fetch_add(&self, val: usize) -> usize {
        self.atomic.0.fetch_add(val, self.ordering)
    }

    #[inline]
    pub fn fetch_sub(&self, val: usize) -> usize {
        self.atomic.0.fetch_sub(val, self.ordering)
    }

    #[inline]
    pub fn fetch_and(&self, val: usize) -> usize {
        self.atomic.0.fetch_and(val, self.ordering)
    }

    #[inline]
    pub fn fetch_nand(&self, val: usize) -> usize {
        self.atomic.0.fetch_nand(val, self.ordering)
    }

    #[inline]
    pub fn fetch_or(&self, val: usize) -> usize {
        self.atomic.0.fetch_or(val, self.ordering)
    }

    #[inline]
    pub fn fetch_xor(&self, val: usize) -> usize {
        self.atomic.0.fetch_xor(val, self.ordering)
    }
}

pub struct NeedsRmw<'a> {
    atomic: &'a AtomicUsize,
    ordering: Ordering,
}

impl NeedsRmw<'_> {
    #[inline]
    pub fn swap(self, val: usize) -> usize {
        self.atomic.0.swap(val, self.ordering)
    }

    #[inline]
    pub fn fetch_add(&self, val: usize) -> usize {
        self.atomic.0.fetch_add(val, self.ordering)
    }

    #[inline]
    pub fn fetch_sub(&self, val: usize) -> usize {
        self.atomic.0.fetch_sub(val, self.ordering)
    }

    #[inline]
    pub fn fetch_and(&self, val: usize) -> usize {
        self.atomic.0.fetch_and(val, self.ordering)
    }

    #[inline]
    pub fn fetch_nand(&self, val: usize) -> usize {
        self.atomic.0.fetch_nand(val, self.ordering)
    }

    #[inline]
    pub fn fetch_or(&self, val: usize) -> usize {
        self.atomic.0.fetch_or(val, self.ordering)
    }

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
