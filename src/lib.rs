use core::sync::atomic::{self, fence, Ordering};

pub struct AtomicUsize(atomic::AtomicUsize);

impl AtomicUsize {
    /// Creates a new atomic integer.
    #[inline]
    pub const fn new(val: usize) -> AtomicUsize {
        AtomicUsize(atomic::AtomicUsize::new(val))
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
    /// use std::cell::UnsafeCell;
    /// use atomics_api::AtomicUsize;
    ///
    /// const NOT_IN_USE: usize = 0;
    /// const WRITING: usize = 1;
    /// let guard = AtomicUsize::new(NOT_IN_USE);
    /// let data = UnsafeCell::new(0i32);
    ///
    /// if NOT_IN_USE == guard.acquire().swap(WRITING) {
    ///     // No others are reading or writing to the data protected by guard (`NOT_IN_USE`).
    ///     // We have acquired the latest state of the data.
    ///     unsafe {
    ///         let val = data.get();
    ///         *val = *val+ 1; // My complex use of the data
    ///     }
    ///
    ///     // Done, release our changes
    ///     guard.release().store(NOT_IN_USE);
    /// }
    ///
    /// // Cleanup when there are no other threads using `data` anymore:
    /// if NOT_IN_USE == guard.acquire().load() {
    ///     unsafe {
    ///         let val = data.get();
    ///         *val = 0;
    ///     }
    /// }
    /// ```
    ///
    /// [`release`]: AtomicUsize::release
    /// [`load`]: AtomicUsize::load
    /// [`swap`]: AtomicUsize::swap
    /// [`fetch_*`]: AtomicUsize::fetch_add
    /// [`compare`]: NeedsLoad::compare
    #[must_use]
    #[inline]
    pub fn acquire(&self) -> NeedsLoad {
        NeedsLoad { atomic: self }
    }

    /// Release data that is written by this thread to another thread. This is the first part of
    /// what needs to be a release/acquire pair on this atomic, where the receiving thread must use
    /// [`acquire`].
    ///
    /// Intended to be used with one of the operations that do a store (📥) in ‘method chaining’:
    /// [`store`], [`swap`], or one of the [`fetch_*`] methods.
    ///
    /// In rare cases can be chained with a [`NeedsStore::acquire`] when you not only need to
    /// release data yourself, but also need to acquire data written by other threads (typically
    /// when the atomic is used to synchronize more than one location of regular data).
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let atomic = AtomicUsize::new(42);
    /// atomic.release().store(15);
    /// ```
    ///
    /// [`acquire`]: AtomicUsize::acquire
    /// [`store`]: AtomicUsize::store
    /// [`swap`]: AtomicUsize::swap
    /// [`fetch_*`]: AtomicUsize::fetch_add
    #[must_use]
    #[inline]
    pub fn release(&self) -> NeedsStore {
        NeedsStore { atomic: self }
    }

    /// 📤 (📥?) Compare the atomic integer to a value, and take some action if successful.
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
    /// - Next you can supply release/acquire orderings, if you want to enforce any: [`release`]
    ///   and/or [`acquire`].
    ///
    /// - Finish with [`swap`], which stores a value into the atomic integer, returning the previous
    ///   value.
    ///
    /// ```text
    /// atomic.compare(current).swap(new);
    /// atomic.compare(current).acquire().swap(new);
    /// atomic.compare(current).release().swap(new);
    /// atomic.compare(current).release().acquire().swap(new);
    ///
    /// atomic.compare(current).weak().swap(new);
    /// atomic.compare(current).weak().acquire().swap(new);
    /// atomic.compare(current).weak().release().swap(new);
    /// atomic.compare(current).weak().release().acquire().swap(new);
    /// ```
    ///
    /// # Examples
    /// Reimplementing `fetch_add` using a weak `compare`:
    /// ```text
    /// use atomics_api::AtomicUsize;
    ///
    /// fn my_fetch_add(atomic: AtomicUsize, other: usize) {
    ///     let mut old = atomic.load();
    ///     loop {
    ///         let new = old + 1;
    ///         atomic.compare(old).weak().swap(new) {
    ///             Ok(_) => break,
    ///             Err(x) => old = x,
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// FIXME
    /// No weak: lock-free singleton construction: https://devblogs.microsoft.com/oldnewthing/20180330-00/?p=98395
    /// with weak: CAS-loop
    /// with acquire: ??
    /// with release: ??
    /// ```text
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
    /// [`compare`]: AtomicUsize::compare
    /// [`swap`]: NeedsCompareOp::swap
    /// [`store`]: NeedsCompareOp::store
    /// [`weak`]: NeedsCompareOp::weak
    /// [`acquire`]: NeedsCompareOp::acquire
    /// [`release`]: NeedsCompareOp::release
    #[must_use]
    #[inline]
    pub fn compare(&self, current: usize) -> NeedsCompareOp {
        NeedsCompareOp {
            atomic: self,
            current,
            ordering_success: Ordering::Relaxed,
            ordering_failure: Ordering::Relaxed,
            weak: false,
        }
    }

    /// Retricted method to acquire data that is written by another thread.
    ///
    /// While `acquire` can always be used to acquire data released by another thread, `consume` can
    /// only do so if there is a data dependency on the value of the atomic.
    ///
    /// In other words: without reading the atomic it must be impossible for this thread to know
    /// where the data lives that has to be synchronized. Typically the atomic will hold the value
    /// of a pointer, or something like an array index.
    ///
    /// Don't try to somehow make fake dependencies, that the optimizer or processor may eliminate.
    #[must_use]
    #[inline]
    pub fn consume(&self) -> NeedsLoad {
        unimplemented!()
    }

    /// Make sure this operation will not be reordered, but remains after all previous loads and
    /// stores to other atomics (and to regular data).
    ///
    /// This does exactly the same thing as [`release`]. It can be used to make the code
    /// self-document the guarantees it relies on.
    ///
    /// [`release`]: AtomicUsize::release
    #[must_use]
    #[inline]
    pub fn stay_after(&self) -> NeedsStore {
        NeedsStore { atomic: self }
    }

    /// Make sure this operation will not be reordered, but remains before all following loads and
    /// stores to other atomics (and to regular data).
    ///
    /// This does exactly the same thing as [`acquire`]. It can be used to make the code
    /// self-document the guarantees it relies on.
    ///
    /// [`acquire`]: AtomicUsize::acquire
    #[must_use]
    #[inline]
    pub fn stay_before(&self) -> NeedsLoad {
        NeedsLoad { atomic: self }
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
    /// ```
    /// // Drop implementation similar to that of `std::sync::Arc`
    /// pub struct MyArc<T: ?Sized> {
    ///     ptr: NonNull<ArcInner<T>>,
    ///     phantom: PhantomData<T>,
    /// }
    ///
    /// struct ArcInner<T: ?Sized> {
    ///     ref_count: atomic::AtomicUsize,
    ///     data: T,
    /// }
    ///
    /// unsafe impl<#[may_dangle] T: ?Sized> Drop for MyArc<T> {
    ///     fn drop(&mut self) {
    ///         let inner = self.ptr.as_ref();
    ///         if inner.ref_count.fetch_sub(1) != 1 {
    ///             return;
    ///         }
    ///         // We held the last reference, acquire the contents of this Arc and drop them.
    ///         inner.data.drop()
    ///     }
    /// }
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
}

pub struct NeedsLoad<'a> {
    atomic: &'a AtomicUsize
}

impl NeedsLoad<'_> {
    /// FIXME: add doc comment
    #[inline]
    pub fn compare(&self, current: usize) -> NeedsCompareOp {
        NeedsCompareOp {
            atomic: self.atomic,
            current,
            ordering_success: Ordering::Acquire,
            ordering_failure: Ordering::Acquire,
            weak: false,
        }
    }

    #[inline]
    pub fn load(self) -> usize { self.atomic.0.load(Ordering::Acquire) }
    #[inline]
    pub fn swap(self, val: usize) -> usize { self.atomic.0.swap(val, Ordering::Acquire) }
    #[inline]
    pub fn fetch_add(&self, val: usize) -> usize { self.atomic.0.fetch_add(val, Ordering::Acquire) }
    #[inline]
    pub fn fetch_sub(&self, val: usize) -> usize { self.atomic.0.fetch_sub(val, Ordering::Acquire) }
    #[inline]
    pub fn fetch_and(&self, val: usize) -> usize { self.atomic.0.fetch_and(val, Ordering::Acquire) }
    #[inline]
    pub fn fetch_nand(&self, val: usize) -> usize { self.atomic.0.fetch_nand(val, Ordering::Acquire) }
    #[inline]
    pub fn fetch_or(&self, val: usize) -> usize { self.atomic.0.fetch_or(val, Ordering::Acquire) }
    #[inline]
    pub fn fetch_xor(&self, val: usize) -> usize { self.atomic.0.fetch_xor(val, Ordering::Acquire) }
}

pub struct NeedsStore<'a> {
    atomic: &'a AtomicUsize
}

impl NeedsStore<'_> {
    /// Not only Release data that is written by this thread to another thread, but at the same time
    /// Acquire data that is written by another thread.
    ///
    /// This method is generally used only in rare cases, where an atomic is not used to synchronize
    /// just one location of regular data, but multiple independend locations.
    ///
    /// Intended to be used with one of the operations that do both a load and a store (📤 📥) in
    /// ‘method chaining’: [`swap`] or one of the [`fetch_*`] methods.
    ///
    /// # Examples
    /// ```
    /// use atomics_api::AtomicUsize;
    ///
    /// let atomic = AtomicUsize::new(42);
    /// let value = atomic.release().acquire().swap(41);
    /// ```
    ///
    /// [`swap`]: AtomicUsize::swap
    /// [`fetch_*`]: AtomicUsize::fetch_add
    #[must_use]
    #[inline]
    pub fn acquire(&self) -> NeedsRmw {
        NeedsRmw { atomic: self.atomic }
    }

    #[inline]
    pub fn store(self, val: usize) { self.atomic.0.store(val, Ordering::Release) }
    #[inline]
    pub fn swap(self, val: usize) -> usize { self.atomic.0.swap(val, Ordering::Release) }
    #[inline]
    pub fn fetch_add(&self, val: usize) -> usize { self.atomic.0.fetch_add(val, Ordering::Release) }
    #[inline]
    pub fn fetch_sub(&self, val: usize) -> usize { self.atomic.0.fetch_sub(val, Ordering::Release) }
    #[inline]
    pub fn fetch_and(&self, val: usize) -> usize { self.atomic.0.fetch_and(val, Ordering::Release) }
    #[inline]
    pub fn fetch_nand(&self, val: usize) -> usize { self.atomic.0.fetch_nand(val, Ordering::Release) }
    #[inline]
    pub fn fetch_or(&self, val: usize) -> usize { self.atomic.0.fetch_or(val, Ordering::Release) }
    #[inline]
    pub fn fetch_xor(&self, val: usize) -> usize { self.atomic.0.fetch_xor(val, Ordering::Release) }
}

pub struct NeedsRmw<'a> {
    atomic: &'a AtomicUsize,
}

impl NeedsRmw<'_> {
    #[inline]
    pub fn swap(self, val: usize) -> usize { self.atomic.0.swap(val, Ordering::AcqRel) }
    #[inline]
    pub fn fetch_add(&self, val: usize) -> usize { self.atomic.0.fetch_add(val, Ordering::AcqRel) }
    #[inline]
    pub fn fetch_sub(&self, val: usize) -> usize { self.atomic.0.fetch_sub(val, Ordering::AcqRel) }
    #[inline]
    pub fn fetch_and(&self, val: usize) -> usize { self.atomic.0.fetch_and(val, Ordering::AcqRel) }
    #[inline]
    pub fn fetch_nand(&self, val: usize) -> usize { self.atomic.0.fetch_nand(val, Ordering::AcqRel) }
    #[inline]
    pub fn fetch_or(&self, val: usize) -> usize { self.atomic.0.fetch_or(val, Ordering::AcqRel) }
    #[inline]
    pub fn fetch_xor(&self, val: usize) -> usize { self.atomic.0.fetch_xor(val, Ordering::AcqRel) }

    /// Synchronizations that need a read-modify-write operation don't work with just a store.
    /// This method emulates a store by using [`swap`] and ignoring the result.
    ///
    /// [`swap`]: NeedsRmw::swap
    #[inline]
    pub fn store(self, val: usize) {
        let _ = self.atomic.0.swap(val, Ordering::AcqRel);
    }
}

pub struct NeedsCompareOp<'a> {
    atomic: &'a AtomicUsize,
    current: usize,
    ordering_success: Ordering,
    ordering_failure: Ordering,
    weak: bool,
}

impl<'a> NeedsCompareOp<'a> {
    /// Stores a value into the atomic integer if the current value is the same as the `current`
    /// value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    #[inline]
    pub fn swap(&self, value: usize) -> Result<usize, usize> {
        match self.weak {
            false => self.atomic.0.compare_exchange(self.current,
                                                    value,
                                                    self.ordering_success,
                                                    self.ordering_failure),
            true => self.atomic.0.compare_exchange_weak(self.current,
                                                        value,
                                                        self.ordering_success,
                                                        self.ordering_failure),
        }
    }

    #[inline]
    pub fn store(&self, value: usize) -> bool {
        self.swap(value).is_ok()
    }

    /// Allow the compare-and-exchange to spuriously fail even when the comparison succeeds. This
    /// will yield better performance on some platforms.
    ///
    /// When to prefer `weak`? If you would have to introduce a loop only because of spurious
    /// failure, don't use it. But if you have a loop anyway, `weak` is the better choice.
    #[must_use]
    #[inline]
    pub fn weak(mut self) -> Self {
        self.weak = true;
        self
    }

    #[must_use]
    #[inline]
    pub fn acquire(mut self) -> Self {
        if self.ordering_success == Ordering::Release {
            self.ordering_success = Ordering::AcqRel;
        } else {
            self.ordering_success = Ordering::Acquire;
        }
        self
    }

    #[must_use]
    #[inline]
    pub fn release(mut self) -> Self {
        if self.ordering_success == Ordering::Acquire {
            self.ordering_success = Ordering::AcqRel;
        } else {
            self.ordering_success = Ordering::Release;
        }
        self
    }
}

/// Do an acquire operations without doing a load on an atomic.
///
/// Note: this uses the atomic that this thread last performed a load on the know with which other
/// threads to synchronize data.
///
/// Prevents all following memory operations from being reordered before the *last read*.
pub fn acquire_using_last_load() {
    fence(Ordering::Acquire)
}

/// Do a release operations without doing a store on an atomic.
///
/// Note: this uses the atomic on which this thread is going to perform a load next to the know with
/// which other threads to synchronize data.
///
/// Prevents all preceding memory operations from being reordered past *subsequent writes*.
pub fn release_using_next_store() {
    fence(Ordering::Release)
}


#[cfg(test)]
mod tests {
    use super::AtomicUsize;

    #[test]
    fn it_works() {
        let atomic = AtomicUsize::new(42);
        atomic.release().store(15);

        atomic.compare(15);
    }
}
