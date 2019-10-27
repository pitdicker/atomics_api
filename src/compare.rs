use core::sync::atomic::Ordering;

use crate::AtomicUsize;

pub(crate) struct CompareExchange<'a> {
    atomic: &'a AtomicUsize,
    current: usize,
    ordering_success: Ordering,
    ordering_failure: Ordering,
    weak: bool,
}

impl<'a> CompareExchange<'a> {
    #[inline]
    pub(crate) fn new(
        atomic: &'a AtomicUsize,
        current: usize,
        ordering_success: Ordering,
        ordering_failure: Ordering,
        weak: bool) -> CompareExchange<'a>
    {
        CompareExchange {
            atomic,
            current,
            ordering_success,
            ordering_failure,
            weak
        }
    }

    #[inline]
    fn swap(&self, value: usize) -> Result<usize, usize> {
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
}

pub struct NeedsCompareOrdering<'a>(pub(crate) CompareExchange<'a>);

impl<'a> NeedsCompareOrdering<'a> {
    #[must_use]
    #[inline]
    pub fn acquire(mut self) -> NeedsCompareFinalizer<'a> {
        self.0.ordering_success = Ordering::Acquire;
        NeedsCompareFinalizer(self.0)
    }

    #[must_use]
    #[inline]
    pub fn release(mut self) -> NeedsCompareFinalizer<'a> {
        self.0.ordering_success = Ordering::Release;
        NeedsCompareFinalizer(self.0)
    }

    #[must_use]
    #[inline]
    pub fn acquire_and_release(mut self) -> NeedsCompareFinalizer<'a> {
        self.0.ordering_success = Ordering::AcqRel;
        NeedsCompareFinalizer(self.0)
    }

    /// Allow the compare-and-exchange to spuriously fail even when the comparison succeeds. This
    /// will yield better performance on some platforms.
    ///
    /// When to prefer `weak`? If you would have to introduce a loop only because of spurious
    /// failure, don't use it. But if you have a loop anyway, `weak` is the better choice.
    #[inline]
    pub fn weak(mut self) -> Self {
        self.0.weak = true;
        self
    }

    /// Stores a value into the atomic integer if the current value is the same as the `current`
    /// value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    #[inline]
    pub fn swap(&self, value: usize) -> Result<usize, usize> {
        self.0.swap(value)
    }

    #[inline]
    pub fn store(&self, value: usize) -> bool {
        self.0.swap(value).is_ok()
    }
}

pub struct NeedsCompareFinalizer<'a>(CompareExchange<'a>);

impl NeedsCompareFinalizer<'_> {
    /// Stores a value into the atomic integer if the current value is the same as the `current`
    /// value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    #[inline]
    pub fn swap(&self, value: usize) -> Result<usize, usize> {
        self.0.swap(value)
    }

    #[inline]
    pub fn store(&self, value: usize) -> bool {
        self.0.swap(value).is_ok()
    }
}

pub struct NeedsCompareAcqOp<'a>(pub(crate) CompareExchange<'a>);

impl<'a> NeedsCompareAcqOp<'a> {
    /// Allow the compare-and-exchange to spuriously fail even when the comparison succeeds. This
    /// will yield better performance on some platforms.
    ///
    /// When to prefer `weak`? If you would have to introduce a loop only because of spurious
    /// failure, don't use it. But if you have a loop anyway, `weak` is the better choice.
    #[inline]
    pub fn weak(mut self) -> Self {
        self.0.weak = true;
        self
    }

    /// Stores a value into the atomic integer if the current value is the same as the `current`
    /// value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    #[inline]
    pub fn swap(&self, value: usize) -> Result<usize, usize> {
        self.0.swap(value)
    }

    #[inline]
    pub fn store(&self, value: usize) -> bool {
        self.0.swap(value).is_ok()
    }

    #[must_use]
    #[inline]
    pub fn release(mut self) -> NeedsCompareFinalizer<'a> {
        if self.0.ordering_success != Ordering::SeqCst {
            self.0.ordering_success = Ordering::AcqRel;
        }
        NeedsCompareFinalizer(self.0)
    }
}
