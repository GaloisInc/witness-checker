use std::ops::Deref;

/// Either `&'a T` or `Box<T>`.  This is similar to `std::borrow::Cow`, but the owned case is
/// always boxed.  This makes it usable when `T` is dynamically sized.
#[derive(Clone, Debug)]
pub enum CowBox<'a, T: ?Sized> {
    Borrowed(&'a T),
    Owned(Box<T>),
}

impl<'a, T: ?Sized + Clone> CowBox<'a, T> {
    pub fn into_owned(self) -> T {
        match self {
            CowBox::Borrowed(r) => r.clone(),
            CowBox::Owned(b) => *b,
        }
    }

    pub fn into_box(self) -> Box<T> {
        match self {
            CowBox::Borrowed(r) => Box::new(r.clone()),
            CowBox::Owned(b) => b,
        }
    }
}

impl<'a, T: ?Sized> From<&'a T> for CowBox<'a, T> {
    fn from(x: &'a T) -> CowBox<'a, T> {
        CowBox::Borrowed(x)
    }
}

impl<'a, T: ?Sized> From<Box<T>> for CowBox<'a, T> {
    fn from(x: Box<T>) -> CowBox<'a, T> {
        CowBox::Owned(x)
    }
}

impl<T: ?Sized> Deref for CowBox<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        match *self {
            CowBox::Borrowed(r) => r,
            CowBox::Owned(ref b) => b,
        }
    }
}
