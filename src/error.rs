#[cfg(feature = "alloc")]
use alloc::{boxed::Box, string::String};
use core::{any::TypeId, fmt};

enum Repr {
    Simple(ErrorKind),
    // &str is a fat pointer, but &&str is a thin pointer.
    SimpleMessage(ErrorKind, &'static &'static str),
    #[cfg(feature = "alloc")]
    Custom(Box<Custom>),
}

impl fmt::Debug for Repr {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            #[cfg(feature = "alloc")]
            Repr::Custom(ref c) => fmt::Debug::fmt(&c, fmt),
            Repr::Simple(kind) => fmt.debug_tuple("Kind").field(&kind).finish(),
            Repr::SimpleMessage(kind, &message) => fmt
                .debug_struct("Error")
                .field("kind", &kind)
                .field("message", &message)
                .finish(),
        }
    }
}

#[cfg(feature = "alloc")]
#[derive(Debug)]
struct Custom {
    kind: ErrorKind,
    error: Box<dyn ErrorTrait + Send + Sync>,
}

/// A trait providing a subset of [`std::error::Error`]'s functionality.
pub trait ErrorTrait: fmt::Debug + fmt::Display {
    /// The lower-level source of this error, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::fmt;
    /// use acid_io::ErrorTrait;
    ///
    /// #[derive(Debug)]
    /// struct SuperError {
    ///     side: SuperErrorSideKick,
    /// }
    ///
    /// impl fmt::Display for SuperError {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "SuperError is here!")
    ///     }
    /// }
    ///
    /// impl ErrorTrait for SuperError {
    ///     fn source(&self) -> Option<&(dyn ErrorTrait + 'static)> {
    ///         Some(&self.side)
    ///     }
    /// }
    ///
    /// #[derive(Debug)]
    /// struct SuperErrorSideKick;
    ///
    /// impl fmt::Display for SuperErrorSideKick {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "SuperErrorSideKick is here!")
    ///     }
    /// }
    ///
    /// impl ErrorTrait for SuperErrorSideKick {}
    ///
    /// fn get_super_error() -> Result<(), SuperError> {
    ///     Err(SuperError { side: SuperErrorSideKick })
    /// }
    ///
    /// fn main() {
    ///     match get_super_error() {
    ///         Err(e) => {
    ///             println!("Error: {}", e);
    ///             println!("Caused by: {}", e.source().unwrap());
    ///         }
    ///         _ => println!("No error"),
    ///     }
    /// }
    /// ```
    fn source(&self) -> Option<&(dyn ErrorTrait + 'static)> {
        None
    }

    /// Gets the `TypeId` of `self`.
    // NOTE: this is memory-unsafe to override in user code
    #[doc(hidden)]
    fn type_id(&self, _: private::Internal) -> TypeId
    where
        Self: 'static,
    {
        TypeId::of::<Self>()
    }
}

mod private {
    pub struct Internal;
}

impl dyn ErrorTrait + 'static {
    /// Returns `true` if the boxed type is the same as `T`
    #[inline]
    pub fn is<T: ErrorTrait + 'static>(&self) -> bool {
        // Get `TypeId` of the type this function is instantiated with.
        let t = TypeId::of::<T>();

        // Get `TypeId` of the type in the trait object.
        let boxed = self.type_id(private::Internal);

        // Compare both `TypeId`s on equality.
        t == boxed
    }

    /// Returns some reference to the boxed value if it is of type `T`, or
    /// `None` if it isn't.
    #[inline]
    pub fn downcast_ref<T: ErrorTrait + 'static>(&self) -> Option<&T> {
        if self.is::<T>() {
            unsafe { Some(&*(self as *const dyn ErrorTrait as *const T)) }
        } else {
            None
        }
    }

    /// Returns some mutable reference to the boxed value if it is of type `T`, or
    /// `None` if it isn't.
    #[inline]
    pub fn downcast_mut<T: ErrorTrait + 'static>(&mut self) -> Option<&mut T> {
        if self.is::<T>() {
            unsafe { Some(&mut *(self as *mut dyn ErrorTrait as *mut T)) }
        } else {
            None
        }
    }
}

impl dyn ErrorTrait + 'static + Send {
    /// Forwards to the method defined on the type `dyn ErrorTrait`.
    #[inline]
    pub fn is<T: ErrorTrait + 'static>(&self) -> bool {
        <dyn ErrorTrait + 'static>::is::<T>(self)
    }

    /// Forwards to the method defined on the type `dyn ErrorTrait`.
    #[inline]
    pub fn downcast_ref<T: ErrorTrait + 'static>(&self) -> Option<&T> {
        <dyn ErrorTrait + 'static>::downcast_ref::<T>(self)
    }

    /// Forwards to the method defined on the type `dyn ErrorTrait`.
    #[inline]
    pub fn downcast_mut<T: ErrorTrait + 'static>(&mut self) -> Option<&mut T> {
        <dyn ErrorTrait + 'static>::downcast_mut::<T>(self)
    }
}

impl dyn ErrorTrait + 'static + Send + Sync {
    /// Forwards to the method defined on the type `dyn ErrorTrait`.
    #[inline]
    pub fn is<T: ErrorTrait + 'static>(&self) -> bool {
        <dyn ErrorTrait + 'static>::is::<T>(self)
    }

    /// Forwards to the method defined on the type `dyn ErrorTrait`.
    #[inline]
    pub fn downcast_ref<T: ErrorTrait + 'static>(&self) -> Option<&T> {
        <dyn ErrorTrait + 'static>::downcast_ref::<T>(self)
    }

    /// Forwards to the method defined on the type `dyn ErrorTrait`.
    #[inline]
    pub fn downcast_mut<T: ErrorTrait + 'static>(&mut self) -> Option<&mut T> {
        <dyn ErrorTrait + 'static>::downcast_mut::<T>(self)
    }
}

#[cfg(feature = "alloc")]
impl From<String> for Box<dyn ErrorTrait + Send + Sync> {
    /// Converts a [`String`] into a box of dyn [`Error`] + [`Send`] + [`Sync`].
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::ErrorTrait;
    /// use core::mem;
    ///
    /// let a_string_error = "a string error".to_string();
    /// let a_boxed_error = Box::<dyn ErrorTrait + Send + Sync>::from(a_string_error);
    /// assert!(
    ///     mem::size_of::<Box<dyn ErrorTrait + Send + Sync>>() == mem::size_of_val(&a_boxed_error))
    /// ```
    #[inline]
    fn from(err: String) -> Box<dyn ErrorTrait + Send + Sync> {
        struct StringError(String);

        impl ErrorTrait for StringError {}

        impl fmt::Display for StringError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }

        // Purposefully skip printing "StringError(..)"
        impl fmt::Debug for StringError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(&self.0, f)
            }
        }

        Box::new(StringError(err))
    }
}

#[cfg(feature = "alloc")]
impl From<&'_ str> for Box<dyn ErrorTrait + Send + Sync> {
    fn from(msg: &'_ str) -> Self {
        From::from(String::from(msg))
    }
}

#[cfg(feature = "alloc")]
impl<'a, E: ErrorTrait + Send + Sync + 'a> From<E> for Box<dyn ErrorTrait + Send + Sync + 'a> {
    /// Converts a type of [`ErrorTrait`] + [`Send`] + [`Sync`] into a box of
    /// dyn [`ErrorTrait`] + [`Send`] + [`Sync`].
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::ErrorTrait;
    /// use core::{fmt, mem};
    ///
    /// #[derive(Debug)]
    /// struct AnErrorTrait;
    ///
    /// impl fmt::Display for AnErrorTrait {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "An error")
    ///     }
    /// }
    ///
    /// impl ErrorTrait for AnErrorTrait {}
    ///
    /// unsafe impl Send for AnErrorTrait {}
    ///
    /// unsafe impl Sync for AnErrorTrait {}
    ///
    /// let an_error = AnErrorTrait;
    /// assert!(0 == mem::size_of_val(&an_error));
    /// let a_boxed_error = Box::<dyn ErrorTrait + Send + Sync>::from(an_error);
    /// assert!(
    ///     mem::size_of::<Box<dyn ErrorTrait + Send + Sync>>() == mem::size_of_val(&a_boxed_error))
    /// ```
    fn from(err: E) -> Box<dyn ErrorTrait + Send + Sync + 'a> {
        Box::new(err)
    }
}

/// The error type for I/O operations of the [`Read`], [`Write`], [`Seek`], and
/// associated traits.
///
/// [`Read`]: crate::Read
/// [`Write`]: crate::Write
/// [`Seek`]: crate::Seek
pub struct Error {
    repr: Repr,
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.repr, f)
    }
}

impl Error {
    /// Creates a new I/O error from a known kind of error as well as an
    /// arbitrary error payload.
    ///
    /// This function is used to generically create I/O errors which do not
    /// originate from the OS itself. The `error` argument is an arbitrary
    /// payload which will be contained in this [`Error`].
    ///
    /// If no extra payload is required, use the `From` conversion from
    /// `ErrorKind`.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{Error, ErrorKind};
    ///
    /// // errors can be created from strings
    /// let custom_error = Error::new(ErrorKind::Other, "oh no!");
    ///
    /// // errors can also be created from other errors
    /// let custom_error2 = Error::new(ErrorKind::Interrupted, custom_error);
    ///
    /// // creating an error without payload
    /// let eof_error = Error::from(ErrorKind::UnexpectedEof);
    /// ```
    #[cfg(feature = "alloc")]
    pub fn new<E>(kind: ErrorKind, error: E) -> Error
    where
        E: Into<Box<dyn ErrorTrait + Send + Sync>>,
    {
        Error {
            repr: Repr::Custom(Box::new(Custom {
                kind,
                error: error.into(),
            })),
        }
    }

    /// Creates a new I/O error from a known kind of error as well as a
    /// constant message.
    ///
    /// This function does not allocate.
    ///
    /// This function should maybe change to
    /// `new_const<const MSG: &'static str>(kind: ErrorKind)`
    /// in the future, when const generics allow that.
    #[inline]
    pub(crate) const fn new_const(kind: ErrorKind, message: &'static &'static str) -> Error {
        Self {
            repr: Repr::SimpleMessage(kind, message),
        }
    }

    /// Returns a reference to the inner error wrapped by this error (if any).
    ///
    /// If this [`Error`] was constructed via [`new`] then this function will
    /// return [`Some`], otherwise it will return [`None`].
    ///
    /// [`new`]: Error::new
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{Error, ErrorKind};
    ///
    /// fn print_error(err: &Error) {
    ///     if let Some(inner_err) = err.get_ref() {
    ///         println!("Inner error: {:?}", inner_err);
    ///     } else {
    ///         println!("No inner error");
    ///     }
    /// }
    ///
    /// fn main() {
    ///     // Will print "Inner error: ...".
    ///     print_error(&Error::new(ErrorKind::Other, "oh no!"));
    /// }
    /// ```
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn get_ref(&self) -> Option<&(dyn ErrorTrait + Send + Sync + 'static)> {
        match self.repr {
            Repr::Simple(..) => None,
            Repr::SimpleMessage(..) => None,
            Repr::Custom(ref c) => Some(&*c.error),
        }
    }

    /// Returns a mutable reference to the inner error wrapped by this error
    /// (if any).
    ///
    /// If this [`Error`] was constructed via [`new`] then this function will
    /// return [`Some`], otherwise it will return [`None`].
    ///
    /// [`new`]: Error::new
    ///
    /// # Examples
    ///
    /// ```
    /// use core::fmt::{self, Display};
    /// use acid_io::{Error, ErrorKind};
    ///
    /// #[derive(Debug)]
    /// struct MyError {
    ///     v: String,
    /// }
    ///
    /// impl MyError {
    ///     fn new() -> MyError {
    ///         MyError {
    ///             v: "oh no!".to_string()
    ///         }
    ///     }
    ///
    ///     fn change_message(&mut self, new_message: &str) {
    ///         self.v = new_message.to_string();
    ///     }
    /// }
    ///
    /// impl acid_io::ErrorTrait for MyError {}
    ///
    /// impl Display for MyError {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "MyError: {}", &self.v)
    ///     }
    /// }
    ///
    /// fn change_error(mut err: Error) -> Error {
    ///     if let Some(inner_err) = err.get_mut() {
    ///         inner_err.downcast_mut::<MyError>().unwrap().change_message("I've been changed!");
    ///     }
    ///     err
    /// }
    ///
    /// fn print_error(err: &Error) {
    ///     if let Some(inner_err) = err.get_ref() {
    ///         println!("Inner error: {}", inner_err);
    ///     } else {
    ///         println!("No inner error");
    ///     }
    /// }
    ///
    /// fn main() {
    ///     // Will print "Inner error: ...".
    ///     print_error(&change_error(Error::new(ErrorKind::Other, MyError::new())));
    /// }
    /// ```
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn get_mut(&mut self) -> Option<&mut (dyn ErrorTrait + Send + Sync + 'static)> {
        match self.repr {
            Repr::Simple(..) => None,
            Repr::SimpleMessage(..) => None,
            Repr::Custom(ref mut c) => Some(&mut *c.error),
        }
    }

    /// Consumes the `Error`, returning its inner error (if any).
    ///
    /// If this [`Error`] was constructed via [`new`] then this function will
    /// return [`Some`], otherwise it will return [`None`].
    ///
    /// [`new`]: Error::new
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{Error, ErrorKind};
    ///
    /// fn print_error(err: Error) {
    ///     if let Some(inner_err) = err.into_inner() {
    ///         println!("Inner error: {}", inner_err);
    ///     } else {
    ///         println!("No inner error");
    ///     }
    /// }
    ///
    /// fn main() {
    ///     // Will print "Inner error: ...".
    ///     print_error(Error::new(ErrorKind::Other, "oh no!"));
    /// }
    /// ```
    #[cfg(feature = "alloc")]
    #[must_use = "`self` will be dropped if the result is not used"]
    #[inline]
    pub fn into_inner(self) -> Option<Box<dyn ErrorTrait + Send + Sync>> {
        match self.repr {
            Repr::Simple(..) => None,
            Repr::SimpleMessage(..) => None,
            Repr::Custom(c) => Some(c.error),
        }
    }

    /// Returns the corresponding [`ErrorKind`] for this error.
    #[inline]
    pub fn kind(&self) -> ErrorKind {
        match self.repr {
            #[cfg(feature = "alloc")]
            Repr::Custom(ref c) => c.kind,
            Repr::Simple(kind) => kind,
            Repr::SimpleMessage(kind, _) => kind,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.repr {
            #[cfg(feature = "alloc")]
            Repr::Custom(ref c) => c.error.fmt(fmt),
            Repr::Simple(kind) => write!(fmt, "{}", kind.as_str()),
            Repr::SimpleMessage(_, &msg) => msg.fmt(fmt),
        }
    }
}

impl ErrorTrait for Error {
    fn source(&self) -> Option<&(dyn ErrorTrait + 'static)> {
        match self.repr {
            Repr::Simple(..) => None,
            Repr::SimpleMessage(..) => None,
            #[cfg(feature = "alloc")]
            Repr::Custom(ref c) => c.error.source(),
        }
    }
}

/// A list specifying general categories of I/O error.
///
/// This list is intended to grow over time and it is not recommended to
/// exhaustively match against it.
///
/// It is used with the [`acid_io::Error`][Error] type.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum ErrorKind {
    /// This operation was interrupted.
    ///
    /// Interrupted operations can typically be retried.
    Interrupted,
    /// Data not valid for the operation were encountered.
    ///
    /// Unlike [`InvalidInput`], this typically means that the operation
    /// parameters were valid, however the error was caused by malformed
    /// input data.
    ///
    /// For example, a function that reads a file into a string will error with
    /// `InvalidData` if the file's contents are not valid UTF-8.
    ///
    /// [`InvalidInput`]: ErrorKind::InvalidInput
    InvalidData,
    /// A parameter was incorrect.
    InvalidInput,
    /// An error returned when an operation could not be completed because an
    /// “end of file” was reached prematurely.
    ///
    /// This typically means that an operation could only succeed if it read a
    /// particular number of bytes but only a smaller number of bytes could be
    /// read.
    UnexpectedEof,
    /// An error returned when an operation could not be completed because a
    /// call to [`write`] returned [`Ok(0)`].
    ///
    /// This typically means that an operation could only succeed if it wrote a
    /// particular number of bytes but only a smaller number of bytes could be
    /// written.
    ///
    /// [`write`]: crate::Write::write
    /// [`Ok(0)`]: Ok
    WriteZero,
    /// A custom error that does not fall under any other I/O error kind.
    ///
    /// This can be used to construct your own [`Error`]s that do not match any
    /// [`ErrorKind`].
    ///
    /// This [`ErrorKind`] is not used by `acid_io`.
    ///
    /// Errors from the standard library that do not fall under any of the I/O
    /// error kinds cannot be `match`ed on, and will only match a wildcard (`_`)
    /// pattern.  New [`ErrorKind`]s might be added in the future for some of
    /// those.
    Other,
    /// Any I/O error from `acid_io` that's not part of this list.
    ///
    /// Errors that are `Uncategorized` now may move to a different or a new
    /// [`ErrorKind`] variant in the future. It is not recommended to match
    /// an error against `Uncategorized`; use a wildcard match (`_`) instead.
    #[doc(hidden)]
    Uncategorized,
}

impl ErrorKind {
    pub(crate) fn as_str(&self) -> &'static str {
        use ErrorKind::*;
        // Strictly alphabetical, please.  (Sadly rustfmt cannot do this yet.)
        match *self {
            Interrupted => "operation interrupted",
            InvalidData => "invalid data",
            InvalidInput => "invalid input parameter",
            Other => "other error",
            Uncategorized => "uncategorized error",
            UnexpectedEof => "unexpected end of file",
            WriteZero => "write zero",
        }
    }
}

/// Intended for use for errors not exposed to the user, where allocating onto
/// the heap (for normal construction via Error::new) is too costly.
impl From<ErrorKind> for Error {
    /// Converts an [`ErrorKind`] into an [`Error`].
    ///
    /// This conversion allocates a new error with a simple representation of error kind.
    ///
    /// # Examples
    ///
    /// ```
    /// use acid_io::{Error, ErrorKind};
    ///
    /// let invalid_data = ErrorKind::InvalidData;
    /// let error = Error::from(invalid_data);
    /// assert_eq!("invalid data", format!("{}", error));
    /// ```
    #[inline]
    fn from(kind: ErrorKind) -> Error {
        Error {
            repr: Repr::Simple(kind),
        }
    }
}

/// A specialized [`Result`] type for I/O operations.
///
/// This type is broadly used across `acid_io` for any operation which may
/// produce an error.
///
/// This typedef is generally used to avoid writing out
/// [`acid_io::Error`][Error] directly and is otherwise a direct mapping to
/// [`Result`].
///
/// While usual Rust style is to import types directly, aliases of [`Result`]
/// often are not, to make it easier to distinguish between them. [`Result`] is
/// generally assumed to be [`core::result::Result`], and so users of this alias
/// will generally use `acid_io::Result` instead of shadowing the [prelude]'s
/// import of [`core::result::Result`].
///
/// [`io::Error`]: Error
/// [prelude]: core::prelude
pub type Result<T> = core::result::Result<T, Error>;
