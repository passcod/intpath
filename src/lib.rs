//! Interned paths and path segments.

#![forbid(missing_docs)]
#![forbid(unsafe_code)]
#![deny(bare_trait_objects)]
#![deny(clippy::pedantic)]

use chashmap::CHashMap;
use std::ffi::{OsStr, OsString};
use std::path::{Component, Path, PathBuf};
use std::sync::{Arc, Weak};

/// An interned path.
///
/// This is a vector of remote [`OsString`]s via [`IntSeg`].
///
/// [`OsString`]: https://doc.rust-lang.org/std/ffi/struct.OsString.html
/// [`IntSeg`]: ./struct.IntSeg.html
#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct IntPath {
    /// Prefix of the path.
    ///
    /// For Windows paths, this may be e.g. `C:`.
    ///
    /// Unlike the stdlib, `IntPath` supports prefixes at all times, such as for URL-style prefixed
    /// paths, e.g. `file:///home/foo.txt`.
    pub prefix: Option<IntSeg>,

    /// Separator of the path.
    ///
    /// Internally, the path is stored in _segments_, and this separator is used when
    /// reconstructing the path to a string. Often defaults to the platform default, but `IntPath`
    /// can handle any kind. Does not need to be a single character.
    pub separator: IntSeg,

    /// Whether the path is absolute.
    pub absolute: bool,

    /// Internal segments of the path.
    pub segments: Vec<IntSeg>,
}

impl IntPath {
    /// Allocates an empty `IntPath`.
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates a new `IntPath` with a given capacity used to create the internal `Vec<IntSeg>`.
    ///
    /// This capacity is the amount of segments, _not_ the length of the path in characters.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            prefix: None,
            separator: main_separator(),
            absolute: false,
            segments: Vec::with_capacity(capacity),
        }
    }

    /// Creates another `IntPath` like `self` but with the given path separator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intpath::IntPath;
    /// let path = IntPath::from("a/path").with_separator("\\");
    /// assert_eq!(path, IntPath::from("a\\path"));
    /// ```
    pub fn with_separator<S>(&self, sep: S) -> Self
    where
        S: Into<IntSeg>,
    {
        let mut this = self.clone();
        this.separator = sep.into();
        this
    }

    /// Creates another `IntPath` like `self` but with the given prefix.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intpath::IntPath;
    /// # use std::ffi::OsString;
    /// let path = IntPath::from("/home/code/rust/intpath").with_prefix("file://");
    /// assert_eq!(path.to_os_string(), OsString::from("file:///home/code/rust/intpath"));
    /// ```
    pub fn with_prefix<S>(&self, sep: S) -> Self
    where
        S: Into<IntSeg>,
    {
        let mut this = self.clone();
        this.prefix = Some(sep.into());
        this
    }

    /// Creates another `IntPath` like `self` but with any prefix removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intpath::IntPath;
    /// let path = IntPath::from("C:\\Windows\\system32").strip_prefix();
    /// assert_eq!(path, IntPath::from("\\Windows\\system32"));
    /// ```
    pub fn strip_prefix(&self) -> Self {
        let mut this = self.clone();
        this.prefix = None;
        this
    }

    /// Creates another `IntPath` like `self` but extended with `path`.
    ///
    ///  - if `path` is relative, it is appended;
    ///  - if `path` has a prefix, it replaced `self`;
    ///  - if `self` has a prefix and `path` is absolute, `self`'s prefix is kept and the pathname
    ///    is replaced.
    ///
    /// # Examples
    ///
    /// Joining a relative path extends the existing one:
    ///
    /// ```
    /// # use intpath::IntPath;
    /// let path = IntPath::from("/tmp");
    /// assert_eq!(path.join("file.bk"), IntPath::from("/tmp/file.bk"));
    /// ```
    ///
    /// Joining an absolute path overrides the existing:
    ///
    /// ```
    /// # use intpath::IntPath;
    /// let path = IntPath::from("/tmp");
    /// assert_eq!(path.join("/etc"), IntPath::from("/etc"));
    /// ```
    ///
    /// Joining a prefixed path overrides as well:
    ///
    /// ```
    /// # use intpath::IntPath;
    /// let path = IntPath::from("http://example.com");
    /// assert_eq!(path.join("https://passcod.name"), IntPath::from("https://passcod.name"));
    /// ```
    ///
    /// Joining onto a prefixed path preserves the prefix:
    ///
    /// ```
    /// # use intpath::IntPath;
    /// let path = IntPath::from("E:\\Games");
    /// assert_eq!(path.join("Vidya"), IntPath::from("E:\\Games\\Vidya"));
    /// assert_eq!(path.join("/Photos"), IntPath::from("E:\\Photos"));
    /// ```
    pub fn join<P>(&self, path: P) -> Self
    where
        P: Into<Self>,
    {
        let path: Self = path.into();
        if path.absolute {
            path
        } else {
            let mut this = self.clone();
            this.segments.extend(path.segments);
            this
        }
    }

    /// Creates another `IntPath` like `self` but without its last segment, if there is one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intpath::IntPath;
    /// let path = IntPath::from("/foo/bar");
    /// assert_eq!(path.parent(), IntPath::from("/foo"));
    /// assert_eq!(path.parent().parent(), IntPath::from("/"));
    /// assert_eq!(path.parent().parent().parent(), IntPath::from("/"));
    /// ```
    ///
    /// Taking the parent of a prefixed path never removes the prefix:
    ///
    /// ```
    /// # use intpath::IntPath;
    /// let path = IntPath::from("editor:///home/code/source.rs");
    /// assert_eq!(path.parent(), IntPath::from("editor:///home/code"));
    /// assert_eq!(path.parent().parent().parent().parent(), IntPath::from("editor:///"));
    /// ```
    pub fn parent(&self) -> Self {
        let mut this = self.clone();
        this.segments.pop();
        this
    }

    // TODO: more methods
}

/// `IntPath` behind an `Arc`.
///
/// `ArcPath` exists because cloning an `IntPath` is still expensive, due to the segmentation and
/// metadata fields. An `ArcPath`, on the other hand, is cheap to clone, and only incurs expensive
/// cloning when modifying the path.
///
/// Unlke `IntSeg`, no effort is made to deduplicate paths: `apath.push("c")` and `bpath.push("c")`
/// will create two distinct `IntPath`s and therefore two distinct `ArcPath`s. However, the
/// path segments in each will still be shared.
///
/// # Examples
///
/// ```
/// use intpath::{ArcPath, IntPath};
/// use std::sync::Arc;
///
/// let p: Arc<IntPath> = <IntPath as ArcPath>::new();
/// ```
pub trait ArcPath {
    /// Allocates an empty `ArcPath`.
    fn new() -> Arc<Self> {
        Self::with_capacity(0)
    }

    /// Creates a new `ArcPath` with a given capacity used to create the internal `Vec<IntSeg>`.
    ///
    /// This capacity is the amount of segments, _not_ the length of the path in characters.
    fn with_capacity(capacity: usize) -> Arc<Self>;

    // TODO: more methods
}

impl ArcPath for IntPath {
    fn with_capacity(capacity: usize) -> Arc<Self> {
        Arc::new(Self::with_capacity(capacity))
    }
}

impl Default for IntPath {
    fn default() -> Self {
        Self {
            prefix: None,
            separator: main_separator(),
            absolute: false,
            segments: Vec::new(),
        }
    }
}

impl<P> From<P> for IntPath
where
    P: Into<PathBuf>,
{
    /// Converts from a PathBuf-like to an IntPath.
    ///
    /// Assumes the directory separator is the platform’s one as per the stdlib.
    fn from(path: P) -> Self {
        let path: PathBuf = path.into();
        let compos = path.components();
        let hint = compos.size_hint();

        let mut absolute = false;
        let mut prefix = None;
        let mut segments: Vec<IntSeg> = Vec::with_capacity(hint.1.unwrap_or(hint.0));

        for comp in compos {
            let os = match comp {
                Component::Prefix(p) => {
                    prefix = Some(p.as_os_str().into());
                    continue;
                }
                Component::RootDir => {
                    absolute = true;
                    continue;
                }
                Component::CurDir => OsStr::new("."),
                Component::ParentDir => OsStr::new(".."),
                Component::Normal(os) => os,
            };

            segments.push(os.into());
        }

        Self {
            prefix,
            separator: main_separator(),
            absolute,
            segments,
        }
    }
}

lazy_static::lazy_static! {
    static ref MAIN_SEPARATOR: IntSeg = {
        IntSeg::from(std::path::MAIN_SEPARATOR.to_string())
    };
}

/// The `IntSeg` of the `MAIN_SEPARATOR`.
pub fn main_separator() -> IntSeg {
    MAIN_SEPARATOR.clone()
}

/// Interned path segment.
///
/// This is an `OsString` that is always stored remotely. The remote storage is a global concurrent
/// hashmap that contains weak `Arc`s of the original strings. Each string is guaranteed to only be
/// stored once, and does not need to be freed as it will drop once all strong copies cease.
///
/// However there is a little leftover as the empty `Weak`s remain in the hashmap. The
/// `intpath::gc()` function may be called to clear out any such entries, and shrink the map. It is
/// healthy to run it once in a while.
#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct IntSeg(Arc<OsString>);

lazy_static::lazy_static! {
    static ref INTERN: Arc<CHashMap<u64, Weak<OsString>>> = Arc::new(CHashMap::new());
}

/// Clears out dead interned paths.
///
/// It is healthy to run this once in a while.
///
/// See the [`IntSeg`] documentation for more.
///
/// [`IntSeg`]: ./struct.IntSeg.html
pub fn gc() {
    INTERN.retain(|_, weak| Weak::upgrade(weak).is_some());
    INTERN.shrink_to_fit();
}

impl IntSeg {
    /// Creates a new `IntSeg` from an [`OsString`].
    ///
    /// Prefer to use [`IntSeg::from`] over this function.
    ///
    /// [`OsString`]: https://doc.rust-lang.org/std/ffi/struct.OsString.html
    /// [`IntSeg::from`]: #impl-From<S>
    ///
    /// # Examples
    ///
    /// ```
    /// # use intpath::IntSeg;
    /// # use std::ffi::OsString;
    /// let from_os_string = IntSeg::new(OsString::from("/the/way/home"));
    /// let from_str = IntSeg::from("/the/way/home");
    /// assert_eq!(from_os_string, from_str);
    /// ```
    pub fn new(seg: OsString) -> Self {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        seg.hash(&mut hasher);
        let hash = hasher.finish();

        let mut arcseg = Arc::new(seg);
        let weakins = Arc::downgrade(&arcseg);
        let weakupd = weakins.clone();

        INTERN.upsert(
            hash,
            || weakins, // insert
            |weak| {
                // update
                if let Some(existing) = Weak::upgrade(weak) {
                    arcseg = existing;
                } else {
                    *weak = weakupd;
                }
            },
        );

        Self(arcseg)
    }

    /// Derefences to an [`OsString`].
    ///
    /// [`OsString`]: https://doc.rust-lang.org/std/ffi/struct.OsString.html
    pub fn to_os_string(&self) -> &OsString {
        self
    }

    /// Derefences to an [`OsStr`].
    ///
    /// [`OsStr`]: https://doc.rust-lang.org/std/ffi/struct.OsStr.html
    pub fn as_os_str(&self) -> &OsStr {
        self
    }
}

impl std::ops::Deref for IntSeg {
    type Target = Arc<OsString>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<Path> for IntSeg {
    fn as_ref(&self) -> &Path {
        self.as_os_str().as_ref()
    }
}

impl<S> From<S> for IntSeg
where
    S: Into<OsString>,
{
    fn from(seg: S) -> Self {
        Self::new(seg.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::{OsStr, OsString};
    use std::ops::Deref;

    #[test]
    fn intseg_from() {
        IntSeg::from("turn");
        IntSeg::from("u".to_string());
        IntSeg::from(PathBuf::from("along-the.way"));
        IntSeg::from(
            PathBuf::from("J’ai trouvé des ఎంతోసియానిన్స్")
                .as_path(),
        );
    }

    #[test]
    fn intseg_from_os_string() {
        let fount = OsString::from("fountain");
        let seg = IntSeg::from(fount.clone());
        let segnt: &OsString = &seg;
        assert_eq!(segnt, &fount);
    }

    #[test]
    fn intseg_eq_intseg() {
        let pot = IntSeg::from("short and stout");
        let kettle = IntSeg::from("short and stout");
        assert_eq!(pot, kettle);
    }

    #[test]
    fn os_string_from_intseg() {
        let cat = IntSeg::from("kitty");
        let puss = OsString::from("kitty");
        let cait: &OsString = &cat;
        assert_eq!(cait, &puss);
    }

    fn accepts_a_path<P: AsRef<Path>>(_: P) -> bool {
        true
    }

    #[test]
    fn intseg_as_path() {
        let key = IntSeg::from("board");
        assert!(accepts_a_path(key));
    }
}
