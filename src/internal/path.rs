use std::cmp::Ordering;
use std::collections::HashMap;
use std::io;
use std::path::{Component, Path, PathBuf};
use std::sync::OnceLock;

// ========================================================================= //

pub struct CaseMapper(HashMap<char, char>);

impl CaseMapper {
    fn new() -> CaseMapper {
        // extracted exceptional uppercase characters from icu_casemap library
        CaseMapper(include!("uppercase.txt").iter().copied().collect())
    }
    fn simple_uppercase(&self, c: char) -> char {
        self.0.get(&c).copied().or(c.to_uppercase().next()).unwrap_or_default()
    }
}

const MAX_NAME_LEN: usize = 31;

// ========================================================================= //

/// Converts a char to uppercase as defined in MS-CFB,
/// using simple capitalization and the ability to add exceptions.
/// Used when two directory entry names need to be compared.
fn cfb_uppercase_char(c: char) -> char {
    static CASE_MAPPER: OnceLock<CaseMapper> = OnceLock::new();
    let case_mapper = CASE_MAPPER.get_or_init(CaseMapper::new);

    // TODO: Edge cases can be added that appear
    // in the table from Appendix A, <3> Section 2.6.4

    // Base case, just do a simple uppercase
    // equivalent to icu_casemap::CaseMapper::new().simple_uppercase(c)
    case_mapper.simple_uppercase(c)
}

/// Compares two directory entry names according to CFB ordering, which is
/// case-insensitive, and which always puts shorter names before longer names,
/// as encoded in UTF-16 (i.e. [shortlex
/// order](https://en.wikipedia.org/wiki/Shortlex_order), rather than
/// dictionary order).
pub fn compare_names(name1: &str, name2: &str) -> Ordering {
    if name1 == name2 {
        return Ordering::Equal;
    }
    if name1.is_ascii() && name2.is_ascii() {
        match name1.len().cmp(&name2.len()) {
            Ordering::Equal => {
                for (left, right) in name1.bytes().zip(name2.bytes()) {
                    let left = left.to_ascii_uppercase();
                    let right = right.to_ascii_uppercase();
                    match left.cmp(&right) {
                        Ordering::Equal => {}
                        other => return other,
                    }
                }
                Ordering::Equal
            }
            other => other,
        }
    } else {
        match name1.encode_utf16().count().cmp(&name2.encode_utf16().count()) {
            // This is actually not 100% correct -- the MS-CFB spec specifies a
            // particular way of doing the uppercasing on individual UTF-16 code
            // units, along with a list of weird exceptions and corner cases.  But
            // hopefully this is good enough for 99+% of the time.
            Ordering::Equal => {
                let mut left_iter = name1.chars();
                let mut right_iter = name2.chars();
                loop {
                    match (left_iter.next(), right_iter.next()) {
                        (Some(left), Some(right)) => {
                            let left = cfb_uppercase_char(left);
                            let right = cfb_uppercase_char(right);
                            match left.cmp(&right) {
                                Ordering::Equal => {}
                                other => return other,
                            }
                        }
                        (None, None) => return Ordering::Equal,
                        (None, Some(_)) => return Ordering::Less,
                        (Some(_), None) => return Ordering::Greater,
                    }
                }
            }
            other => other,
        }
    }
}

/// Converts a storage/stream name to UTF-16, or returns an error if the name
/// is invalid.
pub fn validate_name(name: &str) -> io::Result<Vec<u16>> {
    let name_utf16: Vec<u16> =
        name.encode_utf16().take(MAX_NAME_LEN + 1).collect();
    if name_utf16.len() > MAX_NAME_LEN {
        invalid_input!(
            "Object name cannot be more than {} UTF-16 code units (was {})",
            MAX_NAME_LEN,
            name.encode_utf16().count()
        );
    }
    for &chr in &['/', '\\', ':', '!'] {
        if name.contains(chr) {
            invalid_input!("Object name cannot contain {} character", chr);
        }
    }
    Ok(name_utf16)
}

// ========================================================================= //

/// Given a path within a compound file, turns it into a list of child names
/// descending from the root.  Returns an error if the name is invalid.
pub fn name_chain_from_path(path: &Path) -> io::Result<Vec<&str>> {
    let mut names: Vec<&str> = Vec::new();
    for component in path.components() {
        match component {
            Component::Prefix(_) => {
                invalid_input!("Invalid path (must not have prefix)");
            }
            Component::RootDir => names.clear(),
            Component::CurDir => {}
            Component::ParentDir => {
                if names.pop().is_none() {
                    invalid_input!("Invalid path (must be within root)");
                }
            }
            Component::Normal(osstr) => match osstr.to_str() {
                Some(name) => names.push(name),
                None => invalid_input!("Non UTF-8 path"),
            },
        }
    }
    Ok(names)
}

pub fn path_from_name_chain(names: &[&str]) -> PathBuf {
    let mut path = PathBuf::from("/");
    for name in names {
        path.push(name);
    }
    path
}

// ========================================================================= //

#[cfg(test)]
mod tests {
    use super::{
        cfb_uppercase_char, compare_names, name_chain_from_path,
        path_from_name_chain, validate_name,
    };
    use std::cmp::Ordering;
    use std::path::{Path, PathBuf};

    #[test]
    fn name_ordering() {
        assert_eq!(compare_names("foobar", "FOOBAR"), Ordering::Equal);
        assert_eq!(compare_names("foo", "barfoo"), Ordering::Less);
        assert_eq!(compare_names("Foo", "bar"), Ordering::Greater);
        // testcases from real .doc files
        assert_eq!(
            compare_names(
                "ÖÇÔÍÒÄÁØÐÔÞ3×ÆXVÔÄHMDQ==",
                "ßYÜ0MÈÝEÄÄÂKÏÓÉDÀP5ÃÝA=="
            ),
            Ordering::Less
        );
        assert_eq!(
            compare_names(
                "É1EDAÉNÅPUOÈÒKÔÓCÓÇÇPÐ==",
                "ßÕFÆRDÜÐNÔCÄ2PKQÃFAFMA=="
            ),
            Ordering::Less
        );

        let uppercase = "ßQÑ52Ç4ÅÁÔÂFÛCWCÙÂNË5Q=="
            .chars()
            .map(cfb_uppercase_char)
            .collect::<String>();

        assert_eq!("ßQÑ52Ç4ÅÁÔÂFÛCWCÙÂNË5Q==", uppercase);

        assert_eq!(
            compare_names(
                "ÜL43ÁMÆÛÏEKZÅYWÚÓVDÙÄÀ==",
                "ßQÑ52Ç4ÅÁÔÂFÛCWCÙÂNË5Q=="
            ),
            Ordering::Less
        );
    }

    #[test]
    fn short_name_is_valid() {
        assert_eq!(
            validate_name("Foobar").unwrap(),
            vec![70, 111, 111, 98, 97, 114]
        );
    }

    #[test]
    #[should_panic(
        expected = "Object name cannot be more than 31 UTF-16 code units \
                    (was 35)"
    )]
    fn long_name_is_invalid() {
        validate_name("ThisNameIsMostDefinitelyMuchTooLong").unwrap();
    }

    #[test]
    #[should_panic(expected = "Object name cannot contain / character")]
    fn name_with_slash_is_invalid() {
        validate_name("foo/bar").unwrap();
    }

    #[test]
    fn absolute_path_is_valid() {
        assert_eq!(
            name_chain_from_path(Path::new("/foo/bar/baz/")).unwrap(),
            vec!["foo", "bar", "baz"]
        );
    }

    #[test]
    fn relative_path_is_valid() {
        assert_eq!(
            name_chain_from_path(Path::new("foo/bar/baz")).unwrap(),
            vec!["foo", "bar", "baz"]
        );
    }

    #[test]
    fn path_with_parents_is_valid() {
        assert_eq!(
            name_chain_from_path(Path::new("foo/bar/../baz")).unwrap(),
            vec!["foo", "baz"]
        );
    }

    #[test]
    #[should_panic(expected = "Invalid path (must be within root)")]
    fn parent_of_root_is_invalid() {
        name_chain_from_path(Path::new("foo/../../baz")).unwrap();
    }

    #[test]
    fn canonical_path_is_absolute() {
        let path = Path::new("foo/bar/../baz");
        let names = name_chain_from_path(path).unwrap();
        assert_eq!(path_from_name_chain(&names), PathBuf::from("/foo/baz"));
    }

    #[ignore = "add icu_casemap to dependencies to regenerate exceptional uppercase chars"]
    #[test]
    fn uppercase_generation() {
        use std::fmt;

        struct AsArray(Vec<(char, char)>);

        impl fmt::Display for AsArray {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("[")?;
                let s = self
                    .0
                    .iter()
                    .map(|(input, output)| format!("('{input}', '{output}')"))
                    .collect::<Vec<_>>()
                    .join(", ");
                f.write_str(&s)?;
                f.write_str("]")
            }
        }

        let case_mapper = super::CaseMapper::new();
        // uncomment line to regenerate exceptions
        // let case_mapper = icu_casemap::CaseMapper::new();
        let mut nonequal = Vec::new();
        for i in 0..u32::MAX {
            let Some(c) = char::from_u32(i) else {
                continue;
            };
            let u1 = case_mapper.simple_uppercase(c);
            let mut uppers = c.to_uppercase();
            let u2 = uppers.next().unwrap();
            if u1 != u2 || uppers.next().is_some() {
                nonequal.push((c, u1));
            }
        }
        let array = AsArray(nonequal);
        std::fs::write("src/internal/uppercase.txt", array.to_string())
            .unwrap();
    }
}

// ========================================================================= //
