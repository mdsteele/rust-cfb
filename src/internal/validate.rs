//===========================================================================//

/// A parsing validation strategy.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Validation {
    /// As much as possible, spec violations will be ignored when parsing.
    Permissive,
    /// Any violation of the CFB spec will be treated as an error when parsing.
    Strict,
}

impl Validation {
    /// Returns true for `Strict` validation, false otherwise.
    pub fn is_strict(self) -> bool {
        match self {
            Validation::Permissive => false,
            Validation::Strict => true,
        }
    }
}

//===========================================================================//
