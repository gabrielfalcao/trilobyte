/// `TriloByteParseError` represents errors when converting any types to `TriloByte`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TriloByteParseError(pub String, pub u8);
impl std::error::Error for TriloByteParseError {}
impl std::fmt::Display for TriloByteParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "invalid conversion from {} to TriloByte {}", self.0, self.1)
    }
}
