//! trilobyte
//!
//! This crate provides the [`TriloByte`] data-structure.

pub mod errors;
pub use errors::TriloByteParseError;

pub mod trilobyte;
pub use trilobyte::{TriloByte, high_water_mark_u8_to_trilobyte};


#[macro_export]
macro_rules! dbg_bits {
    ($val:expr) => {{
        let bits = format!("{:b}", $val);
        eprintln!("{:#?} = {} = {}", stringify!($val), bits, $val);
        $val
    }};
}
#[macro_export]
macro_rules! assert_bits_eq {
    ($left:expr, $right:expr $(,)?) => {
        match (&$left, &$right) {
            (left_val, right_val) => {
                assert_eq!(format!("{:b}", *left_val as u8), format!("{:b}", *right_val as u8));
            }
        }
    };
    ($left:expr, $right:expr, $($arg:tt)+) => {
        match (&$left, &$right) {
            (left_val, right_val) => {
                assert_eq!(format!("{:b}", *left_val as u8), format!("{:b}", *right_val as u8), $arg);
            }
        }
    };
}
