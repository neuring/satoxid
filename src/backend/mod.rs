mod dimacs;
pub use dimacs::DimacsWriter;

#[cfg(feature = "cadical")]
mod cadical;
#[cfg(feature = "cadical")]
pub use self::cadical::CadicalEncoder;
