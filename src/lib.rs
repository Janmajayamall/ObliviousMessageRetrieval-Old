pub mod client;
pub mod pvw;
pub mod server;
pub mod utils;
pub use fhe;
pub use fhe_traits;

pub const MODULI_OMR: &[u64; 15] = &[
    268369921,
    549755486209,
    1152921504606584833,
    1152921504598720513,
    1152921504597016577,
    1152921504595968001,
    1152921504595640321,
    1152921504593412097,
    1152921504592822273,
    1152921504592429057,
    1152921504589938689,
    1152921504586530817,
    4293918721,
    1073479681,
    1152921504585547777,
];
pub const DEGREE: usize = 1 << 15;
pub const MODULI_OMR_PT: &[u64; 1] = &[65537];
pub const SET_SIZE: usize = 1 << 15;
pub const VARIANCE: usize = 10;

// SRLC params
pub const K: usize = 50;
pub const M: usize = 100;
pub const DATA_SIZE: usize = 256;
// m_row_span = 256 bytes / 2 bytes
// since each row can store upto 2 bytes
// of data.
pub const M_ROW_SPAN: usize = 128;
pub const GAMMA: usize = 5;
// no of cts required to accomodate all
// rows of buckets; = CEIL((M * M_ROW_SPACE) / DEGREE)
pub const CT_SPAN_COUNT: usize = 7;
