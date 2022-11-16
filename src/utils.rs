use byteorder::{ByteOrder, LittleEndian, ReadBytesExt};
use fhe_math::zq::Modulus;
use std::fs::File;
use std::io::Write;

pub fn read_range_coeffs(path: &str) -> Vec<u64> {
    let mut file = File::open(path).unwrap();
    let mut buf = vec![0u64; 65536];
    file.read_u64_into::<LittleEndian>(&mut buf).unwrap();
    buf
}

pub fn precompute_range_coeffs() {
    // precompute coefficients
    //
    // Range function returns 1 if input > 65536 / 2
    // otherwise returns 0.
    let q = Modulus::new(65537).unwrap();
    let mut coeffs = vec![];
    for i in 1..65537 {
        let mut sum = 0;
        dbg!(i);
        for a in 0..65537 {
            // f(a) * a.pow(65536 - i)
            if a >= 32768 {
                sum = q.add(sum, q.pow(a, 65536 - i));
            }
        }
        coeffs.push(sum);
    }
    let mut bug = [0u8; 65536 * 8];
    LittleEndian::write_u64_into(&coeffs, &mut bug);
    let mut f = File::create("params.bin").unwrap();
    f.write_all(&bug);
}
