export RUSTFLAGS="-O -C target-feature=+avx512ifma"
export RAYON_NUM_THREADS=1
cargo +nightly update
cargo +nightly run --release