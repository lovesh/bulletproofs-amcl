# Bulletproofs

1. On a pairing friendly curve. BLS12-381 and BN254 for now. Adjust the value of `BLSCurve` in [lib.rs](src/lib.rs)
2. Using [Apache Milagro](https://github.com/milagro-crypto/amcl).
3. Pending support for aggregation, non power of 2 values and inner product verification through multi-exponentiation.