`tetris` is a backend agnostic tool for circuit building. It collects various types of constraints and copy relations between witnesses. In synthesis time it stores constaints as intermediate representations that would define a circuit. It generates witnesses in prover time. Witness values filled in intermediate representations then can be moved to a backend to generate the proof. It is compatible with [zkcrypto/ff](https://github.com/zkcrypto/ff/) and [arkworks/ark-ff](https://github.com/arkworks-rs/algebra/tree/master/ff) and [plonky3/p3-field](https://github.com/Plonky3/Plonky3/tree/main/field) field traits. This should allow further integrations to other proof system backends. Additionally we provide integration with the halo2 backend.

Alongside collecting linear-in-witness or quadratic-in-witness zero sum relations, `tetris` has a few build in gadgets:

* Range decompositions
  * A special type of linear-in-witness expression
* Dynamic read only memory where table is determined in prover time
* Static read only memory, typical vector lookups
* Poseidon sponge
* Non native field arithmetic
  * Also available when modulus is determined in prover time
* Short Weistrass ECC operations
  * Including MSM & ECDSA verification
* RSA signature verification with SHA256
* BN254 pairing check

Some of the techniques in gadgets are ported or inspired from [barratenberg](https://github.com/AztecProtocol/barretenberg), [axiom-crypto/halo2-lib](https://github.com/axiom-crypto/halo2-lib), [pse/halo2wrong](https://github.com/privacy-scaling-explorations/halo2wrong)