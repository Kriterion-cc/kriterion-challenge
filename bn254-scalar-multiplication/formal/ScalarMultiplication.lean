import BN254

/-!
This module defines the checked target function.
The [BaBe source](https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_argomac_new.tex) fixes the paper references below.
-/

namespace Kriterion

open BN254

/-- The paper orders the 254 little-endian x bits before the 254 y bits. -/
def affineLamportBits (input : AffineInput) : BitVec 508 :=
  BitVec.ofNat 508 (input.x.val + input.y.val * 2 ^ 254)

def scalarMultiplication [BN254.FieldCertificate] [BN254.GroupCertificate]
    (scalar : ScalarField) (point : Point) : Point :=
  scalar • point

/-- Off-curve inputs return `none`; valid inputs return the scalar multiple.
See `gc_argomac_new.tex`, `fig:garbled_c_with_cm`. `some 0` denotes the group identity. -/
def checkedScalarMultiplication [BN254.FieldCertificate]
    [BN254.GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) : Option Point :=
  (decodePoint input).map (scalarMultiplication scalar)

end Kriterion
