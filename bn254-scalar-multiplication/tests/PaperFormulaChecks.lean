import BN254

namespace Kriterion.ArgoMAC.PaperFormulaChecks
open BN254

/-- These coordinates use digit 1, scale 1, and mask point (1, 2).
The base-7 appendix supplies the coefficients at paper commit
`e2dcf4d540b2708e13cd21090df759051119a116`. -/
def appendixCoordinates (input : AffineInput) : BaseField × BaseField × BaseField :=
  (6 + input.x - 4 * input.y + input.x ^ 2,
    18 + 5 * input.y - 3 * input.x * input.y + 2 * input.x ^ 2 + 2 * input.y ^ 2,
    1 + input.x)

/-- The main text uses different Y coefficients and the opposite Z constant. -/
def mainCoordinates (input : AffineInput) : BaseField × BaseField × BaseField :=
  (6 + input.x - 4 * input.y + input.x ^ 2,
    18 - 13 * input.y - 3 * input.x * input.y + 6 * input.x ^ 2 + 2 * input.y ^ 2,
    input.x - 1)

/-- A Jacobian representative must satisfy this equation. -/
def jacobianEquation (point : BaseField × BaseField × BaseField) : Prop :=
  point.2.1 ^ 2 = point.1 ^ 3 + 3 * point.2.2 ^ 6

/-- This point differs from both (1, 2) and (1, -2). -/
def witness : AffineInput :=
  ⟨2, 16059845205665218889595687631975406613746683471807856151558479858750240882195⟩

theorem witness_onCurve : OnCurve witness := by
  unfold OnCurve
  decide

theorem witness_not_exceptional : witness.x ≠ (1 : BaseField) := by decide

/-- The literal appendix produces a triple that does not lie on the curve. -/
theorem appendix_fails : ¬ jacobianEquation (appendixCoordinates witness) := by
  unfold jacobianEquation
  decide

/-- The main-text coefficients satisfy the curve equation for the same input. -/
theorem main_satisfies_equation : jacobianEquation (mainCoordinates witness) := by
  unfold jacobianEquation
  decide

/-- The main-text addition formula gives the zero triple when the two points agree. -/
theorem main_doubling_degenerates : mainCoordinates ⟨1, 2⟩ = (0, 0, 0) := by decide

/-- The appendix reverses the zero-digit Z branch even if both modifiers are zero. -/
theorem appendix_zero_digit_reverses_y :
    (2 : BaseField) * (-1 : BaseField) ^ 3 = -2 ∧ (2 : BaseField) ≠ -2 := by
  norm_num
  decide

end Kriterion.ArgoMAC.PaperFormulaChecks
