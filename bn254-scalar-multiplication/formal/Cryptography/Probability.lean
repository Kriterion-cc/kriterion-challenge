import VCVio.EvalDist.TVDist
import VCVio.EvalDist.Defs.Instances

namespace Kriterion.Cryptography.Probability

/-- This instance exposes PMF support to VCV-io. -/
noncomputable instance pmfSupport : MonadLiftT PMF SetM where
  monadLift p := p.support

noncomputable instance pmfSupportLawful : LawfulMonadLiftT PMF SetM where
  monadLift_pure := PMF.support_pure
  monadLift_bind := PMF.support_bind

noncomputable instance pmfSupportCompatible : EvalDistCompatible PMF where
  support_eq_SPMF_support p := (SPMF.support_liftM p).symm

/-- Both libraries assign the same probability to each event. -/
theorem event_eq {A : Type*} (p : PMF A) (event : Set A) :
    probEvent p event = p.toOuterMeasure event := by
  rw [probEvent_eq_tsum_indicator p event]
  simp only [PMF.probOutput_eq_apply, PMF.toOuterMeasure_apply]
  rfl
universe w

/-- The lifted binary space preserves all source type universes. -/
private theorem binary_distance (p q : PMF (Option PUnit.{w+1})) :
    p.etvDist q = ENNReal.absDiff (p (some PUnit.unit)) (q (some PUnit.unit)) := by
  have noneMass (p : PMF (Option PUnit.{w+1})) : p none = 1 - p (some PUnit.unit) := by
    have h := p.tsum_coe
    rw [tsum_option _ ENNReal.summable, tsum_fintype, Fintype.sum_unique] at h
    exact (ENNReal.sub_eq_of_eq_add (PMF.apply_ne_top p _) h.symm).symm
  simp only [PMF.etvDist]
  rw [tsum_option _ ENNReal.summable, tsum_fintype, Fintype.sum_unique, noneMass, noneMass,
    ENNReal.absDiff_tsub_tsub (PMF.coe_le_one p _) (PMF.coe_le_one q _) ENNReal.one_ne_top]
  rw [← two_mul, mul_div_assoc]
  simp [ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- VCV-io data processing bounds every event difference. -/
theorem event_difference_le {A : Type w} (p q : PMF A) (event : Set A) :
    |(p.toOuterMeasure event).toReal - (q.toOuterMeasure event).toReal| ≤ tvDist p q := by
  classical
  let choose : Option A → Option PUnit.{w+1} := fun x => if ∃ a ∈ event, x = some a then some PUnit.unit else none
  have mass (p : PMF A) : ((evalSPMF p).toPMF.map choose) (some PUnit.unit) = p.toOuterMeasure event := by
    simp only [PMF.map_apply, PMF.toOuterMeasure_apply, evalSPMF, SPMF.toPMF]
    rw [tsum_option _ ENNReal.summable]
    simp [choose, Set.indicator]
  rw [← ENNReal.absDiff_toReal (by rw [← event_eq]; exact probEvent_ne_top) (by rw [← event_eq]; exact probEvent_ne_top)]
  apply ENNReal.toReal_mono (PMF.etvDist_ne_top _ _)
  rw [← mass p, ← mass q, ← binary_distance]
  exact PMF.etvDist_map_le choose _ _

/-- VCV-io bounds identical games by the probability of their bad event. -/
theorem identical_until_bad {A : Type*} (p q : PMF A) (bad event : Set A)
    (agree : ∀ x ∉ bad, p x = q x) :
    |(p.toOuterMeasure event).toReal - (q.toOuterMeasure event).toReal| ≤
      (q.toOuterMeasure bad).toReal := by
  have good : probEvent p (fun x => x ∉ bad) = probEvent q (fun x => x ∉ bad) := by
    classical
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ bad <;> simp [hx, PMF.probOutput_eq_apply, agree x]
  have totalP := probEvent_compl p bad
  have totalQ := probEvent_compl q bad
  simp only [probFailure_eq_zero, tsub_zero] at totalP totalQ
  have badMass : probEvent p bad = probEvent q bad := by
    erw [good] at totalP
    exact (ENNReal.add_left_inj probEvent_ne_top).mp (totalP.trans totalQ.symm)
  have bound := tvDist_le_probEvent_of_probOutput_eq_of_not (mx := p) (my := q)
    bad (fun x hx => by simpa only [PMF.probOutput_eq_apply] using agree x hx) badMass
  erw [badMass, event_eq] at bound
  exact (event_difference_le p q event).trans bound

universe ua ub

/-- VCV-io lifts each conditional bound through arbitrary private sampling. -/
theorem bind_event_le {A : Type ua} {B : Type ub} (p : PMF A) (f : A → PMF B)
    (event : Set B) (bound : ENNReal)
    (law : ∀ x ∈ p.support, (f x).toOuterMeasure event ≤ bound) :
    (p.bind f).toOuterMeasure event ≤ bound := by
  have lifted := probEvent_bind_le_of_forall_le
    (mx := p.map (ULift.up : A → ULift.{ub} A))
    (my := fun x => (f x.down).map (ULift.up : B → ULift.{ua} B))
    (q := fun y => y.down ∈ event)
    (ε := bound) (by
      rintro ⟨x⟩ hx
      have member : x ∈ p.support := by
        change ULift.up x ∈ (p.map ULift.up).support at hx
        simpa using hx
      erw [event_eq]
      erw [PMF.toOuterMeasure_map_apply]
      exact law x member)
  erw [event_eq] at lifted
  simp only [PMF.monad_bind_eq_bind, PMF.bind_map, ← PMF.map_bind] at lifted
  erw [PMF.toOuterMeasure_map_apply] at lifted
  exact lifted

end Kriterion.Cryptography.Probability
