import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

-- Lean must try ordinary equality instances before the generic oracle instances.
attribute [instance 50] OracleSpec.instDecidableEqDomainOfDecidableEq
  OracleSpec.instDecidableEqRangeOfDecidableEq
  PFunctor.instDecidableEqAOfDecidableEq PFunctor.instDecidableEqBOfDecidableEq

namespace Kriterion.Cryptography

/-- VCV-io samples the complete finite tape before the first query. -/
noncomputable def uniformTape (Tape : Type) [Fintype Tape] (witness : Tape) : PMF Tape :=
  letI : Nonempty Tape := ⟨witness⟩
  letI := SampleableType.ofFintype Tape
  (evalSPMF (uniformSample Tape)).run.map (fun value => value.getD witness)

/-- VCV-io gives every complete tape the same probability. -/
theorem uniformTape_eq (Tape : Type) [Fintype Tape] (witness : Tape) :
    uniformTape Tape witness = @PMF.uniformOfFintype Tape _ ⟨witness⟩ := by
  letI : Nonempty Tape := ⟨witness⟩
  letI := SampleableType.ofFintype Tape
  unfold uniformTape
  rw [evalSPMF_uniformSample]
  simp [OptionT.lift, PMF.map_bind, PMF.pure_map, PMF.bind_pure]

/-- The executable projection returns the answer from the complete oracle tape. -/
def randomOracleAnswer (tape : Domain → Range) (input : Domain) : Range :=
  evalWithAnswerFn (QueryImpl.ofFn tape) ((Domain →ₒ Range).query input)

@[simp] theorem randomOracleAnswer_eq (tape : Domain → Range) (input : Domain) :
    randomOracleAnswer tape input = tape input := rfl

/-- VCV-io gives the same answer from the complete cache without new randomness. -/
theorem randomOracle_complete {Domain Range : Type} [DecidableEq Domain]
    [SampleableType Range] (tape : Domain → Range) (input : Domain) :
    (OracleSpec.randomOracle (spec := Domain →ₒ Range) input).run
        (fun value => some (tape value)) =
      pure (randomOracleAnswer tape input, fun value => some (tape value)) :=
  QueryImpl.withCaching_run_some _ rfl

end Kriterion.Cryptography
