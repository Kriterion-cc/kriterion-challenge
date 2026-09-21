import Mathlib.Data.Fintype.EquivFin
import ScalarMultiplication
import Security.AdaptivePrivacy
import Security.Correctness
import Encoding

/-!
The challenge specializes BaBe's garbling definition to BN254 and a fixed byte metric.
All paper references use BaBe.latex revision `e2dcf4d540b2708e13cd21090df759051119a116`:
https://github.com/babylonlabs-io/BaBe.latex/tree/e2dcf4d540b2708e13cd21090df759051119a116/Latex.
`preliminaries.tex`, `def:garbling-scheme`, defines correctness and adaptive privacy.
`gc_argomac_new.tex`, `fig:garbled_c_with_cm`, adds curve validation.
The fixed byte layout, exact label type, and query-cost bound are challenge conventions.
The statement retains explicit curve premises. It does not prove those premises.
-/

namespace Kriterion

/-- VCV-io samples the entire finite tape. The parameter does not change this law. -/
noncomputable def uniformRandomTape (Randomness : Type) [Fintype Randomness]
    (witness : Randomness) (_parameter : Nat) : PMF Randomness :=
  Cryptography.uniformTape Randomness witness

/-- A submission supplies executable data and proofs of the fixed challenge rules.
The privacy proof must supply a finite machine for the complete simulator.
Authors may use VCV-io lemmas and reductions to prove these exact fields. -/
structure Solution where
  /-- These finite indices name independent permutations in `preliminaries.tex`, `def:pRPM`. -/
  FixedIndex : Type
  EncIndex : Type
  fixedFinite : Finite FixedIndex
  encFinite : Finite EncIndex
  /-- The private coins do not contain the public oracle. -/
  Randomness : Type
  randomnessFinite : Finite Randomness
  randomness : Randomness
  /-- The public value contains every construction-dependent field used by evaluation. -/
  Public : Type
  EncodingKey : Type
  /-- The decoder recovers the complete public value. This rule defines the scored byte format. -/
  encoding : Encoding Public
  ciphertextBytes : Nat
  /-- These bounds count every query on every construction path. -/
  garbleQueries : Nat
  evaluateQueries : Nat
  /-- The algorithms implement `preliminaries.tex`, `def:garbling-scheme`.
  The evaluator receives its input separately from the 508 Lamport blocks. -/
  scheme : (field : BN254.FieldCertificate) → @BN254.GroupCertificate field →
    GarbledCircuit BN254.NonZeroScalar BN254.AffineInput (Option (@BN254.Point field))
      (Randomness × Cryptography.PublicOracle FixedIndex EncIndex) Public EncodingKey GarbledCircuit.LamportSignature
      (Cryptography.PublicOracle FixedIndex EncIndex)
  /-- These programs receive oracle answers only through query nodes. -/
  garbleProgram : (field : BN254.FieldCertificate) → @BN254.GroupCertificate field →
    Nat → BN254.NonZeroScalar → Randomness →
      Cryptography.QueryProgram (Cryptography.publicOracleSpec FixedIndex EncIndex)
        (Public × EncodingKey) garbleQueries
  evaluateProgram : (field : BN254.FieldCertificate) → @BN254.GroupCertificate field →
    Public → BN254.AffineInput → GarbledCircuit.LamportSignature →
      Cryptography.QueryProgram (Cryptography.publicOracleSpec FixedIndex EncIndex)
        (Option (Option (@BN254.Point field))) evaluateQueries
  /-- The proof view agrees with the programs for every complete oracle. -/
  garbleProgramCorrect : ∀ field group parameter scalar coins oracle,
    (garbleProgram field group parameter scalar coins).eval (Cryptography.publicAnswer oracle) =
      (scheme field group).garble parameter scalar (coins, oracle)
  evaluateProgramCorrect : ∀ field group circuit input labels oracle,
    (evaluateProgram field group circuit input labels).eval (Cryptography.publicAnswer oracle) =
      (scheme field group).evaluate oracle circuit input labels
  /-- Every generated circuit has the same byte layout. This property does not specify a gate graph. -/
  ciphertextSize : ∀ field group parameter scalar tape,
    (encoding.encode ((scheme field group).garble parameter scalar tape).1).length = ciphertextBytes
  /-- Encoding returns only the selected blocks. See `preliminaries.tex`, `eq:lampsig-sig`. -/
  lamportCompatible : ∀ field group, GarbledCircuit.LamportCompatibility (scheme field group) affineLamportBits
  /-- The target rejects off-curve inputs. See `gc_argomac_new.tex`, `fig:garbled_c_with_cm`. -/
  functionCorrect : ∀ field group scalar input, (scheme field group).function scalar input =
    @checkedScalarMultiplication field group scalar.value input
  /-- Correctness covers every input and tape, including rejection. See `def:garbling-scheme`. -/
  perfectCorrectness : ∀ field group, GarbledCircuit.PerfectCorrectness (scheme field group) Prod.snd
  /-- The same machine serves every adversary and scalar within the fixed budget. -/
  adaptivePrivacy : ∀ (field : BN254.FieldCertificate) (group : @BN254.GroupCertificate field),
    letI := field
    letI := @Fintype.ofFinite FixedIndex fixedFinite
    letI := @Fintype.ofFinite EncIndex encFinite
    letI := Classical.decEq FixedIndex
    letI := Classical.decEq EncIndex
    GarbledCircuit.OracleAdaptivePrivacy (scheme field group) encoding ciphertextBytes
      (@uniformRandomTape Randomness (@Fintype.ofFinite Randomness randomnessFinite) randomness)
      (fun parameter scalar coins => (garbleProgram field group parameter scalar coins).toOracleProgram)

end Kriterion
