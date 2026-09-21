import Cryptography.OperationalOracle
import Cryptography.Primitives

namespace Kriterion.ArgoMAC.Security.OperationalOracle
open Cryptography

/-- This interpreter samples each oracle transition when a query reaches it. -/
noncomputable def runSampled {oracle : OracleSpec} {Result State : Type}
    (handler : ∀ query, State → PMF (oracle.Answer query × State)) :
    {budget : Nat} → OracleProgram oracle Result budget → State → PMF (Result × State)
  | _, .pure distribution, state => distribution.map (fun value => (value, state))
  | _, .query request next, state =>
      (handler request state).bind (fun answer => runSampled handler (next answer.1) answer.2)
  | _, .sample distribution next, state =>
      distribution.bind (fun value => runSampled handler (next value) state)

end Kriterion.ArgoMAC.Security.OperationalOracle

namespace Kriterion.Cryptography.LazyOracle

open Kriterion.ArgoMAC.Security.OperationalOracle

/-- The oracle stores one partial injection for each permutation index. -/
structure State (FixedIndex EncIndex : Type) where
  fixed : FixedIndex → SparsePermutation (2 ^ 128)
  enc : EncIndex → SparsePermutation (2 ^ 128)
  hash : HashTable BN254.BaseField (Fintype.card (Block × Block))

def empty : State FixedIndex EncIndex :=
  ⟨fun _ => .empty _, fun _ => .empty _, []⟩

private noncomputable def hashEquiv : (Block × Block) ≃ Fin (Fintype.card (Block × Block)) :=
  Fintype.equivFin _

/-- A lookup reads a stored pair without sampling. -/
def permutationLookup (state : SparsePermutation size) (input : Fin size) : Option (Fin size) :=
  if state.knownInput input then some (state.output (state.input.symm input)) else none

/-- A programming request must use a fresh input and a fresh output. -/
def permutationProgram (state : SparsePermutation size) (input output : Fin size) :
    Option (SparsePermutation size) :=
  if fresh : ¬ state.knownInput input ∧ ¬ state.knownOutput output then
    some (state.extend (by have := (state.input.symm input).isLt; unfold SparsePermutation.knownInput at fresh; omega)
      (state.input.symm input) (state.output.symm output))
  else none

/-- A used domain or range makes a programming request fail. -/
theorem permutationProgram_reject (state : SparsePermutation size) (input output : Fin size)
    (used : state.knownInput input ∨ state.knownOutput output) :
    permutationProgram state input output = none := by
  simp only [permutationProgram]
  split
  · rename_i fresh
    exact (used.elim fresh.1 fresh.2).elim
  · rfl

/-- A new programmed pair becomes available in the same partial permutation. -/
theorem permutationProgram_lookup (state next : SparsePermutation size) (input output : Fin size)
    (success : permutationProgram state input output = some next) :
    permutationLookup next input = some output := by
  unfold permutationProgram at success
  split at success
  · cases success
    simp [permutationLookup, SparsePermutation.knownInput, SparsePermutation.extend,
      SparsePermutation.input, SparsePermutation.output, swaps]
  · contradiction

/-- A forward query records the exact pair that it returns. -/
theorem forward_lookup (state : SparsePermutation size) (input : Fin size)
    (answer : Fin size × SparsePermutation size)
    (member : answer ∈ (state.forward input).distribution.support) :
    permutationLookup answer.2 input = some answer.1 := by
  unfold SparsePermutation.forward at member
  dsimp only at member
  split at member
  · simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst answer
    simp_all [permutationLookup, SparsePermutation.knownInput]
  · obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same]
    simp [permutationLookup, SparsePermutation.knownInput, SparsePermutation.extend,
      SparsePermutation.input, SparsePermutation.output, SparsePermutation.suffix, swaps]

/-- A stored forward pair also determines its inverse. -/
theorem lookup_inverse (state : SparsePermutation size) (input output : Fin size)
    (known : permutationLookup state input = some output) :
    permutationLookup state.reverse output = some input := by
  unfold permutationLookup at known
  split at known
  · cases known
    simp_all [permutationLookup, SparsePermutation.reverse, SparsePermutation.knownInput,
      SparsePermutation.input, SparsePermutation.output]
  · contradiction

/-- A repeated forward query returns its stored answer without sampling. -/
theorem lookup_forward (state : SparsePermutation size) (input output : Fin size)
    (known : permutationLookup state input = some output) :
    state.forward input = Draw.pure (output, state) := by
  unfold permutationLookup at known
  split at known
  · cases known
    simp_all [SparsePermutation.forward, SparsePermutation.knownInput]
  · contradiction

/-- The public handler uses the same stored pairs in both query directions. -/
noncomputable def query [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (request : PublicQuery FixedIndex EncIndex) (state : State FixedIndex EncIndex) :
    PMF (request.Answer × State FixedIndex EncIndex) :=
  match request with
  | .fixedForward index input => ((state.fixed index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1, { state with fixed := Function.update state.fixed index answer.2 }))
  | .fixedInverse index output => ((state.fixed index).inverse output.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1, { state with fixed := Function.update state.fixed index answer.2 }))
  | .encForward index input => ((state.enc index).forward input.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1, { state with enc := Function.update state.enc index answer.2 }))
  | .encInverse index output => ((state.enc index).inverse output.toFin).distribution.map
      (fun answer => (BitVec.ofFin answer.1, { state with enc := Function.update state.enc index answer.2 }))
  | .hash input => (state.hash.query (Fintype.card_pos) input).distribution.map
      (fun answer => (hashEquiv.symm answer.1, { state with hash := answer.2 }))

/-- The simulator can inspect existing entries without changing the oracle. -/
noncomputable def lookup (request : PublicQuery FixedIndex EncIndex)
    (state : State FixedIndex EncIndex) : Option request.Answer :=
  match request with
  | .fixedForward index input => (permutationLookup (state.fixed index) input.toFin).map BitVec.ofFin
  | .fixedInverse index output => (permutationLookup (state.fixed index).reverse output.toFin).map BitVec.ofFin
  | .encForward index input => (permutationLookup (state.enc index) input.toFin).map BitVec.ofFin
  | .encInverse index output => (permutationLookup (state.enc index).reverse output.toFin).map BitVec.ofFin
  | .hash input => (state.hash.lookup input).map hashEquiv.symm

/-- Only the simulator receives this operation. Hash values can collide. -/
noncomputable def program [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (request : PublicQuery FixedIndex EncIndex) (answer : request.Answer)
    (state : State FixedIndex EncIndex) : Option (State FixedIndex EncIndex) :=
  match request with
  | .fixedForward index input => (permutationProgram (state.fixed index) input.toFin answer.toFin).map
      (fun next => { state with fixed := Function.update state.fixed index next })
  | .fixedInverse index output => (permutationProgram (state.fixed index) answer.toFin output.toFin).map
      (fun next => { state with fixed := Function.update state.fixed index next })
  | .encForward index input => (permutationProgram (state.enc index) input.toFin answer.toFin).map
      (fun next => { state with enc := Function.update state.enc index next })
  | .encInverse index output => (permutationProgram (state.enc index) answer.toFin output.toFin).map
      (fun next => { state with enc := Function.update state.enc index next })
  | .hash input => if state.hash.lookup input = none then
      some { state with hash := state.hash.program input (hashEquiv answer) } else none

/-- The same fixed interpreter serves constructions and adversaries. -/
noncomputable def run [DecidableEq FixedIndex] [DecidableEq EncIndex]
    {Result : Type} {budget : Nat}
    (computation : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : State FixedIndex EncIndex) : PMF (Result × State FixedIndex EncIndex) :=
  runSampled query computation state

end Kriterion.Cryptography.LazyOracle
