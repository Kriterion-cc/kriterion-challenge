import Cryptography.RandomOracle
import BN254
import Cryptography.Probability
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.QueryTracking.QueryBound
import Mathlib.Data.BitVec
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
This module defines the executable oracle primitives.
The [BaBe source](https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_optimizations.tex) fixes the paper references below.
-/

namespace Kriterion.Cryptography

universe uIndex uBlock uDomain uRange uKey uMessage uCipher uCounter uState
  uQuery uAnswer uResult

/-- An oracle specification fixes each query and its answer type. -/
structure OracleSpec where
  Query : Type uQuery
  Answer : Query → Type uAnswer

/-- An oracle handler answers one query and updates one shared state. -/
abbrev OracleHandler (oracle : OracleSpec.{uQuery, uAnswer}) (State : Type uState) :=
  ∀ query, State → oracle.Answer query × State

/-- A construction computes locally and reads the oracle only through query nodes. -/
inductive QueryProgram (oracle : OracleSpec.{0, 0}) (Result : Type) : Nat → Type 1
  | pure {budget : Nat} (result : Result) : QueryProgram oracle Result budget
  | query {budget : Nat} (request : oracle.Query)
      (next : oracle.Answer request → QueryProgram oracle Result budget) :
      QueryProgram oracle Result (budget + 1)

namespace QueryProgram

/-- This interpreter uses one fixed oracle. -/
def eval {oracle : OracleSpec.{0, 0}} {Result : Type} (answer : ∀ q, oracle.Answer q) :
    {budget : Nat} → QueryProgram oracle Result budget → Result
  | _, .pure result => result
  | _, .query request next => eval answer (next (answer request))

def map {oracle : OracleSpec.{0, 0}} {First Second : Type} (f : First → Second) :
    {budget : Nat} → QueryProgram oracle First budget → QueryProgram oracle Second budget
  | _, .pure result => .pure (f result)
  | _, .query request next => .query request (fun answer => map f (next answer))

def castBudget {oracle : OracleSpec.{0, 0}} {Result : Type} {first second : Nat}
    (equal : first = second) (program : QueryProgram oracle Result first) :
    QueryProgram oracle Result second := equal ▸ program

@[simp] theorem eval_castBudget {oracle : OracleSpec.{0, 0}} {Result : Type}
    (answer : ∀ q, oracle.Answer q) {first second : Nat} (equal : first = second)
    (program : QueryProgram oracle Result first) :
    (program.castBudget equal).eval answer = program.eval answer := by cases equal; rfl

def raise {oracle : OracleSpec.{0, 0}} {Result : Type} (extra : Nat) :
    {budget : Nat} → QueryProgram oracle Result budget → QueryProgram oracle Result (budget + extra)
  | _, .pure result => .pure result
  | _, .query request next =>
      (QueryProgram.query request (fun answer => raise extra (next answer))).castBudget
        (by omega)

def bind {oracle : OracleSpec.{0, 0}} {First Second : Type} {second : Nat}
    (next : First → QueryProgram oracle Second second) :
    {first : Nat} → QueryProgram oracle First first → QueryProgram oracle Second (first + second)
  | first, .pure result => (raise first (next result)).castBudget (Nat.add_comm _ _)
  | _, .query request rest =>
      (QueryProgram.query request (fun answer => bind next (rest answer))).castBudget
        (by omega)

@[simp] theorem eval_map {oracle : OracleSpec.{0, 0}} {First Second : Type}
    (answer : ∀ q, oracle.Answer q) (f : First → Second) {budget : Nat}
    (program : QueryProgram oracle First budget) :
    (program.map f).eval answer = f (program.eval answer) := by
  induction program with
  | pure result => rfl
  | query request next ih => exact ih (answer request)

@[simp] theorem eval_raise {oracle : OracleSpec.{0, 0}} {Result : Type}
    (answer : ∀ q, oracle.Answer q) (extra : Nat) {budget : Nat}
    (program : QueryProgram oracle Result budget) :
    (program.raise extra).eval answer = program.eval answer := by
  induction program with
  | pure result => rfl
  | query request next ih => simp only [raise, eval_castBudget, eval, ih]

@[simp] theorem eval_bind {oracle : OracleSpec.{0, 0}} {First Second : Type}
    (answer : ∀ q, oracle.Answer q) {first second : Nat}
    (program : QueryProgram oracle First first)
    (next : First → QueryProgram oracle Second second) :
    (program.bind next).eval answer = (next (program.eval answer)).eval answer := by
  induction program with
  | pure result => simp only [bind, eval_castBudget, eval_raise, eval]
  | query request rest ih => simp only [bind, eval_castBudget, eval, ih]

def ofFn {oracle : OracleSpec.{0, 0}} {Result : Type} {budget : Nat} :
    (count : Nat) → (Fin count → QueryProgram oracle Result budget) →
      QueryProgram oracle (Vector Result count) (count * budget)
  | 0, _ => .pure #v[]
  | count + 1, program =>
      ((program 0).bind fun value =>
        (ofFn count (fun index => program index.succ)).map fun values =>
          Vector.ofFn (Fin.cases value values.get)).castBudget (by simp [Nat.add_mul, Nat.add_comm])

@[simp] theorem eval_ofFn {oracle : OracleSpec.{0, 0}} {Result : Type}
    (answer : ∀ q, oracle.Answer q) {budget : Nat} (count : Nat)
    (program : Fin count → QueryProgram oracle Result budget) :
    (ofFn count program).eval answer = Vector.ofFn (fun index => (program index).eval answer) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [ofFn, eval_castBudget, eval_bind, eval_map, ih]
      apply Vector.ext
      intro index valid
      simp only [Vector.getElem_ofFn]
      rcases Fin.eq_zero_or_eq_succ (⟨index, valid⟩ : Fin (count + 1)) with zero | ⟨index, equal⟩
      · rw [zero]; rfl
      · rw [equal]; simp [Vector.get]; rfl

end QueryProgram

/-- An oracle program uses at most the indexed number of queries. -/
inductive OracleProgram (oracle : OracleSpec.{uQuery, uAnswer}) (Result : Type uResult) :
    Nat → Type (max uQuery uAnswer uResult + 1)
  | pure {budget : Nat} (result : PMF Result) : OracleProgram oracle Result budget
  | query {budget : Nat} (request : oracle.Query)
      (next : oracle.Answer request → OracleProgram oracle Result budget) :
      OracleProgram oracle Result (budget + 1)
  | sample {budget : Nat} {Sample : Type uResult} (distribution : PMF Sample)
      (next : Sample → OracleProgram oracle Result budget) :
      OracleProgram oracle Result budget

namespace OracleProgram

universe vQuery vAnswer vResult vState vLift

/-- Each operation requests an oracle answer or an arbitrary private sample. -/
inductive Effect (oracle : OracleSpec.{vQuery, vAnswer}) where
  | query (request : oracle.Query)
  | sample (Sample : Type vResult) (distribution : PMF Sample)

/-- VCV-io uses one common universe for its generic simulation rules. -/
abbrev effectSpec (oracle : OracleSpec.{vQuery, vAnswer}) :
    _root_.OracleSpec (ULift.{max vQuery vAnswer (vResult + 1) vLift} (Effect.{vQuery, vAnswer, vResult} oracle)) :=
  _root_.OracleSpec.ofFn fun request => match request.down with
    | .query request => ULift.{max vQuery vAnswer (vResult + 1) vLift} (oracle.Answer request)
    | .sample Sample _ => ULift.{max vQuery vAnswer (vResult + 1) vLift} Sample

/-- This translation preserves private samples and the indexed query syntax. -/
def toComp {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult} :
    {budget : Nat} → OracleProgram oracle Result budget →
      OracleComp (effectSpec.{vQuery, vAnswer, vResult, vLift} oracle) (ULift.{max vQuery vAnswer (vResult + 1) vLift} Result)
  | _, .pure distribution => OracleComp.queryBind (ULift.up (.sample Result distribution)) Pure.pure
  | _, .query request next => OracleComp.queryBind (ULift.up (.query request)) fun answer => toComp (next answer.down)
  | _, .sample distribution next => OracleComp.queryBind (ULift.up (.sample _ distribution)) fun value => toComp (next value.down)

/-- VCV-io counts public queries and excludes private sampling from the budget. -/
theorem toComp_queryBound {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {budget : Nat} (program : OracleProgram oracle Result budget) :
    OracleComp.IsQueryBoundP (toComp.{vQuery, vAnswer, vResult, vLift} program)
      (fun request => (match request.down with | .query _ => true | .sample _ _ => false) = true) budget := by
  induction program with
  | pure distribution =>
      constructor
      · simp
      · intro value; trivial
  | query request next ih =>
      constructor
      · simp
      · intro answer
        simpa only [OracleComp.IsQueryBoundP, OracleComp.IsQueryBound, PFunctor.FreeM.IsRollBound,
          Bool.true_eq, ↓reduceIte, Nat.add_sub_cancel] using ih answer.down
  | sample distribution next ih =>
      constructor
      · simp
      · intro value
        exact ih value.down

/-- This handler interprets private sampling in the PMF monad. -/
noncomputable def implementation {oracle : OracleSpec.{vQuery, vAnswer}} {State : Type vState}
    (handler : OracleHandler oracle State) :
    QueryImpl (effectSpec.{vQuery, vAnswer, vResult, max vState vLift} oracle) (StateT (ULift.{max vQuery vAnswer (vResult + 1) vLift} State) PMF)
  | ⟨.query request⟩ => fun state => PMF.pure (ULift.up (handler request state.down).1, ULift.up (handler request state.down).2)
  | ⟨.sample _ distribution⟩ => fun state => distribution.map fun value => (ULift.up value, state)

/-- The universe lift permits heterogeneous state projections. -/
noncomputable def execute {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {State : Type vState} (handler : OracleHandler oracle State) {budget : Nat}
    (program : OracleProgram oracle Result budget) (state : State) : PMF (Result × State) :=
  (simulateQ (implementation handler) (toComp.{vQuery, vAnswer, vResult, max vState vLift} program) (ULift.up state)).map fun output => (output.1.down, output.2.down)
@[simp] theorem execute_pure {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {State : Type vState} (handler : OracleHandler oracle State) {budget : Nat}
    (distribution : PMF Result) (state : State) :
    execute.{vQuery, vAnswer, vResult, vState, vLift} handler (.pure (budget := budget) distribution) state =
      distribution.map (fun value => (value, state)) := by
  unfold execute toComp OracleComp.queryBind simulateQ
  simp only [PFunctor.FreeM.liftM]
  simp [implementation, PMF.map_comp, Function.comp_def]

@[simp] theorem execute_query {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {State : Type vState} (handler : OracleHandler oracle State) {budget : Nat}
    (request : oracle.Query) (next : oracle.Answer request → OracleProgram oracle Result budget)
    (state : State) :
    execute.{vQuery, vAnswer, vResult, vState, vLift} handler (.query request next) state =
      execute.{vQuery, vAnswer, vResult, vState, vLift} handler (next (handler request state).1) (handler request state).2 := by
  simp only [execute, toComp, OracleComp.queryBind, simulateQ, PFunctor.FreeM.liftM, implementation]
  change ((PMF.pure (ULift.up (handler request state).1, ULift.up (handler request state).2)).bind
    (fun answer => simulateQ (implementation handler) (next answer.1.down).toComp answer.2)).map
    (fun output => (output.1.down, output.2.down)) = _
  rw [PMF.pure_bind]
  rfl

@[simp] theorem execute_sample {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {State : Type vState} (handler : OracleHandler oracle State) {budget : Nat}
    {Sample : Type vResult} (distribution : PMF Sample)
    (next : Sample → OracleProgram oracle Result budget) (state : State) :
    execute.{vQuery, vAnswer, vResult, vState, vLift} handler (.sample distribution next) state =
      distribution.bind (fun value => execute.{vQuery, vAnswer, vResult, vState, vLift} handler (next value) state) := by
  simp only [execute, toComp, OracleComp.queryBind, simulateQ, PFunctor.FreeM.liftM, implementation]
  change ((distribution.map (fun value => (ULift.up value, ULift.up state))).bind
    (fun answer => simulateQ (implementation handler) (next answer.1.down).toComp answer.2)).map
    (fun output => (output.1.down, output.2.down)) = _
  rw [PMF.bind_map, PMF.map_bind]
  rfl

/-- VCV-io executes the program with one shared oracle state. -/
noncomputable def run {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {State : Type vState} (handler : OracleHandler oracle State) {budget : Nat}
    (program : OracleProgram oracle Result budget) (state : State) : PMF (Result × State) :=
  execute.{vQuery, vAnswer, vResult, vState, 0} handler program state

@[simp] theorem run_pure {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {State : Type vState} (handler : OracleHandler oracle State) {budget : Nat}
    (distribution : PMF Result) (state : State) :
    run handler (.pure (budget := budget) distribution) state =
      distribution.map (fun value => (value, state)) := by
  simp only [run, execute_pure]

@[simp] theorem run_query {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {State : Type vState} (handler : OracleHandler oracle State) {budget : Nat}
    (request : oracle.Query) (next : oracle.Answer request → OracleProgram oracle Result budget)
    (state : State) :
    run handler (.query request next) state =
      run handler (next (handler request state).1) (handler request state).2 := by
  simp only [run, execute_query]

@[simp] theorem run_sample {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {State : Type vState} (handler : OracleHandler oracle State) {budget : Nat}
    {Sample : Type vResult} (distribution : PMF Sample)
    (next : Sample → OracleProgram oracle Result budget) (state : State) :
    run handler (.sample distribution next) state =
      distribution.bind (fun value => run handler (next value) state) := by
  simp only [run, execute_sample]

/-- The universe lift preserves the complete execution distribution. -/
theorem execute_eq_run {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {State : Type vState} (handler : OracleHandler oracle State) {budget : Nat}
    (program : OracleProgram oracle Result budget) (state : State) :
    execute.{vQuery, vAnswer, vResult, vState, vLift} handler program state = run handler program state := by
  induction program generalizing state with
  | pure distribution => simp only [execute_pure, run_pure]
  | query request next ih =>
      simpa only [execute_query, run_query] using ih (handler request state).1 (handler request state).2
  | sample distribution next ih => simp only [execute_sample, run_sample, ih]

/-- This operation changes the result without adding oracle queries. -/
noncomputable def map {oracle : OracleSpec} {First Second : Type} (f : First → Second) :
    {budget : Nat} → OracleProgram oracle First budget → OracleProgram oracle Second budget
  | _, .pure result => .pure (result.map f)
  | _, .query request next => .query request (fun answer => map f (next answer))
  | _, .sample distribution next => .sample distribution (fun value => map f (next value))

/-- This operation adds one unused query to the allowance. -/
def weaken {oracle : OracleSpec} {Result : Type} :
    {budget : Nat} → OracleProgram oracle Result budget → OracleProgram oracle Result (budget + 1)
  | _, .pure result => .pure result
  | _, .query request next => .query request (fun answer => weaken (next answer))
  | _, .sample distribution next => .sample distribution (fun value => weaken (next value))

universe vStateTwo

/-- VCV-io transports a state projection through every query and private sample. -/
theorem run_project {oracle : OracleSpec.{vQuery, vAnswer}} {Result : Type vResult}
    {State : Type vState} {StateTwo : Type vStateTwo}
    (first : OracleHandler oracle State) (second : OracleHandler oracle StateTwo)
    (project : State → StateTwo)
    (agree : ∀ query state, (first query state).1 = (second query (project state)).1 ∧
      project (first query state).2 = (second query (project state)).2)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State) :
    (program.run first state).map (fun output => (output.1, project output.2)) =
      program.run second (project state) := by
  rw [← execute_eq_run.{vQuery, vAnswer, vResult, vState, vStateTwo} first program state,
    ← execute_eq_run.{vQuery, vAnswer, vResult, vStateTwo, vState} second program (project state)]
  have projected := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (implementation.{vQuery, vAnswer, vResult, vState, vStateTwo} first)
    (implementation.{vQuery, vAnswer, vResult, vStateTwo, vState} second)
    (fun value => ULift.up (project value.down)) (by
      rintro ⟨request⟩ initial
      cases request with
      | query query =>
          obtain ⟨answer, next⟩ := agree query initial.down
          simp [implementation, StateT.run, PMF.monad_map_eq_map, PMF.pure_map, answer, next]
      | sample Sample distribution =>
          simp [implementation, StateT.run, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def])
    (toComp program) (ULift.up state)
  have lowered := congrArg (PMF.map (fun output => (output.1.down, output.2.down))) projected
  simpa only [execute, PMF.monad_map_eq_map, StateT.run, PMF.map_comp, Function.comp_def, Prod.map, id] using lowered


end OracleProgram

namespace QueryProgram

noncomputable def toOracleProgram {oracle : OracleSpec.{0, 0}} {Result : Type} :
    {budget : Nat} → QueryProgram oracle Result budget → OracleProgram oracle Result budget
  | _, .pure result => .pure (PMF.pure result)
  | _, .query request next => .query request (fun answer => toOracleProgram (next answer))

theorem run_toOracleProgram {oracle : OracleSpec.{0, 0}} {Result State : Type}
    (answer : ∀ q, oracle.Answer q) {budget : Nat}
    (program : QueryProgram oracle Result budget) (state : State) :
    program.toOracleProgram.run (fun q s => (answer q, s)) state =
      PMF.pure (program.eval answer, state) := by
  induction program with
  | pure result => simp [toOracleProgram, OracleProgram.run_pure, PMF.pure_map, eval]
  | query request next ih => simp only [toOracleProgram, OracleProgram.run_query, eval, ih]

end QueryProgram


abbrev Block := BitVec 128

noncomputable instance : Fintype Block :=
  Fintype.ofEquiv (Fin (2 ^ 128)) BitVec.equivFin.symm.toEquiv

def xor (left right : Block) : Block := left ^^^ right

theorem xorSelfCancel (pad value : Block) : xor pad (xor pad value) = value := by
  rw [xor, xor, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Encryption uses the PRF pad as the paper specifies. -/
def encrypt (pad value : Block) : Block := xor pad value

theorem decryptEncrypt (pad value : Block) :
    encrypt pad (encrypt pad value) = value :=
  xorSelfCancel pad value

/-- A permutation oracle gives one public permutation for each index. -/
structure PermutationOracle (Index : Type uIndex) (Value : Type uBlock) where
  permutation : Index → Equiv Value Value

instance : Nonempty (PermutationOracle Index Value) :=
  ⟨⟨fun _ => Equiv.refl Value⟩⟩

/-- The challenge exposes both permutation directions and the field hash. -/
inductive PublicQuery (FixedIndex EncIndex : Type)
  | fixedForward (index : FixedIndex) (input : Block)
  | fixedInverse (index : FixedIndex) (output : Block)
  | encForward (index : EncIndex) (input : Block)
  | encInverse (index : EncIndex) (output : Block)
  | hash (input : BN254.BaseField)

def PublicQuery.Answer : PublicQuery FixedIndex EncIndex → Type
  | .fixedForward _ _ | .fixedInverse _ _ | .encForward _ _ | .encInverse _ _ => Block
  | .hash _ => Block × Block

abbrev publicOracleSpec (FixedIndex EncIndex : Type) : OracleSpec :=
  ⟨PublicQuery FixedIndex EncIndex, PublicQuery.Answer⟩

abbrev PublicOracle (FixedIndex EncIndex : Type) :=
  PermutationOracle FixedIndex Block × PermutationOracle EncIndex Block ×
    (BN254.BaseField → Block × Block)

/-- Evaluation and adversary queries read the same public tables. -/
def publicAnswer (oracle : PublicOracle FixedIndex EncIndex) :
    (query : PublicQuery FixedIndex EncIndex) → query.Answer
  | .fixedForward index input => oracle.1.permutation index input
  | .fixedInverse index output => (oracle.1.permutation index).symm output
  | .encForward index input => oracle.2.1.permutation index input
  | .encInverse index output => (oracle.2.1.permutation index).symm output
  | .hash input => randomOracleAnswer oracle.2.2 input

def publicHandler (project : Tape → PublicOracle FixedIndex EncIndex) :
    OracleHandler (publicOracleSpec FixedIndex EncIndex) Tape :=
  fun query tape => (publicAnswer (project tape) query, tape)

noncomputable instance [Fintype Index] [Fintype Value] :
    Fintype (PermutationOracle Index Value) := by
  classical
  exact Fintype.ofEquiv (Index → Equiv Value Value) {
    toFun := fun permutation => ⟨permutation⟩
    invFun := PermutationOracle.permutation
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

/-- This tape samples an independent uniform permutation family. -/
noncomputable def uniformPermutationTape
    (Index : Type uIndex) (Value : Type uBlock)
    [Fintype Index] [Fintype Value] [DecidableEq Value] :
    PMF (PermutationOracle Index Value) :=
  PMF.uniformOfFintype (PermutationOracle Index Value)

/-- A random permutation assumption uses the exact uniform tape. -/
structure RandomPermutation
    (Index : Type uIndex) (Value : Type uBlock)
    [Fintype Index] [Fintype Value] [DecidableEq Value] where
  sample : Nat → PMF (PermutationOracle Index Value)
  sampleUniform : ∀ parameter,
    sample parameter = uniformPermutationTape Index Value

/-- This value records one permutation transcript action. -/
inductive PermutationAction
  | forward
  | inverse
  | program
deriving DecidableEq

/-- This value records who added one permutation transcript entry. -/
inductive PermutationOrigin
  | adversary
  | construction
  | simulator
deriving DecidableEq

/-- This value records one permutation pair in the transcript. -/
structure PermutationRecord (Index : Type uIndex) (Value : Type uBlock) where
  action : PermutationAction
  origin : PermutationOrigin
  index : Index
  domain : Value
  range : Value

/-- A fresh pair does not reuse a queried domain or range value. -/
def FreshPermutationPair (history : List (PermutationRecord Index Value))
    (index : Index) (domain range : Value) : Prop :=
  ∀ record ∈ history, record.index = index →
    record.domain ≠ domain ∧ record.range ≠ range

/-- This executable check tests permutation-pair freshness. -/
def freshPermutationPairCheck [DecidableEq Index] [DecidableEq Value]
    (history : List (PermutationRecord Index Value))
    (index : Index) (domain range : Value) : Bool :=
  history.all fun record => decide (record.index ≠ index ∨
    (record.domain ≠ domain ∧ record.range ≠ range))

theorem freshPermutationPairCheck_eq_true [DecidableEq Index] [DecidableEq Value]
    (history : List (PermutationRecord Index Value))
    (index : Index) (domain range : Value) :
    freshPermutationPairCheck history index domain range = true ↔
      FreshPermutationPair history index domain range := by
  constructor
  · intro check record member sameIndex
    have clause := List.all_eq_true.mp check record member
    rcases of_decide_eq_true clause with differentIndex | different
    · exact (differentIndex sameIndex).elim
    · exact different
  · intro fresh
    apply List.all_eq_true.mpr
    intro record member
    apply decide_eq_true
    by_cases sameIndex : record.index = index
    · exact Or.inr (fresh record member sameIndex)
    · exact Or.inl sameIndex

/-- A consistent transcript defines one partial injection per index. -/
def ConsistentPermutationTranscript
    (history : List (PermutationRecord Index Value)) : Prop :=
  ∀ first ∈ history, ∀ second ∈ history, first.index = second.index →
    (first.domain = second.domain ↔ first.range = second.range)

/-- A compatible pair agrees with every prior pair at its index. -/
def CompatiblePermutationPair (history : List (PermutationRecord Index Value))
    (record : PermutationRecord Index Value) : Prop :=
  ∀ prior ∈ history, record.index = prior.index →
    (record.domain = prior.domain ↔ record.range = prior.range)

/-- A compatible pair extends a consistent transcript. -/
theorem consistentPermutationTranscript_cons_of_compatible
    {history : List (PermutationRecord Index Value)}
    {record : PermutationRecord Index Value}
    (consistent : ConsistentPermutationTranscript history)
    (compatible : CompatiblePermutationPair history record) :
    ConsistentPermutationTranscript (record :: history) := by
  intro first firstMember second secondMember sameIndex
  simp only [List.mem_cons] at firstMember secondMember
  rcases firstMember with rfl | firstMember
  · rcases secondMember with rfl | secondMember
    · simp
    · exact compatible second secondMember sameIndex
  · rcases secondMember with rfl | secondMember
    · simpa only [eq_comm] using compatible first firstMember sameIndex.symm
    · exact consistent first firstMember second secondMember sameIndex

/-- A fresh pair extends a consistent transcript. -/
theorem consistentPermutationTranscript_cons
    {history : List (PermutationRecord Index Value)}
    {record : PermutationRecord Index Value}
    (consistent : ConsistentPermutationTranscript history)
    (fresh : FreshPermutationPair history record.index record.domain record.range) :
    ConsistentPermutationTranscript (record :: history) :=
  consistentPermutationTranscript_cons_of_compatible consistent fun prior member sameIndex => by
    have different := fresh prior member sameIndex.symm
    constructor <;> intro equal
    · exact (different.1 equal.symm).elim
    · exact (different.2 equal.symm).elim

/-- An encryption scheme uses a public counter. -/
structure Encryption
    (Key : Type uKey) (Message : Type uMessage) (Cipher : Type uCipher)
    (Counter : Type uCounter) where
  encrypt : Key → Counter → Message → Cipher
  decrypt : Key → Counter → Cipher → Message
  correct : ∀ key counter message,
    decrypt key counter (encrypt key counter message) = message

structure WhiteningKeys where
  first : Block
  second : Block

def encodeBit (bit : Bool) : Block :=
  if bit then 1 else 0

/-- This is the two-key Even--Mansour formula in `claim:hybrid_1_opt`. -/
def evenMansour (permutation : Equiv Block Block) (keys : WhiteningKeys)
    (bit : Bool) : Block :=
  xor (permutation (xor (encodeBit bit) keys.first)) keys.second

/-- CTPRF uses the Davies--Meyer feed-forward formula. -/
def daviesMeyer (permutation : Equiv Block Block) (input : Block) : Block :=
  xor (permutation input) input

end Kriterion.Cryptography
