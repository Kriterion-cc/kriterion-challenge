import Mathlib.Data.Vector.Basic
import Mathlib.Tactic

namespace Kriterion

/-- An encoding preserves its value and the remaining bytes. -/
structure Encoding (α : Type) where
  encode : α → List (Fin 256)
  decode : List (Fin 256) → Option (α × List (Fin 256))
  decode_encode : ∀ value tail, decode (encode value ++ tail) = some (value, tail)

namespace Encoding

def map (encoding : Encoding α) (encode : β → α) (decode : α → β)
    (inverse : ∀ value, decode (encode value) = value) : Encoding β where
  encode value := encoding.encode (encode value)
  decode bytes := (encoding.decode bytes).map fun result => (decode result.1, result.2)
  decode_encode value tail := by simp [encoding.decode_encode, inverse]

def pair (first : Encoding α) (second : Encoding β) : Encoding (α × β) where
  encode value := first.encode value.1 ++ second.encode value.2
  decode bytes := do
    let left ← first.decode bytes
    let right ← second.decode left.2
    return ((left.1, right.1), right.2)
  decode_encode value tail := by
    simp [List.append_assoc, first.decode_encode, second.decode_encode]

def byte : Encoding (Fin 256) where
  encode value := [value]
  decode bytes := match bytes with
    | [] => none
    | value :: tail => some (value, tail)
  decode_encode _ _ := rfl

def option (encoding : Encoding α) : Encoding (Option α) where
  encode value := match value with
    | none => [0]
    | some value => 1 :: encoding.encode value
  decode bytes := match bytes with
    | [] => none
    | tag :: tail =>
      if tag = 0 then some (none, tail)
      else if tag = 1 then (encoding.decode tail).map fun result => (some result.1, result.2)
      else none
  decode_encode value tail := by
    cases value <;> simp [encoding.decode_encode]

def vector (encoding : Encoding α) : (count : Nat) → Encoding (Vector α count)
  | 0 => {
      encode := fun _ => []
      decode := fun bytes => some (#v[], bytes)
      decode_encode := fun value _ => by simp }
  | count + 1 =>
      (pair (vector encoding count) encoding).map
        (fun value => (value.pop, value.back))
        (fun value => value.1.push value.2)
        (fun value => Vector.push_pop_back value)

def natural : (width : Nat) → Encoding (Fin (256 ^ width))
  | 0 => {
      encode := fun _ => []
      decode := fun bytes => some (0, bytes)
      decode_encode := fun value _ => by
        have equal : value = 0 := by apply Fin.ext; have := value.isLt; simpa only [pow_zero, Nat.lt_one_iff, Fin.val_zero] using this
        simp [equal] }
  | width + 1 =>
      (pair byte (natural width)).map
        (fun value => (⟨value.val % 256, Nat.mod_lt _ (by decide)⟩,
          ⟨value.val / 256, by have := value.isLt; simp only [pow_succ] at this; omega⟩))
        (fun value => ⟨value.1.val + 256 * value.2.val, by
          have := value.1.isLt
          have := value.2.isLt
          rw [pow_succ]
          omega⟩)
        (fun value => by apply Fin.ext; exact Nat.mod_add_div _ _)

@[simp] theorem natural_length (width : Nat) (value : Fin (256 ^ width)) :
    ((natural width).encode value).length = width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [natural, map, pair, byte, ih]

theorem vector_length (encoding : Encoding α) (size : Nat)
    (count : Nat) (value : Vector α count)
    (fixed : ∀ index : Fin count, (encoding.encode (value.get index)).length = size) :
    ((vector encoding count).encode value).length = count * size := by
  induction count with
  | zero => simp [vector]
  | succ count ih =>
      simp only [vector, map, pair, List.length_append]
      rw [ih value.pop (fun index => by simpa [Vector.get, Fin.cast] using fixed index.castSucc)]
      have last := fixed (Fin.last count)
      simpa [Nat.add_mul, Vector.back, Vector.get, Fin.last] using congrArg (count * size + ·) last

end Encoding
end Kriterion
