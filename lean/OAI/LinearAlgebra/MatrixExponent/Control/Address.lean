import OAI.LinearAlgebra.MatrixExponent.Lookup.Counter
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute

/-! # Little-endian binary addresses -/

namespace OAI.LinearAlgebra.MatrixExponent.Control

theorem value_lt (h : ℕ) (x : Val (word h)) : Lookup.value h x < 2 ^ h := by
  induction h with
  | zero => simp [Lookup.value]
  | succ h ih =>
    obtain ⟨b, y⟩ := x
    have := ih y
    cases b <;> simp [Lookup.value, pow_succ] <;> omega

theorem value_injective (h : ℕ) : Function.Injective (Lookup.value h) := by
  induction h with
  | zero => exact fun _ _ _ => rfl
  | succ h ih =>
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    cases i <;> cases j <;> simp [Lookup.value] at he <;> first | omega | exact Prod.ext rfl (ih he)

def index (w : ℕ) : Val (word w) ≃ Fin (2 ^ w) where
  toFun k := ⟨Lookup.value w k, value_lt w k⟩
  invFun k := Lookup.bits w k
  left_inv k := value_injective w (Lookup.value_bits (value_lt w k))
  right_inv k := Fin.ext (Lookup.value_bits k.isLt)

def decode (w : ℕ) : (slots (word w) → Bool) ≃ Fin (2 ^ w) :=
  (bits (word w)).symm.trans (index w)

def read (w : ℕ) (x : Fin (2 ^ w) ⊕ (Fin (2 ^ w) × slots (word w)) → Bool) (i : Fin (2 ^ w)) : Bool :=
  x (.inl (decode w (fun j => x (.inr (i, j)))))

end OAI.LinearAlgebra.MatrixExponent.Control
