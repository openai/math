import OAI.LinearAlgebra.MatrixExponent.Diagram.Wide
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute

/-! # Indexing independent copies of a bit bundle -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

private def nextPort {α β : Type} {d : ℕ} (e : β ≃ Fin d × α) :
    α ⊕ β ≃ Fin (d + 1) × α where
  toFun := Sum.elim (fun i => (0, i)) (fun j => ((e j).1.succ, (e j).2))
  invFun := fun p => Fin.cases (.inl p.2) (fun i => .inr (e.symm (i, p.2))) p.1
  left_inv := by rintro (i | j) <;> simp
  right_inv := by
    rintro ⟨j, i⟩
    induction j using Fin.cases <;> simp

/-- The first copy has index zero. Positions inside each copy are unchanged. -/
def port (a : Wire) : (d : ℕ) → slots (copies a d) ≃ Fin d × slots a
  | 0 => (Equiv.equivEmpty _).symm
  | d + 1 => nextPort (port a d)

def bundle (a : Wire) : (d : ℕ) → (Fin d → Val a) → Val (copies a d)
  | 0, _ => ()
  | d + 1, x => (x 0, bundle a d (fun i => x i.succ))

theorem bits_bundle (a : Wire) (d : ℕ) (x : Fin d → Val a) (i : slots (copies a d)) :
    bits (copies a d) (bundle a d x) i = bits a (x (port a d i).1) (port a d i).2 := by
  induction d with
  | zero => exact i.elim
  | succ d ih =>
    cases i with
    | inl i => rfl
    | inr i => exact ih (fun j => x j.succ) i

theorem power_bundle {F : Type} [Field F] {a b : Wire} (k : Val a → Val b → F)
    (d : ℕ) (x : Fin d → Val a) (y : Fin d → Val b) :
    power k d (bundle a d x) (bundle b d y) = ∏ i, k (x i) (y i) := by
  induction d with
  | zero => simp [power]
  | succ d ih => rw [Fin.prod_univ_succ, bundle, bundle, power, ih]

end OAI.LinearAlgebra.MatrixExponent.Diagonal
