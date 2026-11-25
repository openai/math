import OAI.LinearAlgebra.MatrixExponent.Diagonal.Physical

/-!
# Reconnecting processor inputs

Copies at the same input position have the same label. Consequently
all occurrences of a broadcast or physical bit are colocated at a
single worker. Only literal bits may require additional communication.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

abbrev Pin (N l b r : ℕ) := (Fin (3 * r) × Fin l) ⊕ Fin b ⊕ Links.Slot (3 * r) N

namespace Pin

variable {N l b r : ℕ}

def position : Pin N l b r → Fin l ⊕ Fin b ⊕ Fin (N / 4)
  | .inl (_, i) => .inl i
  | .inr (.inl i) => .inr (.inl i)
  | .inr (.inr i) => .inr (.inr (Links.address i))

def literal (y : Pin N l b r → Bool) (u : Fin (3 * r)) (i : Fin l) := y (.inl (u, i))

def broadcast (y : Pin N l b r → Bool) (i : Fin b) := y (.inr (.inl i))

def link (y : Pin N l b r → Bool) (i : Links.Slot (3 * r) N) := y (.inr (.inr i))

variable (f : Fin l ⊕ Fin b ⊕ Fin (N / 4) → Worker r)

def dst (e : Pin N l b r) : Worker r := f e.position

def src (e : Pin N l b r) : Worker r :=
  match e with
  | .inl (u, _) => (Worker.index r).symm u
  | .inr _ => dst f e

end Pin
end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-! # Summing over copies of the literal bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Pin

open Finset
variable {F : Type} [Field F] {N l b r : ℕ}

/-- Each worker imposes only its own literal, without knowing the
program or wiring information provided to any other processor. -/
def mask (F : Type) [Field F] (u : Worker r) (s : Fin l → Bool) (y : Pin N l b r → Bool) : F :=
  if literal y (Worker.index r u) = s then 1 else 0

theorem mask_local (u : Worker r) (s : Fin l → Bool) (y z : Pin N l b r → Bool)
    (f : Fin l ⊕ Fin b ⊕ Fin (N / 4) → Worker r) (he : ∀ e, src f e = u → y e = z e) :
    mask F u s y = mask F u s z := by
  have h : literal y (Worker.index r u) = literal z (Worker.index r u) :=
    funext (fun i => he (.inl (Worker.index r u, i)) ((Worker.index r).symm_apply_apply u))
  rw [mask, mask, h]

private theorem masks (ξ : Fin (3 * r) → Fin l → Bool) (y : Pin N l b r → Bool) :
    (∏ u, mask F u (ξ (Worker.index r u)) y) = if literal y = ξ then 1 else 0 := by
  by_cases h : literal y = ξ
  · simp [mask, h]
  · rw [ite_eq_right h]
    obtain ⟨u, hu⟩ := Function.ne_iff.mp h
    refine prod_eq_zero (mem_univ ((Worker.index r).symm u)) ?_
    simp [mask, hu]

private def coordinates (N l b r : ℕ) :
    (Pin N l b r → Bool) ≃ (Fin (3 * r) → Fin l → Bool) × (Fin b → Bool) × (Links.Slot (3 * r) N → Bool) :=
  (Equiv.sumPiEquivProdPi (fun _ => Bool)).trans
    ((Equiv.curry _ _ _).prodCongr (Equiv.sumPiEquivProdPi (fun _ => Bool)))

theorem sum_masks (ξ : Fin (3 * r) → Fin l → Bool)
    (g : (Fin (3 * r) → Fin l → Bool) → (Fin b → Bool) → (Links.Slot (3 * r) N → Bool) → F) :
    (∑ y : Pin N l b r → Bool, (∏ u, mask F u (ξ (Worker.index r u)) y) *
      g (literal y) (broadcast y) (link y)) = ∑ z, ∑ t, g ξ z t := by
  simp only [masks]
  rw [← (coordinates N l b r).symm.sum_comp, Fintype.sum_prod_type]
  change (∑ a, ∑ x : (Fin b → Bool) × (Links.Slot (3 * r) N → Bool),
    (if a = ξ then (1 : F) else 0) * g a x.1 x.2) = _
  rw [sum_comm]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  rw [Fintype.sum_prod_type]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Pin
end
