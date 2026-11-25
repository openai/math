import OAI.Computability.NearSquareRoot.KernelPassMonomial

/-! # Lowering signs and partial transforms of a single binary column

These constructors produce programs for arbitrary sign tables, partial Walsh
transforms in any binary basis, and their compositions. Signs and changes of
basis use zero child calls. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open Matrix Finset SynchronizedPadding SynchronizedPair KernelNormalization

variable {A : ℕ}

def letterAt (c : Column A) (j : Fin 2) : Bits A := fun a => c a j

def signPass (φ : Bits A → ZMod 2) : Plan A 1 1 :=
  .scale 1 (fun c _ => φ (letterAt c 0) + φ (letterAt c 1))
    (fun s => if s 0 = 0 then (1,0) else (-1,0))

private theorem character_if (z : ZMod 2) :
    character z = (if z = 0 then (1 : ℂ) else -1) := by
  fin_cases z
  · rfl
  · change (-1 : ℂ)^1 = if (1 : ZMod 2) = 0 then 1 else -1
    norm_num

theorem implements_sign (φ : Bits A → ZMod 2) :
    Implements (signPass φ) (diagonal fun v => character (φ v)) := by
  intro h
  ext y x
  let chi (x : Addr A h) := ∑ c, (φ (letterAt (x c) 0) + φ (letterAt (x c) 1))
  have eval : oneRow ((signPass φ).eval h) y x =
      if x = y then (if chi x = 0 then (1 : ℚ) else -1) else 0 := by
    change (if x = y then value (if (∑ c, fun _ : Fin 1 =>
      φ (letterAt (x c) 0) + φ (letterAt (x c) 1)) 0 = 0 then (1,0) else (-1,0)) else 0) = _
    simp only [Finset.sum_apply, chi]
    split_ifs <;> norm_num [value]
  rw [Matrix.map_apply,eval, lift, tensorMatrix_diagonal]
  by_cases e : x = y
  · subst y
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply_eq, ↓reduceIte]
    have E : (∑ t : Fin h × Fin 2, φ ((expose h) x t)) = chi x := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two]
      rfl
    change _ = ∏ t : Fin h × Fin 2, OAI.LinearAlgebra.FiniteFourier.digitPhase binaryRoot (φ ((expose h) x t))
    rw [← OAI.LinearAlgebra.FiniteFourier.digitPhase_sum, E]
    change _ = character (chi x)
    rw [character_if]
    split <;> norm_num
  · have hn : (expose h) y ≠ (expose h) x := fun t => e (Equiv.injective _ t.symm)
    simp [e, hn]

noncomputable def childLocal (a : Fin A) : Local A := fun y x =>
  if ∀ b ≠ a, x b = y b then walsh (y a) (x a) else 0

private theorem child_entry (a : Fin A) (y x : Column A) :
    (childEntry a y x : ℂ) = ∏ t, childLocal a (letterAt y t) (letterAt x t) := by
  rw [Fin.prod_univ_two]
  let P (t : Fin 2) := ∀ b ≠ a, letterAt x t b = letterAt y t b
  have iff : (∀ b ≠ a, x b = y b) ↔ P 0 ∧ P 1 := by
    constructor
    · intro hs
      exact ⟨fun b h => congrFun (hs b h) 0, fun b h => congrFun (hs b h) 1⟩
    · intro ⟨h₀,h₁⟩ b hb
      funext t
      fin_cases t
      · exact h₀ b hb
      · exact h₁ b hb
  change (childEntry a y x : ℂ) =
    (if P 0 then walsh _ _ else 0) * (if P 1 then walsh _ _ else 0)
  unfold childEntry
  simp only [iff]
  by_cases h₀ : P 0 <;> by_cases h₁ : P 1 <;> simp [h₀,h₁]
  rw [pairEntry_complex]
  simp [axis, Fin.prod_univ_two, letterAt]

theorem implements_child (a : Fin A) : Implements (Plan.child a) (childLocal a) := by
  intro h
  ext y x
  change (algebraMap ℚ ℂ) (∏ c, childEntry a (y c) (x c)) =
    ∏ t : Fin h × Fin 2, childLocal a ((expose h) y t) ((expose h) x t)
  rw [map_prod, Fintype.prod_prod_type]
  exact prod_congr rfl (fun c _ => child_entry a (y c) (x c))

noncomputable def partialLocal (s : List (Fin A)) : Local A := (s.map childLocal).prod

theorem implements_partial (s : List (Fin A)) :
    Implements (fullConversion s) (partialLocal s) := by
  induction s with
  | nil => exact implements_identity
  | cons a s ih => exact (implements_child a).seq ih

/-- One column transform with a prescribed child-call budget. -/
def Realizes (budget : ℕ) (M : Local A) : Prop :=
  ∃ p : Plan A 1 1, p.calls ≤ budget ∧ Implements p M

theorem Realizes.mul {s t : ℕ} {M N : Local A} (hM : Realizes s M)
    (hN : Realizes t N) : Realizes (s+t) (M*N) := by
  obtain ⟨p,hp,ep⟩ := hM
  obtain ⟨q,hq,eq⟩ := hN
  exact ⟨p.seq q, Nat.add_le_add hp hq, ep.seq eq⟩

theorem Realizes.sign (φ : Bits A → ZMod 2) :
    Realizes 0 (diagonal fun x => character (φ x)) :=
  ⟨signPass _, le_rfl, implements_sign _⟩

theorem Realizes.permutation (e : Bits A ≃ₗ[ZMod 2] Bits A) :
    Realizes 0 (pushAddress e) := by
  obtain ⟨p,h,e⟩ := reindex_linear e
  exact ⟨p,h.le,e⟩

theorem Realizes.partial (s : List (Fin A)) : Realizes s.length (partialLocal s) :=
  ⟨fullConversion s, (calls_fullConversion s).le, implements_partial s⟩

end KernelPass

end NearSquareRoot
end Computability
end OAI
