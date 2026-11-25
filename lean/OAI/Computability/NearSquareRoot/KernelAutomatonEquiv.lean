import OAI.Computability.NearSquareRoot.KernelAutomatonSearch
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Finite tests for rational column transfer matrices

Each address column gives one letter. The same fixed matrices apply at
every width. Vanishing on all words shorter than the state dimension
certifies vanishing on every word, including the empty word. Comparing two
such computations uses the sum of their state dimensions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelAutomatonEquiv

open Matrix
open scoped Matrix

section Reachable

variable {γ V : Type*} [AddCommGroup V] [Module ℚ V]

private def walk (step : γ → Module.End ℚ V) (v : V) : List γ → V
  | [] => v
  | a :: w => step a (walk step v w)

private def reach (step : γ → Module.End ℚ V) (v : V) (n : ℕ) : Submodule ℚ V :=
  Submodule.span ℚ {x | ∃ w : List γ, w.length < n ∧ walk step v w = x}

private theorem reach_mono (step : γ → Module.End ℚ V) (v : V) :
    Monotone (reach step v) := by
  intro i j hij
  apply Submodule.span_mono
  rintro x ⟨w,hw,rfl⟩
  exact ⟨w,lt_of_lt_of_le hw hij,rfl⟩

private theorem step_reach (step : γ → Module.End ℚ V) (v : V) (n : ℕ) (a : γ) :
    (reach step v n).map (step a) ≤ reach step v (n+1) := by
  apply (Submodule.map_span_le _ _ _).mpr
  rintro x ⟨w,hw,rfl⟩
  exact Submodule.subset_span ⟨a::w, by simpa using hw, rfl⟩

private theorem walk_mem_stable (step : γ → Module.End ℚ V) (v : V) {n : ℕ}
    (h : reach step v n = reach step v (n+1)) (w : List γ) :
    walk step v w ∈ reach step v n := by
  induction w with
  | nil =>
    rw [h]
    exact Submodule.subset_span ⟨[], Nat.zero_lt_succ _, rfl⟩
  | cons a w ih =>
    rw [h]
    exact step_reach step v n a ⟨_,ih,rfl⟩

private theorem stable_by_dimension [FiniteDimensional ℚ V]
    (step : γ → Module.End ℚ V) (v : V) :
    ∃ n ≤ Module.finrank ℚ V, reach step v n = reach step v (n+1) := by
  by_contra! h
  let d := Module.finrank ℚ V
  have grow (n : ℕ) (hn : n ≤ d) :
      Module.finrank ℚ (reach step v n) < Module.finrank ℚ (reach step v (n+1)) :=
    Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne (reach_mono step v (Nat.le_succ n)) (h n hn))
  have lower (n : ℕ) (hn : n ≤ d+1) : n ≤ Module.finrank ℚ (reach step v n) := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      apply (ih (by omega)).trans_lt
      exact grow n (by omega)
  exact Nat.not_succ_le_self d ((lower (d+1) le_rfl).trans (Submodule.finrank_le _))

private theorem vanish_iff [FiniteDimensional ℚ V] (step : γ → Module.End ℚ V)
    (v : V) (observe : V →ₗ[ℚ] ℚ) :
    (∀ w, observe (walk step v w) = 0) ↔
      ∀ w : List γ, w.length < Module.finrank ℚ V → observe (walk step v w) = 0 := by
  refine ⟨fun h w _ => h w, fun h w => ?_⟩
  obtain ⟨n, hn, stable⟩ := stable_by_dimension step v
  have sub : reach step v n ≤ LinearMap.ker observe :=
    Submodule.span_le.mpr (by
      rintro x ⟨u,hu,rfl⟩
      exact h u (hu.trans_le hn))
  exact sub (walk_mem_stable step v stable w)

end Reachable

/-- Weight of a list of columns in a rational matrix representation. -/
def weight {γ : Type*} {d : ℕ} (initial : Fin d → ℚ)
    (letter : γ → Matrix (Fin d) (Fin d) ℚ) (final : Fin d → ℚ) (w : List γ) : ℚ :=
  initial ⬝ᵥ ((w.map letter).prod *ᵥ final)

private theorem walk_matrix {γ : Type*} {d : ℕ}
    (L : γ → Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) (w : List γ) :
    walk (fun a => (L a).mulVecLin) v w = (w.map L).prod *ᵥ v := by
  induction w with
  | nil => simp [walk]
  | cons a w ih =>
    simp [walk, ih, Matrix.mulVec_mulVec]

/-- It suffices to test words of length strictly less than the state dimension.
In dimension zero the empty collection of tests suffices. -/
theorem zero_iff_short {γ : Type*} {d : ℕ} (initial : Fin d → ℚ)
    (letter : γ → Matrix (Fin d) (Fin d) ℚ) (final : Fin d → ℚ) :
    (∀ w, weight initial letter final w = 0) ↔
      ∀ w : List γ, w.length < d → weight initial letter final w = 0 := by
  simpa only [walk_matrix, weight, dotProductBilin_apply_apply,
    Module.finrank_pi, Fintype.card_fin] using
    vanish_iff (fun a => (letter a).mulVecLin) final
      (dotProductBilin ℚ ℚ initial)

/-- Two matrix representations with possibly different state dimensions
agree at every width if they agree below their combined dimension. -/
theorem equal_iff_short {γ : Type*} {d e : ℕ}
    (u₁ : Fin d → ℚ) (L₁ : γ → Matrix (Fin d) (Fin d) ℚ) (v₁ : Fin d → ℚ)
    (u₂ : Fin e → ℚ) (L₂ : γ → Matrix (Fin e) (Fin e) ℚ) (v₂ : Fin e → ℚ) :
    (∀ w, weight u₁ L₁ v₁ w = weight u₂ L₂ v₂ w) ↔
      ∀ w : List γ, w.length < d + e → weight u₁ L₁ v₁ w = weight u₂ L₂ v₂ w := by
  let step (a : γ) := ((L₁ a).mulVecLin).prodMap (L₂ a).mulVecLin
  let observe : ((Fin d → ℚ) × (Fin e → ℚ)) →ₗ[ℚ] ℚ :=
    (dotProductBilin ℚ ℚ u₁).comp (LinearMap.fst ..) -
    (dotProductBilin ℚ ℚ u₂).comp (LinearMap.snd ..)
  have paired (w : List γ) :
      walk step (v₁,v₂) w =
        (walk (fun a => (L₁ a).mulVecLin) v₁ w, walk (fun a => (L₂ a).mulVecLin) v₂ w) := by
    induction w with
    | nil => rfl
    | cons a w ih => simp [walk, ih, step]
  simpa only [paired, walk_matrix, observe, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, dotProductBilin_apply_apply,
    sub_eq_zero, weight, Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] using
    vanish_iff step (v₁,v₂) observe

/-- A total boolean test for equality at every width, using only rational
arithmetic and bounded enumeration over the supplied finite alphabet. -/
def equivalent {γ : Type*} [Fintype γ] {d e : ℕ}
    (u₁ : Fin d → ℚ) (L₁ : γ → Matrix (Fin d) (Fin d) ℚ) (v₁ : Fin d → ℚ)
    (u₂ : Fin e → ℚ) (L₂ : γ → Matrix (Fin e) (Fin e) ℚ) (v₂ : Fin e → ℚ) : Bool :=
  equalBelow (d+e) (weight u₁ L₁ v₁) (weight u₂ L₂ v₂)

theorem equivalent_iff {γ : Type*} [Fintype γ] {d e : ℕ}
    (u₁ : Fin d → ℚ) (L₁ : γ → Matrix (Fin d) (Fin d) ℚ) (v₁ : Fin d → ℚ)
    (u₂ : Fin e → ℚ) (L₂ : γ → Matrix (Fin e) (Fin e) ℚ) (v₂ : Fin e → ℚ) :
    equivalent u₁ L₁ v₁ u₂ L₂ v₂ = true ↔
      ∀ w, weight u₁ L₁ v₁ w = weight u₂ L₂ v₂ w :=
  (equalBelow_iff ..).trans (equal_iff_short ..).symm

end KernelAutomatonEquiv

end NearSquareRoot
end Computability
end OAI
