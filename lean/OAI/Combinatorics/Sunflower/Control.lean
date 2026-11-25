import OAI.Combinatorics.Sunflower.Tensor
import Mathlib.Analysis.Complex.Basic

/-! A local matrix may be chosen by a symbol at the same site. A symbol carried
as a basis index can itself select such a matrix while being retained. -/

open scoped BigOperators Classical
open OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Control

noncomputable section

variable {I : Type*} {C D A B E : I → Type*}

/-- Local matrices indexed by classical controls, with output rows first. -/
abbrev Map (C A B : I → Type*) := ∀ i, C i → B i → A i → ℂ

/-- The coefficient obtained by applying the chosen local matrices. -/
def eval [Fintype I] [∀ i, Fintype (A i)] (M : Map C A B)
    (c : ∀ i, C i) (X : (∀ i, A i) → ℂ) (b : ∀ i, B i) : ℂ :=
  contract (fun i => M i (c i)) X b

/-- Apply a function to each control before reading it. -/
def pre (f : ∀ i, D i → C i) (M : Map C A B) : Map D A B :=
  fun i d => M i (f i d)

@[simp] theorem eval_pre [Fintype I] [∀ i, Fintype (A i)]
    (f : ∀ i, D i → C i) (M : Map C A B) (d : ∀ i, D i)
    (X : (∀ i, A i) → ℂ) (b : ∀ i, B i) :
    eval (pre f M) d X b = eval M (fun i => f i (d i)) X b := rfl

/-- The identity acts on every branch of the external control. -/
def idMap {C A : I → Type*} : Map C A A :=
  fun _ _ b a => if a = b then 1 else 0

@[simp] theorem eval_idMap [Fintype I] [∀ i, Fintype (A i)]
    (c : ∀ i, C i) (X : (∀ i, A i) → ℂ) (b : ∀ i, A i) :
    eval idMap c X b = X b := by
  simp [eval, contract, idMap, Fintype.prod_boole, ← funext_iff, mul_ite]

/-- Only the selected rows influence an output coefficient. -/
theorem eval_congr_at [Fintype I] [∀ i, Fintype (A i)]
    {M : Map C A B} {N : Map D A B} {c : ∀ i, C i} {d : ∀ i, D i}
    (X : (∀ i, A i) → ℂ) {b : ∀ i, B i}
    (h : ∀ i a, M i (c i) (b i) a = N i (d i) (b i) a) :
    eval M c X b = eval N d X b := by
  simp only [eval, contract, h]

/-- The output control index selects a block. Within each block the auxiliary
matrix can use both the external control and the retained basis label. -/
def retainMap (M : Map (fun i => D i × C i) A B) :
    Map D (fun i => C i × A i) (fun i => C i × B i) :=
  fun i d y x => if x.1 = y.1 then M i (d, y.1) y.2 x.2 else 0

/-- A block diagonal matrix acts on each slice with precisely its own controls.
The input tensor may correlate the retained labels with the auxiliary indices. -/
theorem eval_retainMap [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (C i)]
    (M : Map (fun i => D i × C i) A B) (d : ∀ i, D i)
    (X : (∀ i, C i × A i) → ℂ) (y : ∀ i, C i × B i) :
    eval (retainMap M) d X y =
      eval M (fun i => (d i, (y i).1))
        (fun a => X (fun i => ((y i).1, a i))) (fun i => (y i).2) := by
  classical
  change (∑ x, X x * ∏ i, (if (x i).1 = (y i).1 then M i (d i, (y i).1) (y i).2 (x i).2 else 0)) = _
  let e := Equiv.arrowProdEquivProdArrow I C A
  calc
    _ = ∑ p : (∀ i, C i) × (∀ i, A i),
        X (fun i => (p.1 i,p.2 i)) *
          ∏ i, (if p.1 i = (y i).1 then M i (d i,(y i).1) (y i).2 (p.2 i) else 0) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp_rw [Fintype.prod_ite_zero, ← funext_iff, mul_ite, mul_zero]
      simp [eval, contract]

/-- Tensoring independent factors with the same controls. -/
def prodMap {A' B' : I → Type*} (M : Map C A B) (N : Map C A' B') :
    Map C (fun i => A i × A' i) (fun i => B i × B' i) :=
  fun i c y x => M i c y.1 x.1 * N i c y.2 x.2

theorem eval_prodMap [Fintype I] {A' B' : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)]
    (M : Map C A B) (N : Map C A' B') (c : ∀ i, C i)
    (X : (∀ i, A i) → ℂ) (Y : (∀ i, A' i) → ℂ) (b : ∀ i, B i × B' i) :
    eval (prodMap M N) c (fun a => X (fun i => (a i).1) * Y (fun i => (a i).2)) b =
      eval M c X (fun i => (b i).1) * eval N c Y (fun i => (b i).2) :=
  contract_mul (fun i => M i (c i)) (fun i => N i (c i)) X Y b

/-- Compose two local maps chosen by the same external control. -/
def compMap [∀ i, Fintype (B i)] (N : Map C B E) (M : Map C A B) : Map C A E :=
  fun i c e a => ∑ b, M i c b a * N i c e b

theorem eval_compMap [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (N : Map C B E) (M : Map C A B) (c : ∀ i, C i) (X : (∀ i, A i) → ℂ) (e : ∀ i, E i) :
    eval (compMap N M) c X e = eval N c (eval M c X) e :=
  congrFun (contract_comp (fun i => N i (c i)) (fun i => M i (c i)) X).symm e

/-- Local assembly of two block maps into a common output format. -/
def sumMap {A' : I → Type*} (M : Map C A B) (N : Map C A' B) :
    Map C (fun i => A i ⊕ A' i) B :=
  fun i c b => Sum.elim (M i c b) (N i c b)

theorem eval_sumMap [Fintype I] {A' : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)]
    (M : Map C A B) (N : Map C A' B) (c : ∀ i, C i)
    (X : (∀ i, A i) → ℂ) (Y : (∀ i, A' i) → ℂ) (b : ∀ i, B i) :
    eval (sumMap M N) c (sumCoeff X Y) b = eval M c X b + eval N c Y b :=
  congrFun (contract_addBlocks (fun i => M i (c i)) (fun i => N i (c i)) X Y) b

/-- The distinguished site's sign changes the second summand to its negative. -/
def diffMap {A' : I → Type*} (j : I) (M : Map C A B) (N : Map C A' B) :
    Map C (fun i => A i ⊕ A' i) B :=
  fun i c b => Sum.elim (M i c b) (fun a => (if i = j then -1 else 1) * N i c b a)

theorem eval_diffMap [Fintype I] {A' : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)]
    (j : I) (M : Map C A B) (N : Map C A' B) (c : ∀ i, C i)
    (X : (∀ i, A i) → ℂ) (Y : (∀ i, A' i) → ℂ) (b : ∀ i, B i) :
    eval (diffMap j M N) c (sumCoeff X Y) b = eval M c X b - eval N c Y b :=
  contract_subBlocks j (fun i => M i (c i)) (fun i => N i (c i)) X Y b

/-- Fixed controls give an ordinary restriction of the input tensor. -/
theorem restricts_eval [Fintype I] {R Q : Raw I ℂ} (M : Map C R.Leg Q.Leg)
    (c : ∀ i, C i) (h : ∀ b, eval M c R.coeff b = Q.coeff b) : Q.Restricts R :=
  ⟨fun i => M i (c i), fun b => (h b).symm⟩

end
end Control
end Sunflower
end Combinatorics
end OAI
