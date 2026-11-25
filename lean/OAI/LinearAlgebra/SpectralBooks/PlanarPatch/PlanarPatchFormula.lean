import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPruneAlgebra
import Mathlib.Tactic

/-! # Formula sizes for contractions in a tree patch

The weight of a division-free expression is its number of arithmetic gates plus one.
Weights add under binary gates. This gives one bound for all the contractions
that eliminate scalar branches and absorb matrices at adjacent vertices.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace PlanarPatch

open Arithmetic MvPolynomial

variable {F I : Type*} [Field F]

/-- The polynomial is represented formally by a formula of the indicated weight. -/
def HasFormula (n : ℕ) (p : MvPolynomial I F) : Prop :=
  ∃ e : Expression F I, expressionPolynomial e = p ∧ e.cost + 1 ≤ n

namespace HasFormula

theorem mono {a b : ℕ} {p : MvPolynomial I F} (hp : HasFormula a p) (h : a ≤ b) :
    HasFormula b p := by
  obtain ⟨e, he, hc⟩ := hp
  exact ⟨e, he, hc.trans h⟩

theorem const (c : F) : HasFormula 1 (C c : MvPolynomial I F) :=
  ⟨.constant c, rfl, le_rfl⟩

theorem input (i : I) : HasFormula 1 (X i : MvPolynomial I F) :=
  ⟨.input i, rfl, le_rfl⟩

theorem add {a b : ℕ} {p r : MvPolynomial I F} (hp : HasFormula a p) (hr : HasFormula b r) :
    HasFormula (a + b) (p + r) := by
  obtain ⟨e, rfl, hc⟩ := hp
  obtain ⟨f, rfl, hd⟩ := hr
  exact ⟨.add e f, rfl, by simp only [Expression.cost]; omega⟩

theorem mul {a b : ℕ} {p r : MvPolynomial I F} (hp : HasFormula a p) (hr : HasFormula b r) :
    HasFormula (a + b) (p * r) := by
  obtain ⟨e, rfl, hc⟩ := hp
  obtain ⟨f, rfl, hd⟩ := hr
  exact ⟨.mul e f, rfl, by simp only [Expression.cost]; omega⟩

theorem finSum {n W : ℕ} {p : Fin n → MvPolynomial I F} (hW : 1 ≤ W)
    (hp : ∀ a, HasFormula W (p a)) : HasFormula ((n + 1) * W) (∑ a, p a) := by
  induction n with
  | zero =>
    simpa using (const (I := I) (0 : F)).mono hW
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact ((hp 0).add (ih (fun a ↦ hp a.succ))).mono (by rw [Nat.succ_mul (n + 1) W, Nat.add_comm])

end HasFormula

variable {C D q i j k l p : ℕ}

private theorem oneSum {n : ℕ} {f : Fin n → MvPolynomial I F} (hC : 1 ≤ C) (hn : n ≤ D)
    (hf : ∀ a, HasFormula (4 * C) (f a)) :
    HasFormula (4 * (D + 1)^2 * C) (∑ a, f a) := by
  apply (HasFormula.finSum (by omega) hf).mono
  calc
    (n + 1) * (4 * C) ≤ (D + 1) * (4 * C) := by gcongr
    _ ≤ (D + 1) * (4 * C) * (D + 1) := Nat.le_mul_of_pos_right _ (by omega)
    _ = _ := by ring

private theorem twoSum {n m : ℕ} {f : Fin n → Fin m → MvPolynomial I F}
    (hC : 1 ≤ C) (hn : n ≤ D) (hm : m ≤ D) (hf : ∀ a b, HasFormula (4 * C) (f a b)) :
    HasFormula (4 * (D + 1)^2 * C) (∑ a, ∑ b, f a b) := by
  have hp : 0 < (m + 1) * (4 * C) := Nat.mul_pos (by omega) (by omega)
  apply (HasFormula.finSum hp fun a ↦ HasFormula.finSum (by omega) (hf a)).mono
  calc
    (n + 1) * ((m + 1) * (4 * C)) ≤ (D + 1) * ((D + 1) * (4 * C)) := by gcongr
    _ = _ := by ring

theorem hasFormula_linId (q : ℕ) (o a : Fin q) :
    HasFormula 1 (linId (K := MvPolynomial I F) q o a) := by
  by_cases h : a = o
  · simpa [linId, h] using (HasFormula.const (I := I) (1 : F))
  · simpa [linId, h] using (HasFormula.const (I := I) (0 : F))

theorem hasFormula_linEval {M : LinTable (MvPolynomial I F) q i} {v : Fin i → MvPolynomial I F}
    (hC : 1 ≤ C) (hi : i ≤ D) (hM : ∀ o a, HasFormula C (M o a))
    (hv : ∀ a, HasFormula C (v a)) (o : Fin q) :
    HasFormula (4 * (D + 1)^2 * C) (linEval M v o) :=
  oneSum hC hi fun a ↦ ((hM o a).mul (hv a)).mono (by omega)

theorem hasFormula_linComp {M : LinTable (MvPolynomial I F) q i}
    {N : LinTable (MvPolynomial I F) i j} (hC : 1 ≤ C) (hi : i ≤ D)
    (hM : ∀ o a, HasFormula C (M o a)) (hN : ∀ a b, HasFormula C (N a b))
    (o : Fin q) (b : Fin j) : HasFormula (4 * (D + 1)^2 * C) (linComp M N o b) :=
  oneSum hC hi fun a ↦ ((hM o a).mul (hN a b)).mono (by omega)

theorem hasFormula_triLeftScalar {B : TriTable (MvPolynomial I F) q i j}
    {v : Fin i → MvPolynomial I F} (hC : 1 ≤ C) (hi : i ≤ D)
    (hB : ∀ o a b, HasFormula C (B o a b)) (hv : ∀ a, HasFormula C (v a)) (o : Fin q)
    (b : Fin j) : HasFormula (4 * (D + 1)^2 * C) (triLeftScalar B v o b) :=
  oneSum hC hi fun a ↦ ((hB o a b).mul (hv a)).mono (by omega)

theorem hasFormula_triRightScalar {B : TriTable (MvPolynomial I F) q i j}
    {w : Fin j → MvPolynomial I F} (hC : 1 ≤ C) (hj : j ≤ D)
    (hB : ∀ o a b, HasFormula C (B o a b)) (hw : ∀ b, HasFormula C (w b)) (o : Fin q)
    (a : Fin i) : HasFormula (4 * (D + 1)^2 * C) (triRightScalar B w o a) :=
  oneSum hC hj fun b ↦ ((hB o a b).mul (hw b)).mono (by omega)

theorem hasFormula_triEval {B : TriTable (MvPolynomial I F) q i j}
    {v : Fin i → MvPolynomial I F} {w : Fin j → MvPolynomial I F}
    (hC : 1 ≤ C) (hi : i ≤ D) (hj : j ≤ D)
    (hB : ∀ o a b, HasFormula C (B o a b)) (hv : ∀ a, HasFormula C (v a))
    (hw : ∀ b, HasFormula C (w b)) (o : Fin q) :
    HasFormula (4 * (D + 1)^2 * C) (triEval B v w o) :=
  twoSum hC hi hj fun a b ↦ (((hB o a b).mul (hv a)).mul (hw b)).mono (by omega)

theorem hasFormula_triPrecomp {B : TriTable (MvPolynomial I F) q i j}
    {M : LinTable (MvPolynomial I F) i k} {N : LinTable (MvPolynomial I F) j l}
    (hC : 1 ≤ C) (hi : i ≤ D) (hj : j ≤ D) (hB : ∀ o a b, HasFormula C (B o a b))
    (hM : ∀ a s, HasFormula C (M a s)) (hN : ∀ b t, HasFormula C (N b t))
    (o : Fin q) (s : Fin k) (t : Fin l) :
    HasFormula (4 * (D + 1)^2 * C) (triPrecomp B M N o s t) :=
  twoSum hC hi hj fun a b ↦ (((hB o a b).mul (hM a s)).mul (hN b t)).mono (by omega)

theorem hasFormula_triPostcomp {M : LinTable (MvPolynomial I F) p q}
    {B : TriTable (MvPolynomial I F) q i j} (hC : 1 ≤ C) (hq : q ≤ D)
    (hM : ∀ o t, HasFormula C (M o t)) (hB : ∀ t a b, HasFormula C (B t a b))
    (o : Fin p) (a : Fin i) (b : Fin j) :
    HasFormula (4 * (D + 1)^2 * C) (triPostcomp M B o a b) :=
  oneSum hC hq fun t ↦ ((hM o t).mul (hB t a b)).mono (by omega)

end PlanarPatch

end

end SpectralBooks
end LinearAlgebra
end OAI
