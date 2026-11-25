import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPruneCost
import Mathlib.Data.Fintype.Sigma

/-! # Computing all pruned tables of a patch

A single program computes the table entries for all terms in the straightening
identity. The exponent is linear in the wire width when the patch size, hence
the maximum number of vertices and the triangulation depth, is fixed.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace PlanarPatch

open Arithmetic

variable {F I V T : Type*} [Field F] [Fintype T] {d : V → ℕ} {q : ℕ}

/-- Compile every entry at every vertex in every summand into one program. -/
theorem compile_tree_tables {D W n : ℕ} (u : T → TrivalentTree (MvPolynomial I F) d q)
    (hb : ∀ k, (u k).Bounded D) (hn : ∀ k, (u k).vertices ≤ n)
    (hw : ∀ k, (u k).FormulaBound W) :
    ∃ (r : ℕ) (p : Program F I r) (out : (k : T) → (u k).Entry → Fin r),
      (∀ k e, registerPolynomial p (out k e) = (u k).entry e) ∧
        p.cost ≤ Fintype.card T * n * D^3 * W := by
  classical
  choose E hE hC using fun ke : (k : T) × (u k).Entry ↦ hw ke.1 ke.2
  let p := Expression.compileFamily E
  refine ⟨p.registers, p.program, fun k e ↦ p.output ⟨k,e⟩,
    fun k e ↦ (registerPolynomial_compileFamily E ⟨k,e⟩).trans (hE ⟨k,e⟩), ?_⟩
  have hc : Fintype.card ((k : T) × (u k).Entry) ≤ Fintype.card T * (n * D^3) := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _ : T, n * D^3 := Finset.sum_le_sum fun k _ ↦
        ((u k).card_entry_le (hb k)).trans (Nat.mul_le_mul_right _ (hn k))
      _ = _ := by simp
  rw [p.cost_eq]
  calc
    _ ≤ ∑ _ : (k : T) × (u k).Entry, W :=
      Finset.sum_le_sum fun ke _ ↦ (Nat.le_succ _).trans (hC ke)
    _ = Fintype.card ((k : T) × (u k).Entry) * W := by simp
    _ ≤ _ := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right W hc

/-- With width at most `8*w`, each pruning operation has formula growth
at most `2^(20*(w+1))`. -/
theorem contractionFactor_le_pow {D w : ℕ} (hD : D ≤ 2^(8*w)) :
    contractionFactor D ≤ 2^(20*(w+1)) := by
  have hd : D+1 ≤ 2^(8*w+1) := by
    rw [pow_succ]
    have hp : 0 < 2^(8*w) := by positivity
    omega
  calc
    _ ≤ 4 * (2^(8*w+1))^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hd 2)
    _ = 2^(2 + (8*w+1)*2) := by rw [pow_add 2 2, pow_mul 2 (8*w+1) 2]; rfl
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The gate budget for the whole patch, with the dependence on the width
and the fixed patch parameters separated explicitly. -/
theorem patch_table_gate_budget {m n D C H w a c : ℕ}
    (hm : m ≤ 2^(w+c)) (hD : D ≤ 2^(8*w)) (hC : C ≤ 2^(a*(w+1))) :
    m*n*D^3*(contractionFactor D^(2*H+1)*C) ≤
      2^((c+1+n+24+20*(2*H+1)+a)*(w+1)) := by
  have hn : n ≤ (2 : ℕ)^n := Nat.lt_two_pow_self.le
  have bound := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul hm hn) (Nat.pow_le_pow_left hD 3))
    (Nat.mul_le_mul (Nat.pow_le_pow_left (contractionFactor_le_pow hD) (2*H+1)) hC)
  refine bound.trans ?_
  simp only [← pow_mul, ← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.zero_le (c*w), Nat.zero_le (n*w)]

/-- For given polynomial tables, prune an entire straightening decomposition
and compute the resulting coefficients together. There are at most `2^(w+c)`
terms, bonds have dimension at most `2^(8*w)`, and the starting coefficient
weight is at most `2^(a*(w+1))`. The final program has `2^O(w+1)` gates for
fixed `c, n, H, a`. -/
theorem compile_pruned_patch_with_formulas {w c a H n D C : ℕ}
    (t : T → OrderedTensorTree (MvPolynomial I F) d q)
    (hm : Fintype.card T ≤ 2^(w+c)) (hD : D ≤ 2^(8*w))
    (hC : 1 ≤ C) (hsize : C ≤ 2^(a*(w+1)))
    (hb : ∀ k, (t k).Bounded D) (hc : ∀ k, (t k).FormulaBound C)
    (hh : ∀ k, (t k).height ≤ H)
    (hp : ∀ k, 2 ≤ (t k).labels.length) (hn : ∀ k, (t k).labels.length ≤ n+1) :
    ∃ (u : T → TrivalentTree (MvPolynomial I F) d q),
      (∀ k, (u k).labels = (t k).labels ∧ (u k).Bounded D ∧
        (u k).vertices + 2 = (t k).labels.length + 1 ∧ ∀ x, (u k).eval x = (t k).eval x) ∧
      (∀ k, (u k).FormulaBound (2^((20*(2*H+1)+a)*(w+1)))) ∧
      ∃ (r : ℕ) (p : Program F I r) (out : (k : T) → (u k).Entry → Fin r),
        (∀ k e, registerPolynomial p (out k e) = (u k).entry e) ∧
          p.cost ≤ 2^((c+1+n+24+20*(2*H+1)+a)*(w+1)) := by
  classical
  choose u hul hub huv hue huf using fun k ↦
    (t k).trivalent_pruning_formulaBound hC (hb k) (hc k) (hp k)
  refine ⟨u, fun k ↦ ⟨hul k, hub k, huv k, hue k⟩, ?_⟩
  have hweight (k : T) : (u k).FormulaBound (contractionFactor D^(2*H+1)*C) := by
    intro e
    apply (huf k e).mono
    apply Nat.mul_le_mul_right
    exact Nat.pow_le_pow_right (by unfold contractionFactor; positivity) (by have := hh k; omega)
  have hvertex (k : T) : (u k).vertices ≤ n := by have := huv k; have := hn k; omega
  obtain ⟨r,p,out,he,hs⟩ := compile_tree_tables u hub hvertex hweight
  refine ⟨fun k e => (hweight k e).mono ?_, r,p,out,he,hs.trans (patch_table_gate_budget hm hD hsize)⟩
  calc
    _ ≤ (2^(20*(w+1)))^(2*H+1) * 2^(a*(w+1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (contractionFactor_le_pow hD) _) hsize
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring

/-- For given polynomial tables, prune an entire straightening decomposition
and compute the resulting coefficients together. There are at most `2^(w+c)`
terms, bonds have dimension at most `2^(8*w)`, and the starting coefficient
weight is at most `2^(a*(w+1))`. The final program has `2^O(w+1)` gates for
fixed `c, n, H, a`. -/
theorem compile_pruned_patch {w c a H n D C : ℕ}
    (t : T → OrderedTensorTree (MvPolynomial I F) d q)
    (hm : Fintype.card T ≤ 2^(w+c)) (hD : D ≤ 2^(8*w))
    (hC : 1 ≤ C) (hsize : C ≤ 2^(a*(w+1)))
    (hb : ∀ k, (t k).Bounded D) (hc : ∀ k, (t k).FormulaBound C)
    (hh : ∀ k, (t k).height ≤ H)
    (hp : ∀ k, 2 ≤ (t k).labels.length) (hn : ∀ k, (t k).labels.length ≤ n+1) :
    ∃ (u : T → TrivalentTree (MvPolynomial I F) d q),
      (∀ k, (u k).labels = (t k).labels ∧ (u k).Bounded D ∧
        (u k).vertices + 2 = (t k).labels.length + 1 ∧ ∀ x, (u k).eval x = (t k).eval x) ∧
      ∃ (r : ℕ) (p : Program F I r) (out : (k : T) → (u k).Entry → Fin r),
        (∀ k e, registerPolynomial p (out k e) = (u k).entry e) ∧
          p.cost ≤ 2^((c+1+n+24+20*(2*H+1)+a)*(w+1)) := by
  obtain ⟨u,hu,_,hprogram⟩ := compile_pruned_patch_with_formulas t hm hD hC hsize hb hc hh hp hn
  exact ⟨u,hu,hprogram⟩

end PlanarPatch

end

end SpectralBooks
end LinearAlgebra
end OAI
