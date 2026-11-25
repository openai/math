import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchEntries
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchFormula

/-! # Gate cost of pruning a tree of patch tables

We run the scalar, unary, and trivalent pruning operations on formal polynomials
in the original patch entries. Each level performs at most two successive finite
contractions. The resulting expressions compile to one division-free program,
with an output register for every table entry of the pruned tree.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace PlanarPatch

open Arithmetic
noncomputable section

variable {F I V : Type*} [Field F] {d : V → ℕ}

private abbrev Poly := MvPolynomial I F

/-- A common formula-weight bound on every local coefficient of an unpruned tree. -/
def OrderedTensorTree.FormulaBound (C : ℕ) :
    {q : ℕ} → OrderedTensorTree (MvPolynomial I F) d q → Prop
  | _, .scalar v => ∀ o, HasFormula C (v o)
  | _, .stub _ M => ∀ o a, HasFormula C (M o a)
  | _, .unary M t => (∀ o a, HasFormula C (M o a)) ∧ t.FormulaBound C
  | _, .branch B t u => (∀ o a b, HasFormula C (B o a b)) ∧ t.FormulaBound C ∧ u.FormulaBound C

/-- A common formula-weight bound on the coefficient tables of the output tree. -/
def TrivalentTree.FormulaBound {q : ℕ} (C : ℕ) (t : TrivalentTree (MvPolynomial I F) d q) :=
  ∀ e : t.Entry, HasFormula C (t.entry e)

private theorem branch_formulaBound {q i j C : ℕ} {B : TriTable (Poly (I := I) (F := F)) q i j}
    {t : TrivalentTree _ d i} {u : TrivalentTree _ d j} :
    (TrivalentTree.branch B t u).FormulaBound C ↔
      (∀ o a b, HasFormula C (B o a b)) ∧ t.FormulaBound C ∧ u.FormulaBound C := by
  constructor
  · intro h
    exact ⟨fun o a b ↦ h (Sum.inl (o,a,b)),
      fun e ↦ h (Sum.inr (Sum.inl e)), fun e ↦ h (Sum.inr (Sum.inr e))⟩
  · rintro ⟨h, ht, hu⟩ (⟨o,a,b⟩ | (e | e))
    · exact h o a b
    · exact ht e
    · exact hu e

private theorem TrivalentTree.FormulaBound.mono {q a b : ℕ} {t : TrivalentTree (MvPolynomial I F) d q}
    (h : t.FormulaBound a) (hab : a ≤ b) : t.FormulaBound b := fun e ↦ (h e).mono hab

private def Pruned.FormulaBound {q : ℕ} (C : ℕ) : Pruned (MvPolynomial I F) d q → Prop
  | .scalar v => ∀ o, HasFormula C (v o)
  | .tree M t => (∀ o a, HasFormula C (M o a)) ∧ t.FormulaBound C

private theorem Pruned.FormulaBound.mono {q a b : ℕ} {t : Pruned (MvPolynomial I F) d q}
    (h : t.FormulaBound a) (hab : a ≤ b) : t.FormulaBound b := by
  cases t with
  | scalar => exact fun o ↦ (h o).mono hab
  | tree => exact ⟨fun o i ↦ (h.1 o i).mono hab, h.2.mono hab⟩

/-- A single table contraction on at most two summed indices grows the
weight bound by at most this factor. -/
def contractionFactor (D : ℕ) := 4 * (D+1)^2

private theorem le_factor_mul (D C : ℕ) : C ≤ contractionFactor D * C := by
  apply Nat.le_mul_of_pos_left
  unfold contractionFactor
  positivity

private theorem Pruned.formulaBound_post {q i C D : ℕ} {M : LinTable (MvPolynomial I F) q i}
    {t : Pruned _ d i} (hC : 1 ≤ C) (hi : i ≤ D) (hM : ∀ o a, HasFormula C (M o a))
    (ht : t.FormulaBound C) : (post M t).FormulaBound (contractionFactor D * C) := by
  cases t with
  | scalar v => exact fun o ↦ hasFormula_linEval hC hi hM ht o
  | tree N t =>
    exact ⟨fun o a ↦ hasFormula_linComp hC hi hM ht.1 o a, ht.2.mono (le_factor_mul ..)⟩

private theorem Pruned.formulaBound_fuse {q i j C D : ℕ} {B : TriTable (MvPolynomial I F) q i j}
    {t : Pruned _ d i} {u : Pruned _ d j} (hC : 1 ≤ C) (hi : i ≤ D) (hj : j ≤ D)
    (hB : ∀ o a b, HasFormula C (B o a b)) (ht : t.FormulaBound C) (hu : u.FormulaBound C) :
    (fuse B t u).FormulaBound (contractionFactor D * (contractionFactor D * C)) := by
  have h₁ := le_factor_mul D C
  have h₂ := le_factor_mul D (contractionFactor D * C)
  cases t with
  | scalar v =>
    cases u with
    | scalar w => exact fun o ↦ (hasFormula_triEval hC hi hj hB ht hu o).mono h₂
    | tree N u =>
      exact ⟨fun o a ↦ hasFormula_linComp (hC.trans h₁) hj
        (fun o b ↦ hasFormula_triLeftScalar hC hi hB ht o b)
        (fun c a ↦ (hu.1 c a).mono h₁) o a, hu.2.mono (h₁.trans h₂)⟩
  | tree M t =>
    cases u with
    | scalar w =>
      exact ⟨fun o a ↦ hasFormula_linComp (hC.trans h₁) hi
        (fun o a ↦ hasFormula_triRightScalar hC hj hB hu o a)
        (fun c a ↦ (ht.1 c a).mono h₁) o a, ht.2.mono (h₁.trans h₂)⟩
    | tree N u =>
      exact ⟨fun o a ↦ (hasFormula_linId q o a).mono (hC.trans (h₁.trans h₂)),
        branch_formulaBound.mpr ⟨fun o a b ↦ (hasFormula_triPrecomp hC hi hj hB ht.1 hu.1 o a b).mono h₂,
          ht.2.mono (h₁.trans h₂), hu.2.mono (h₁.trans h₂)⟩⟩

private def budget (D C h : ℕ) := contractionFactor D ^ (2*h) * C

private theorem budget_mono (D C : ℕ) {h k : ℕ} (hh : h ≤ k) : budget D C h ≤ budget D C k := by
  apply Nat.mul_le_mul_right
  exact Nat.pow_le_pow_right (by unfold contractionFactor; positivity) (Nat.mul_le_mul_left 2 hh)

private theorem budget_base (D C h : ℕ) : C ≤ budget D C h := by
  simpa [budget] using budget_mono D C (Nat.zero_le h)

private theorem budget_succ (D C h : ℕ) :
    budget D C (h+1) = contractionFactor D * (contractionFactor D * budget D C h) := by
  simp only [budget, Nat.mul_add, Nat.mul_one, pow_add]
  ring

private theorem OrderedTensorTree.formulaBound_prune {q D C : ℕ}
    (t : OrderedTensorTree (MvPolynomial I F) d q)
    (hC : 1 ≤ C) (hb : t.Bounded D) (ht : t.FormulaBound C) :
    t.prune.FormulaBound (budget D C t.height) := by
  induction t with
  | scalar => simpa [height, budget, prune, Pruned.FormulaBound, FormulaBound] using ht
  | stub v M =>
    simp only [height, budget, Nat.mul_zero, pow_zero, one_mul, prune]
    exact ⟨ht, fun e ↦ Empty.elim e⟩
  | unary M t ih =>
    rw [height, budget_succ, prune]
    have h₀ := budget_base D C t.height
    exact (Pruned.formulaBound_post (hC.trans h₀) (root_bounded t hb.2)
      (fun o a ↦ (ht.1 o a).mono h₀) (ih hb.2 ht.2)).mono (le_factor_mul ..)
  | branch B t u ih jh =>
    rw [height, budget_succ, prune]
    have h₀ := budget_base D C (max t.height u.height)
    exact Pruned.formulaBound_fuse (hC.trans h₀) (root_bounded t hb.2.1) (root_bounded u hb.2.2)
      (fun o a b ↦ (ht.1 o a b).mono h₀)
      ((ih hb.2.1 ht.2.1).mono (budget_mono D C (le_max_left ..)))
      ((jh hb.2.2 ht.2.2).mono (budget_mono D C (le_max_right ..)))

/-- Pruning preserves the contraction as a formal polynomial in the patch inputs.
Every coefficient in the resulting tree admits an expression of bounded weight. -/
theorem OrderedTensorTree.trivalent_pruning_formulaBound {q D C : ℕ}
    (t : OrderedTensorTree (MvPolynomial I F) d q)
    (hC : 1 ≤ C) (hb : t.Bounded D) (ht : t.FormulaBound C) (hports : 2 ≤ t.labels.length) :
    ∃ (u : TrivalentTree (MvPolynomial I F) d q), u.labels = t.labels ∧ u.Bounded D ∧
      u.vertices + 2 = t.labels.length + 1 ∧ (∀ x, u.eval x = t.eval x) ∧
      u.FormulaBound (contractionFactor D ^ (2*t.height+1) * C) := by
  have hl := t.labels_prune
  have he := t.eval_prune
  have hdim := t.bounded_prune hb
  have hc := t.formulaBound_prune hC hb ht
  cases hp : t.prune with
  | scalar v =>
    rw [hp] at hl
    change [] = t.labels at hl
    simp [← hl] at hports
  | tree M u =>
    rw [hp] at hl hdim hc
    cases u with
    | port v =>
      change [v] = t.labels at hl
      simp [← hl] at hports
    | branch B l r =>
      let u := TrivalentTree.branch (triPostcomp M B) l r
      have hlu : u.labels = t.labels := hl
      have hdu : u.Bounded D := ⟨t.root_bounded hb, hdim.2⟩
      refine ⟨u, hlu, hdu, ?_, ?_, ?_⟩
      · have hh := u.vertices_add_one_eq_length
        rw [hlu] at hh
        omega
      · intro x
        specialize he x
        rw [hp] at he
        exact (triEval_postcomp M B _ _).trans he
      · have h₀ := hC.trans (budget_base D C t.height)
        obtain ⟨hB, hL, hR⟩ := branch_formulaBound.mp hc.2
        have hu : u.FormulaBound (contractionFactor D * budget D C t.height) :=
          branch_formulaBound.mpr ⟨fun o a b ↦ hasFormula_triPostcomp h₀ hdim.1 hc.1 hB o a b,
            hL.mono (le_factor_mul ..), hR.mono (le_factor_mul ..)⟩

        convert hu using 1
        simp only [budget, pow_succ]
        ring

/-- Pruning preserves the contraction as a formal polynomial in the patch inputs.
The same straight-line program computes all entries of the resulting tree. -/
theorem OrderedTensorTree.trivalent_pruning_cost {q D C : ℕ}
    (t : OrderedTensorTree (MvPolynomial I F) d q)
    (hC : 1 ≤ C) (hb : t.Bounded D) (ht : t.FormulaBound C) (hports : 2 ≤ t.labels.length) :
    ∃ (u : TrivalentTree (MvPolynomial I F) d q), u.labels = t.labels ∧ u.Bounded D ∧
      u.vertices + 2 = t.labels.length + 1 ∧ (∀ x, u.eval x = t.eval x) ∧
      ∃ (r : ℕ) (p : Program F I r) (out : u.Entry → Fin r),
        (∀ e, registerPolynomial p (out e) = u.entry e) ∧
          p.cost ≤ u.vertices * D^3 * (contractionFactor D ^ (2*t.height+1) * C) := by
  obtain ⟨u, hl, hbu, hv, he, hu⟩ := t.trivalent_pruning_formulaBound hC hb ht hports
  refine ⟨u, hl, hbu, hv, he, ?_⟩
  choose E hE hcost using hu
  let p := Expression.compileFamily E
  refine ⟨p.registers, p.program, p.output,
    fun e ↦ (registerPolynomial_compileFamily E e).trans (hE e), ?_⟩
  rw [p.cost_eq]
  calc
    _ ≤ ∑ _ : u.Entry, contractionFactor D ^ (2*t.height+1) * C :=
      Finset.sum_le_sum (fun e _ ↦ (Nat.le_succ _).trans (hcost e))
    _ = Fintype.card u.Entry * (contractionFactor D ^ (2*t.height+1) * C) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (u.card_entry_le hbu)

end
end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
