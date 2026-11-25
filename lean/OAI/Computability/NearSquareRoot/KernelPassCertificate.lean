import OAI.Computability.NearSquareRoot.KernelAutomatonCompose
import OAI.Computability.NearSquareRoot.KernelAutomatonPhase
import OAI.Computability.NearSquareRoot.KernelPass

/-! # Deciding template correctness simultaneously at every even child width

A template entry is a rational transfer-matrix series on pairs of columns.
A child call contributes its exact normalized rational Walsh kernel. Composing
two banks contracts both the finite intermediate row number and the whole
intermediate address. The finite-dimensional word test verifies these series
against every entry of the target.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open KernelAutomatonEquiv Matrix Finset

namespace Plan

private def sumSeries {γ : Type*} {j : ℕ} (T : Fin j → Series γ) : Series γ :=
  (List.ofFn T).foldr Series.add (Series.constant 0)

private theorem eval_sumSeries {γ : Type*} {j : ℕ} (T : Fin j → Series γ) (w : List γ) :
    (sumSeries T).eval w = ∑ k, (T k).eval w := by
  have hs (xs : List (Series γ)) :
      (xs.foldr Series.add (Series.constant 0)).eval w =
        (xs.map (fun t => t.eval w)).sum := by
    induction xs with
    | nil => simp [Series.constant_eval]
    | cons a l ih => simp [Series.add_eval, ih]
  rw [sumSeries, hs, List.map_ofFn, List.sum_ofFn]
  rfl

private def push {X : Type*} [DecidableEq X] (g : X → X) : Series (X × X) :=
  Series.letterProduct (fun ⟨y,x⟩ => if y = g x then 1 else 0)

private theorem eval_push {X : Type*} [DecidableEq X] (g : X → X)
    {h : ℕ} (y x : Fin h → X) :
    (push g).eval (Series.columns y x) = if y = g ∘ x then 1 else 0 := by
  rw [push, Series.letterProduct_eval, Series.columns, List.map_ofFn, List.prod_ofFn]
  by_cases he : y = g ∘ x
  · subst y
    simp [Function.comp_def]
  · simp only [he, ↓reduceIte]
    obtain ⟨a,ha⟩ : ∃ a, y a ≠ g (x a) := by
      by_contra! q
      exact he (funext q)
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp [ha]

/-- The rational word series for one output/input row pair of a program. -/
def series {A i o : ℕ} :
    Plan A i o → Fin o → Fin i → Series (Column A × Column A)
  | .mix coeff, b, a => (push id).scale (value (coeff b a))
  | .xor g, _, _ => push (xorColumn g)
  | .scale _ test table, _, _ => phaseSeries test (value ∘ table)
  | .child axis, _, _ => Series.letterProduct (fun ⟨y,x⟩ => childEntry axis y x)
  | .seq p q, b, a => sumSeries fun c => (p.series b c).compose (q.series c a)
  | .parallel p q, b, a =>
      Fin.addCases (fun l => Fin.addCases (fun k => p.series l k) (fun _ => Series.constant 0) a)
        (fun r => Fin.addCases (fun _ => Series.constant 0) (fun k => q.series r k) a) b

/-- The finite-state composition sums one product dimension per internal row.
The extra state is the zero series at the end of the fold. -/
theorem series_seq_dim {A i j o : ℕ} (p : Plan A j o) (q : Plan A i j) (b : Fin o) (a : Fin i) :
    ((p.seq q).series b a).dim = (∑ c, (p.series b c).dim * (q.series c a).dim) + 1 := by
  have dim_fold (l : List (Series (Column A × Column A))) :
      (l.foldr Series.add (Series.constant 0)).dim = (l.map Series.dim).sum + 1 := by
    induction l with
    | nil => rfl
    | cons u l ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      change u.dim + _ = _
      rw [ih, Nat.add_assoc]
  rw [series, sumSeries, dim_fold, List.map_ofFn, List.sum_ofFn]
  rfl

theorem eval_series {A i o : ℕ} (p : Plan A i o) (b : Fin o) (a : Fin i)
    {h : ℕ} (y x : Addr A h) :
    (p.series b a).eval (Series.columns y x) = p.eval h (b,y) (a,x) := by
  induction p generalizing x y with
  | mix coeff =>
    simp only [series, eval, Series.scale_eval, eval_push, Function.id_comp]
    by_cases q : x = y <;> simp [q, Ne.symm]
  | xor g => exact eval_push _ _ _
  | scale q test table =>
    simpa [series, eval, Series.columns, Function.comp_def, eq_comm] using
      eval_phaseSeries test (value ∘ table) y x
  | child axis =>
    rw [series, Series.letterProduct_eval, Series.columns, List.map_ofFn, List.prod_ofFn]
    rfl
  | seq p q ihp ihq =>
    simp only [series, eval, eval_sumSeries, Series.eval_compose, ihp, ihq,
      Matrix.mul_apply, Fintype.sum_prod_type]
  | @parallel i j o u p q ihp ihq =>
    refine Fin.addCases (fun l => ?_) (fun r => ?_) b <;>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) a <;>
      simp [series, eval, directSum, ihp, ihq, Series.constant_eval]

end Plan

/-- Target word series for one pair of independent rows. -/
def targetSeries (A : ℕ) {W : ℕ} (b a : Fin W) : Series (Column A × Column A) :=
  if a = b then
    Series.letterProduct (fun ⟨y,x⟩ => ∏ j, pairEntry (y j) (x j))
  else Series.constant 0

theorem eval_targetSeries {A W h : ℕ} (b a : Fin W) (y x : Addr A h) :
    (targetSeries A b a).eval (Series.columns y x) = target A W h (b,y) (a,x) := by
  by_cases q : a = b <;>
    simp [targetSeries, target, q, Series.constant_eval, Series.letterProduct_eval,
      Series.columns, List.map_ofFn, List.prod_ofFn, Function.comp_def]

/-- A terminating finite certificate check for all widths. -/
def Plan.certified {A W : ℕ} (p : Plan A W W) : Bool :=
  decide (∀ b a, (p.series b a).same (targetSeries A b a) = true)

theorem Plan.certified_iff {A W : ℕ} (p : Plan A W W) :
    p.certified = true ↔ Correct p := by
  simp only [certified, decide_eq_true_eq, Series.same_iff]
  constructor
  · intro hc h
    ext ⟨b,y⟩ ⟨a,x⟩
    exact (p.eval_series b a y x).symm.trans
      ((hc b a (Series.columns y x)).trans (eval_targetSeries b a y x))
  · intro hc b a w
    let y : Addr A w.length := fun c => (w.get c).1
    let x : Addr A w.length := fun c => (w.get c).2
    have rebuild : Series.columns y x = w := by
      simp [Series.columns, y, x]
    rw [← rebuild, eval_series, eval_targetSeries, hc]

end KernelPass

end NearSquareRoot
end Computability
end OAI
