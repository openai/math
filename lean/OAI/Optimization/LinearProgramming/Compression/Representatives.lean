import OAI.Optimization.LinearProgramming.Compression.Basic
import OAI.Optimization.LinearProgramming.Compression.Signed
import OAI.Optimization.LinearProgramming.Compression.ProjectionCramer

/-! Completing affine answers on a fixed generator set to simultaneous minor representatives (§3). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

private theorem sum_zeroPad {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    {J I : Finset ι} (hJI : J ⊆ I) (g : J → M) :
    (∑ i : I, if h : i.val ∈ J then g ⟨i.val, h⟩ else 0) = ∑ j, g j := by
  symm
  refine Finset.sum_bij_ne_zero (fun j _ _ ↦ (⟨j.val, hJI j.property⟩ : I))
    (fun _ _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro a _ _ b _ _ hab
    exact Subtype.ext (congrArg (fun z : I ↦ z.val) hab)
  · intro b _ hne
    by_cases hb : b.val ∈ J
    · exact ⟨⟨b.val, hb⟩, Finset.mem_univ _, by simpa only [dite_eq_left hb] using hne, rfl⟩
    · exact False.elim (hne (dite_eq_right hb))
  · intro a _ _
    simp only [dite_eq_left a.property]

/-- Pad coefficients by zero on newly added generators. -/
def AffineFamily.zeroPad {ι υ : Type*} [DecidableEq ι] {J I : Finset ι}
    (F : AffineFamily υ J) : AffineFamily υ I where
  coefficient u i := if h : i.val ∈ J then F.coefficient u ⟨i.val, h⟩ else 0
  offset := F.offset

theorem AffineFamily.eval_zeroPad {ι υ : Type*} [DecidableEq ι] {J I : Finset ι}
    (F : AffineFamily υ J) (hJI : J ⊆ I) (y : I → ℝ) (u : υ) :
    (F.zeroPad (I := I)).eval y u = F.eval (fun j : J ↦ y ⟨j.val, hJI j.property⟩) u := by
  unfold AffineFamily.eval
  congr 1
  rw [← sum_zeroPad hJI (fun j : J ↦ (F.coefficient u j : ℝ) * y ⟨j.val, hJI j.property⟩)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ∈ J <;> simp [AffineFamily.zeroPad, hi]

theorem AffineFamily.evalRat_zeroPad {ι υ : Type*} [DecidableEq ι] {J I : Finset ι}
    (F : AffineFamily υ J) (hJI : J ⊆ I) (y : I → ℚ) (u : υ) :
    (F.zeroPad (I := I)).evalRat y u = F.evalRat (fun j : J ↦ y ⟨j.val, hJI j.property⟩) u := by
  unfold AffineFamily.evalRat
  congr 1
  rw [← sum_zeroPad hJI (fun j : J ↦ F.coefficient u j * y ⟨j.val, hJI j.property⟩)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ∈ J <;> simp [AffineFamily.zeroPad, hi]

/-- If a request succeeds, its affine function on `J` is fixed. This completes those functions
on one larger dissociated set. Every returned function agrees for every specialization on the
new generators. The unseen minors use ternary coefficients and offsets of height at most `2D`. -/
theorem exists_completed_affineFamily {ι : Type*} [DecidableEq ι]
    (l : ι → ℝ) (U J : Finset ι) (hJU : J ⊆ U) (hJ : IsDissociated l J)
    (D H : ℕ) (hD : 0 < D) (accepted : Finset U) (known : AffineFamily U J)
    (hk : ∀ u ∈ accepted, |known.eval (fun j ↦ l j) u - l u| ≤ 1 / (D : ℝ))
    (hkc : ∀ u ∈ accepted, ∀ j, (known.coefficient u j).num.natAbs ≤ H ∧
      (known.coefficient u j).den ≤ H)
    (hko : ∀ u ∈ accepted, (known.offset u).num.natAbs ≤ H ∧ (known.offset u).den ≤ H) :
    ∃ (I : Finset ι) (hJI : J ⊆ I), I ⊆ U ∧ IsDissociated l I ∧ ∃ F : AffineFamily U I,
      (∀ u, |F.eval (fun i ↦ l i) u - l u| ≤ 1 / (D : ℝ)) ∧
      (∀ u ∈ accepted, ∀ y : I → ℚ,
        F.evalRat y u = known.evalRat (fun j : J ↦ y ⟨j.val, hJI j.property⟩) u) ∧
      (∀ u i, (F.coefficient u i).num.natAbs ≤ max H (2*D) ∧
        (F.coefficient u i).den ≤ max H (2*D)) ∧
      (∀ u, (F.offset u).num.natAbs ≤ max H (2*D) ∧ (F.offset u).den ≤ max H (2*D)) := by
  classical
  obtain ⟨I, hJI, hIU, hI, c, k, hc⟩ := exists_simultaneous_affine_grid l U J hJU hJ D hD
  let old := known.zeroPad (I := I)
  let F : AffineFamily U I := {
    coefficient := fun u i ↦ if u ∈ accepted then old.coefficient u i else (c u i : ℚ)
    offset := fun u ↦ if u ∈ accepted then old.offset u else (k u : ℚ) / D }
  have hlarge : 1 ≤ max H (2*D) := by omega
  refine ⟨I, hJI, hIU, hI, F, ?_, ?_, ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ accepted
    · have he : F.eval (fun i ↦ l i) u = old.eval (fun i ↦ l i) u := by
        simp only [AffineFamily.eval, F, ite_eq_left hu]
      rw [he, show old.eval (fun i ↦ l i) u = _ from known.eval_zeroPad hJI _ _]
      exact hk _ hu
    · obtain ⟨_, _, _, _, he⟩ := hc u
      simp only [AffineFamily.eval, F, ite_eq_right hu, Rat.cast_intCast, Rat.cast_div, Rat.cast_natCast]
      rw [Finset.sum_coe_sort I (fun i ↦ (c u i : ℝ) * l i), abs_sub_comm]
      exact he.le
  · intro u hu y
    have he : F.evalRat y u = old.evalRat y u := by simp only [AffineFamily.evalRat, F, ite_eq_left hu]
    exact he.trans (known.evalRat_zeroPad hJI y u)
  · intro u i
    by_cases hu : u ∈ accepted
    · by_cases hi : i.val ∈ J
      · obtain ⟨hn, hd⟩ := hkc u hu ⟨i.val, hi⟩
        simpa only [F, ite_eq_left hu, old, AffineFamily.zeroPad, dite_eq_left hi] using
          And.intro (hn.trans (le_max_left H (2*D))) (hd.trans (le_max_left H (2*D)))
      · simp [F, old, AffineFamily.zeroPad, hu, hi, hlarge]
    · rcases (hc u).1 i with h | h | h <;> simp [F, hu, h, hlarge]
  · intro u
    by_cases hu : u ∈ accepted
    · obtain ⟨hn, hd⟩ := hko u hu
      simpa only [F, ite_eq_left hu, old, AffineFamily.zeroPad] using
        And.intro (hn.trans (le_max_left H (2*D))) (hd.trans (le_max_left H (2*D)))
    · obtain ⟨_, _, _, hkn, _⟩ := hc u
      have hkn' : (k u).natAbs ≤ 2*D := by
        exact_mod_cast (show ((k u).natAbs : ℤ) ≤ 2 * (D : ℤ) by simpa using hkn)
      obtain ⟨hn, hd⟩ := reduced_fraction_height (k u) (D : ℤ) (by exact_mod_cast hD.ne')
      simp only [F, ite_eq_right hu]
      norm_cast at hn hd ⊢
      exact ⟨by omega, by omega⟩

end Compression
end LinearProgramming
end Optimization
end OAI
