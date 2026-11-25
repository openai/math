import OAI.Optimization.LinearProgramming.Compression.AffineValue
import OAI.Optimization.LinearProgramming.Compression.BitBudget
import OAI.Optimization.LinearProgramming.Compression.CommitCap
import OAI.Optimization.LinearProgramming.Compression.FiberProjection
import OAI.Optimization.LinearProgramming.Compression.ProjectionSmallPoint
import OAI.Optimization.LinearProgramming.Compression.Representatives

/-! One generator commitment for every successful request that can occur in a run.
The budget, and hence the committed vector, are fixed before the choice of the family
extending the request test. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators Matrix

/-- Height of the rational linear inequalities controlling all four-term comparisons. -/
def epochRowHeight (B E C : ℕ) : ℕ := (B + 17 + 4*C)*(E*C^4)

/-- A fixed choice from the bounded-sign construction. Its arguments consist only of the
generator proxies and size parameters, independently of all future requests. -/
noncomputable def epochCommit {σ : Type*} [Fintype σ] (x : σ → ℝ)
    (width rowHeight : ℕ) : σ → ℚ :=
  Classical.choose (exists_bounded_projection_commit x (fiberProjectionBudget (Fintype.card σ) width rowHeight))

/-- The exact guarantee needed from the executable sign-rounding procedure.
It refers to integer halfspaces and includes tests at equality. -/
structure ValidEpochCommit {σ : Type*} [Fintype σ] (x : σ → ℝ)
    (width H : ℕ) (γ : σ → ℚ) : Prop where
  size : ∀ j, (γ j).num.natAbs < fiberCommitCap (Fintype.card σ)
      ((Fintype.card σ+1)*fiberProjectionBudget (Fintype.card σ) width H+1) ∧
    (γ j).den < fiberCommitCap (Fintype.card σ)
      ((Fintype.card σ+1)*fiberProjectionBudget (Fintype.card σ) width H+1)
  tests : ∀ (a : σ → ℤ) (c : ℤ),
    (∀ j, (a j).natAbs ≤ fiberProjectionBudget (Fintype.card σ) width H) →
    c.natAbs ≤ fiberProjectionBudget (Fintype.card σ) width H →
    (∑ j, (a j : ℝ) * x j) ≤ c → (∑ j, (a j : ℝ) * (γ j : ℝ)) ≤ c

theorem epochCommit_valid {σ : Type*} [Fintype σ] (x : σ → ℝ) (width H : ℕ) :
    ValidEpochCommit x width H (epochCommit x width H) := by
  have h := Classical.choose_spec
    (exists_bounded_projection_commit x (fiberProjectionBudget (Fintype.card σ) width H))
  exact ⟨fun j => ⟨(h.1 j).1.trans_le (commitHeight_le_fiberCommitCap ..),
    (h.1 j).2.trans_le (commitHeight_le_fiberCommitCap ..)⟩, h.2⟩

/-- Uniform (numerator and denominator) bound for the entire assignment rather than
only the minor replies that were requested. -/
def epochValueCap (k width B E C : ℕ) : ℕ :=
  offlineValueCap width C (offlinePointCap width (fiberPinnedHeight k width (epochRowHeight B E C)))

private theorem cast_matrix_feasible {α κ : Type*} [Fintype κ]
    {A : Matrix α κ ℚ} {b : α → ℚ} {y : κ → ℚ} (h : A *ᵥ y ≤ b) :
    A.map (Rat.cast : ℚ → ℝ) *ᵥ (fun i => (y i : ℝ)) ≤ (fun i => (b i : ℝ)) := by
  intro i
  have hh : (((A *ᵥ y) i : ℚ) : ℝ) ≤ (b i : ℝ) := by exact_mod_cast h i
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using hh

/-- For a bounded affine representation on a completion of the generator set,
the original proxies give a real point of the clipping polyhedron. The predetermined
commit of the old coordinates has a small rational point in its fiber. -/
theorem epoch_realization {α σ κ : Type*} [Fintype α] [Fintype σ] [Fintype κ]
    [DecidableEq σ] [DecidableEq κ]
    (F : AffineFamily α κ) (proxy trueLog : α → ℝ) (x : κ → ℝ) (anchor : σ → κ)
    (width B E C : ℕ) (hw : Fintype.card κ ≤ width) (hE : 0 < E) (hC : 0 < C)
    (hF : ∀ u, |F.eval x u - proxy u| ≤ 1 / (E : ℝ))
    (hl : ∀ u, |proxy u - trueLog u| ≤ 1 / (E : ℝ))
    (hc : ∀ u j, (F.coefficient u j).num.natAbs ≤ C ∧ (F.coefficient u j).den ≤ C)
    (ho : ∀ u, (F.offset u).num.natAbs ≤ C ∧ (F.offset u).den ≤ C)
    (γ : σ → ℚ) (hγ : ValidEpochCommit (x ∘ anchor) width (epochRowHeight B E C) γ) :
    ∃ y : κ → ℚ,
      (∀ j, y (anchor j) = γ j) ∧
      (∀ u, (F.evalRat y u).num.natAbs ≤ epochValueCap (Fintype.card σ) width B E C ∧
        (F.evalRat y u).den ≤ epochValueCap (Fintype.card σ) width B E C) ∧
      ∀ a : α → ℤ, (∑ u, |(a u : ℝ)|) ≤ 4 →
        |clip B (intForm a (fun u => (F.evalRat y u : ℝ))) - clip B (intForm a trueLog)| ≤
          17 * (1 / (E : ℝ)) := by
  classical
  let k := Fintype.card σ
  let H := epochRowHeight B E C
  let Q := fiberProjectionBudget k width H
  let K := fiberPinnedHeight k width H
  have hH : 1 ≤ H := Nat.succ_le_of_lt (by dsimp [H,epochRowHeight]; positivity)
  have hη : (0 : ℚ) < 1 / E := by positivity
  have hηcast : (((1 / (E : ℚ)) : ℚ) : ℝ) = 1 / (E : ℝ) := by simp
  have mag (q : ℚ) (h : q.num.natAbs ≤ C) : |q| ≤ (C : ℚ) :=
    (rat_abs_le_num_natAbs q).trans (by exact_mod_cast h)
  let A := clippingMatrix F B (1/(E:ℚ)) trueLog
  let b := clippingRhs F B (1/(E:ℚ)) trueLog
  obtain ⟨hA, hb⟩ := clipping_system_height F B E trueLog hC hE
    (fun u j => ⟨mag _ (hc u j).1, (hc u j).2⟩) (fun u => ⟨mag _ (ho u).1, (ho u).2⟩)
  have hx : A.map (Rat.cast : ℚ → ℝ) *ᵥ x ≤ (fun t => (b t : ℝ)) := by
    apply (comparisonRows_iff_mulVec_le _ _ _ _ _).mp
    apply affineFamily_comparisonRows_feasible F x proxy trueLog B _ hη
    · simpa only [hηcast] using hF
    · simpa only [hηcast] using hl
  have hbudget := fiberProjectionBudget_term_le k width H hw
  have hproj := preserves_generator_fiber A b anchor hH hA hb
    (x := x ∘ anchor) (x' := fun j => (γ j : ℝ)) ⟨x, hx, fun _ => rfl⟩
    (fun a c ha hbc => hγ.tests a c (fun j => (ha j).trans hbudget) (hbc.trans hbudget))
  have hHK : H ≤ K := by dsimp [K,fiberPinnedHeight]; omega
  have hK : 1 ≤ K := hH.trans hHK
  have hγK (j : σ) : (γ j).num.natAbs ≤ K ∧ (γ j).den ≤ K := by
    have hcommit : fiberCommitCap k ((k+1)*Q+1) ≤ K := by dsimp [K,fiberPinnedHeight,Q]; omega
    exact ⟨(hγ.size j).1.le.trans hcommit, (hγ.size j).2.le.trans hcommit⟩
  obtain ⟨y,hy,hfix,hsize⟩ := exists_small_rat_feasible_with_fixed A b anchor γ hK
    (fun t j => ⟨(hA t j).1.trans hHK, (hA t j).2.trans hHK⟩)
    (fun t => ⟨(hb t).1.trans hHK, (hb t).2.trans hHK⟩) hγK hproj
  refine ⟨y, hfix, ?_, ?_⟩
  · have hcap := offlinePointCap_mono hw hK
    intro u
    exact affine_evalRat_height F y u width C (offlinePointCap width K) hw (hc u) (ho u)
      (fun j => ⟨(hsize j).1.trans hcap, (hsize j).2.trans hcap⟩)
  · intro a ha
    have hrow := (comparisonRows_iff_mulVec_le F B _ trueLog _).mpr
      (cast_matrix_feasible hy) a ha
    have habs := comparisonRow_abs_clip_sub_le (by positivity : 0 ≤ (B : ℚ)) hη hrow
    simpa only [AffineFamily.cast_evalRat, Rat.cast_natCast, hηcast] using habs


/-- Every affine request successfully answered during one generator epoch has one common
bounded assignment, including requests that have not yet been issued. The commitment
does not depend on the set of accepted requests or on their affine coefficients. -/
theorem epoch_commit_extends_accepted {ι : Type*} [DecidableEq ι]
    (proxy : ι → ℝ) (U J : Finset ι) (trueLog : U → ℝ)
    (hJU : J ⊆ U) (hJ : IsDissociated proxy J) (width B E H : ℕ) (hE : 0 < E)
    (hwidth : ∀ I ⊆ U, IsDissociated proxy I → I.card ≤ width)
    (hl : ∀ u : U, |proxy u - trueLog u| ≤ 1/(E:ℝ))
    (accepted : Finset U) (known : AffineFamily U J)
    (hk : ∀ u ∈ accepted, |known.eval (fun j => proxy j) u - proxy u| ≤ 1/(E:ℝ))
    (hc : ∀ u ∈ accepted, ∀ j, (known.coefficient u j).num.natAbs ≤ H ∧
      (known.coefficient u j).den ≤ H)
    (ho : ∀ u ∈ accepted, (known.offset u).num.natAbs ≤ H ∧ (known.offset u).den ≤ H)
    (γ : J → ℚ) (hγ : ValidEpochCommit (fun j : J => proxy j) width
      (epochRowHeight B E (max H (2*E))) γ) :
    let C := max H (2*E)
    ∃ f : U → ℚ, (∀ u ∈ accepted, f u = known.evalRat γ u) ∧
      (∀ u, (f u).num.natAbs ≤ epochValueCap J.card width B E C ∧
        (f u).den ≤ epochValueCap J.card width B E C) ∧
      ∀ a : U → ℤ, (∑ u, |(a u : ℝ)|) ≤ 4 →
        |clip B (intForm a (fun u => (f u : ℝ))) - clip B (intForm a trueLog)| ≤
          17 * (1 / (E : ℝ)) := by
  classical
  obtain ⟨I, hJI, hIU, hI, F, hF, hknown, hFc, hFo⟩ :=
    exists_completed_affineFamily proxy U J hJU hJ E H hE accepted known hk hc ho
  let anchor : J → I := fun j => ⟨j.val,hJI j.property⟩
  have hw : Fintype.card I ≤ width := by simpa using hwidth I hIU hI
  have hC : 0 < max H (2*E) := (by omega)
  obtain ⟨y,hy,hsize,hclip⟩ := epoch_realization F (fun u => proxy u) trueLog
    (fun j => proxy j) anchor width B E (max H (2*E)) hw hE hC hF hl hFc hFo γ hγ
  refine ⟨F.evalRat y, ?_, by simpa only [Fintype.card_coe] using hsize, hclip⟩
  intro u hu
  rw [hknown u hu y]
  congr 1
  funext j
  exact hy j

/-- The proof uses 17 grid units of error out of the 128 grid units available in δ. -/
theorem seventeen_units_le_clip_precision (B : ℕ) :
    17 * (1 / (2 : ℝ)^(B+7)) ≤ 1 / (2 : ℝ)^B := by
  rw [pow_add]
  have hb : 0 < (2 : ℝ)^B := by positivity
  field_simp
  norm_num
end Compression
end LinearProgramming
end Optimization
end OAI
