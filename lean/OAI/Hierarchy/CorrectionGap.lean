import OAI.Hierarchy.CorrectionRetained
import OAI.Hierarchy.CorrectionBatch
import OAI.Hierarchy.CorrectionPrice
import OAI.Hierarchy.CorrectionBenchmark

namespace OAI
/-! # Sparse correction on the physical unit catalyst frame -/

noncomputable section
namespace Hierarchy.CorrectionGap

open LinearAlgebra.SpectralBooks SiteTensor
open ThreeFlat Routing
open CorrectionFrame CorrectionProducts Catalyst
open scoped Classical BigOperators

private def fiber {I I' J : Type} (e : I ≃ I') (σ : I' → J) (j : J) :
    ({i : I' // σ i = j} → Bool) ≃ ({i : I // (σ ∘ e) i = j} → Bool) where
  toFun x i := x ⟨e i.val,i.property⟩
  invFun y i := y ⟨e.symm i.val,by simpa using i.property⟩
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp

private theorem reindex {I I' J : Type} [Fintype I] [Fintype I'] [Fintype J] [Nonempty J]
    {F : Type*} [Field F] (φ : Point J F) (e : I ≃ I') (σ : I' → J)
    (v : (I' → Bool) → F) :
    value φ σ v = value φ (σ ∘ e) (fun x => v (x ∘ e.symm)) := by
  apply congrArg φ.val
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (fiber e σ)
  intro x
  apply congrArg v
  funext i
  let decode (j : I') := x (σ j) ⟨j,rfl⟩
  change decode i = decode (e (e.symm i))
  rw [e.apply_symm_apply]

variable {F : Type*} [Field F] {k p s : ℕ}

private theorem retained_error (X : Approximation F k p) (f : (Fin p → Bool) → F)
    (L : ℕ) (A : BitNetwork F (Fintype.card (Fin s × Port p X.width)))
    (rows : ∀ x, TypedWiring.value A x = CorrectionAssembly.retained X f L x) :
    (fun x : Fin s × Port p X.width → Bool =>
      ((CorrectionBatch.package X.width A).error (dataProduct s f)).coeff
        (x ∘ (copiesPortEquiv s X.width).symm)) =
      -CorrectionPrice.omitted L (ideal X.width f - X.coeff) X.coeff := by
  funext x
  let e := copiesPortEquiv (p:=p) s X.width
  change (CorrectionBatch.package X.width A).coeff (x ∘ e.symm) -
    ideal (copiesWidth s X.width) (dataProduct s f) (x ∘ e.symm) = _
  erw [CorrectionBatch.coeff_package X.width A (x ∘ e.symm),
    CorrectionBatch.ideal_power X.width f (x ∘ e.symm)]
  have xx : (x ∘ e.symm) ∘ e = x := by funext i; simp
  rw [xx, rows]
  change CorrectionAssembly.retained X f L x -
    (∏ i, ideal X.width f (fun j => x (e.symm (e (i,j))))) = _
  simp only [e.symm_apply_apply, Pi.neg_apply]
  have H := SparseCorrection.split (fun i : Fin s => ideal X.width f (fun j => x (i,j)))
    (fun i => X.coeff (fun a => x (i,a))) L
  change CorrectionAssembly.retained X f L x -
      (∏ i, ideal X.width f (fun j => x (i,j))) = -_
  simpa only [neg_sub,CorrectionAssembly.retained,CorrectionPrice.omitted,Pi.sub_def] using congrArg Neg.neg H

/-- An implemented sparse truncation amplifies the genuine exposed price gap.
The dimension is positive, and the independent product uses exactly the summed
physical widths in each direction. -/
theorem amplified {H D : ℝ} (hk : 0<k) (hH : 1 ≤ H)
    (hD : 4*(k:ℝ)*(Real.logb 2 H+3) ≤ D) (L : ℕ) (copies : (s:ℝ)/H ≤ L+1)
    (X : Approximation F k p) (f : (Fin p → Bool) → F) (gap : X.Gap f D)
    (A : BitNetwork F (Fintype.card (Fin s × Port p X.width)))
    (rows : ∀ x, TypedWiring.value A x = CorrectionAssembly.retained X f L x) :
    (CorrectionBatch.package X.width A).Gap (dataProduct s f) ((s:ℝ)*D/(2*H)) := by
  intro P
  let Y := CorrectionBatch.package X.width A
  let v : (Port (s*p) (copiesWidth s X.width) → Bool) → F := (Y.error (dataProduct s f)).coeff
  by_cases null : v = 0
  · exact Or.inl null
  right
  let : NeZero k := ⟨hk.ne'⟩
  let c := P.price (Raw.diagonal (Location k) F (Fin 2)) (frame k)
  let R := 2*∑ j, (X.width j : ℝ)
  obtain ⟨φ,hc,prices⟩ := P.normalized_group (frame k)
  let σ := location (p := p) (b := X.width)
  let σ' := location (p := s*p) (b := copiesWidth s X.width)
  let e := copiesPortEquiv (p:=p) s X.width
  have Rbudget := CorrectionFrame.scale_le P (k:=k)
  have gain : 2*c*(Real.logb 2 H+3) ≤ D := by
    apply le_trans ?_ hD
    have hh := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hH
    exact mul_le_mul_of_nonneg_right (by dsimp [c]; linarith) (by linarith)
  have logValue (v : (Port p X.width → Bool) → F) (hv : v ≠ 0) :
      P.price (raw v) (sites X.width) = c*Real.logb 2 (value φ σ v) := by
    rw [sites_eq]
    exact prices σ (raw v) hv
  have base (nz : ideal X.width f ≠ 0) : c*Real.logb 2 (value φ σ (ideal X.width f)) ≤ R := by
    rw [← logValue _ nz]
    exact CorrectionBenchmark.price_le P X.width _
  have err (nz : ideal X.width f - X.coeff ≠ 0) :
      c*Real.logb 2 (value φ σ (ideal X.width f-X.coeff)) ≤ R-D := by
    have neg : ideal X.width f-X.coeff = -(X.coeff-ideal X.width f) := by abel
    have nz' : X.coeff-ideal X.width f ≠ 0 := fun eq => nz (by simp [neg,eq])
    rw [neg,value_neg,← logValue _ nz']
    exact (gap P).resolve_left nz'
  have sigs : σ' ∘ e = σ ∘ Prod.snd := funext (copies_location X.width)
  have equal := retained_error X f L A rows
  change (fun x => v (x ∘ e.symm)) = _ at equal
  have grouped : value φ σ' v = value φ (σ ∘ Prod.snd)
      (CorrectionPrice.omitted (s:=s) L (ideal X.width f-X.coeff) X.coeff) := by
    rw [reindex φ e σ' v, sigs, equal, value_neg]
  have nzout : CorrectionPrice.omitted (s:=s) L (ideal X.width f-X.coeff) X.coeff ≠ 0 := by
    intro hz
    rw [hz,value_zero] at grouped
    exact (value_pos φ σ' null).ne' grouped
  have disc := CorrectionPrice.discounted φ σ s L (ideal X.width f) X.coeff hc hH gain copies
    base err nzout
  change P.price (raw v) (sites (copiesWidth s X.width)) ≤ _
  rw [sites_eq]
  change P.price (raw v) (frame k ∘ σ') ≤ _
  rw [prices σ' (raw v) null]
  change c * Real.logb 2 (value φ σ' v) ≤ _
  rw [grouped]
  convert disc using 1
  change 2*(∑ j, ((s*X.width j : ℕ):ℝ)) - _ = (s:ℝ)*R - _
  push_cast
  rw [← Finset.mul_sum]
  dsimp only [R]
  ring

/-- In dimension zero all ports coincide. Any positive discount forces the
one-copy error to vanish, and every discarded summand then vanishes as well. -/
theorem amplified_all {H D : ℝ} (hH : 1 ≤ H)
    (hD : 4*(k:ℝ)*(Real.logb 2 H+3) ≤ D) (L : ℕ) (copies : (s:ℝ)/H ≤ L+1)
    (X : Approximation F k p) (f : (Fin p → Bool) → F) (g : X.Gap f D)
    (A : BitNetwork F (Fintype.card (Fin s × Port p X.width)))
    (rows : ∀ x, TypedWiring.value A x = CorrectionAssembly.retained X f L x) :
    (CorrectionBatch.package X.width A).Gap (dataProduct s f) ((s:ℝ)*D/(2*H)) := by
  rcases Nat.eq_zero_or_pos k with rfl | pos
  · intro P
    have collapsed {n : ℕ} (b : Fin 0 → ℕ) (T : Raw (Port n b) F) :
        P.price T (sites b) = 0 := by
      rw [show sites (p:=n) b = fun _ => 0 from funext (fun _ => Subsingleton.elim _ _)]
      exact P.collapsed _ _
    by_cases dpos : 0 < D
    · left
      have clean : (X.error f).coeff = 0 := (g P).resolve_right (by
        rw [collapsed]; simp; linarith)
      change X.coeff - ideal X.width f = 0 at clean
      have eq := retained_error X f L A rows
      have noErr : ideal X.width f-X.coeff = 0 := sub_eq_zero.mpr (sub_eq_zero.mp clean).symm
      erw [noErr] at eq
      have allzero : CorrectionPrice.omitted (s:=s) L 0 X.coeff = 0 := by
        funext x
        apply Finset.sum_eq_zero
        intro t ht
        have hc := (Finset.mem_filter.mp ht).2
        obtain ⟨j,hj⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le L) hc)
        simp only [SparseCorrection.term,Pi.zero_apply]
        rw [Finset.prod_eq_zero hj (by rfl),zero_mul]
      erw [allzero,neg_zero] at eq
      funext y
      let e := copiesPortEquiv (p:=p) s X.width
      have h := congrFun eq (y ∘ e)
      have back : (y ∘ e) ∘ e.symm = y := by
        funext i
        change y (e (e.symm i))=y i
        rw [e.apply_symm_apply]
      change ((CorrectionBatch.package X.width A).error (dataProduct s f)).coeff ((y ∘ e) ∘ e.symm)=0 at h
      let E : (Port (s*p) (copiesWidth s X.width)→Bool)→F :=
        ((CorrectionBatch.package X.width A).error (dataProduct s f)).coeff
      exact (congrArg E back).symm.trans h
    · right
      rw [collapsed]
      have weak : (s:ℝ)*D/(2*H) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_gt dpos)) (by linarith)
      simpa only [Finset.univ_eq_empty,Finset.sum_empty,mul_zero,zero_sub] using neg_nonneg.mpr weak
  · exact amplified pos hH hD L copies X f g A rows

end Hierarchy.CorrectionGap

end
end OAI
