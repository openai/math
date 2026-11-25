import OAI.Hierarchy.TaggedSortLiftStage
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI
/-! # The cyclic deal in the four-pass column sort

There are `k` source columns of height `k*p`. Source position `r*k+c`
goes to destination column `c`. A threshold cutting a sorted source column
after `a` entries contributes either `a/k` or `a/k+1` entries to each
destination. Once the destination columns are sorted, their row-major order
has a single ambiguous window of at most `k*k` entries.
-/

namespace Hierarchy.Tagged.SortLift

open scoped BigOperators Classical
noncomputable section

def uniformStage {k h n : ℕ} (i o : Fin k × Fin h ≃ Fin n) : Stage n where
  blocks := k
  length _ := h
  input := (Equiv.sigmaEquivProd _ _).trans i
  output := (Equiv.sigmaEquivProd _ _).trans o

def columns (k h : ℕ) : Stage (k*h) := uniformStage finProdFinEquiv finProdFinEquiv

def dealInput (k p : ℕ) : Fin k × Fin (k*p) ≃ Fin (k*(k*p)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm).trans <|
    (Equiv.prodComm _ _).trans <| (Equiv.prodAssoc _ _ _).trans <|
    (Equiv.prodCongr (Equiv.refl _) (finProdFinEquiv.trans (finCongr (Nat.mul_comm p k)))).trans
      finProdFinEquiv

def rowMajor (k h : ℕ) : Fin k × Fin h ≃ Fin (k*h) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm h k)))

def deal (k p : ℕ) : Stage (k*(k*p)) := uniformStage (dealInput k p) (rowMajor k (k*p))

theorem dealInput_apply (k p : ℕ) (c s : Fin k) (r : Fin p) :
    dealInput k p (c,finProdFinEquiv (s,r)) =
      finProdFinEquiv (s,finCongr (Nat.mul_comm p k) (finProdFinEquiv (r,c))) := by
  simp [dealInput]

theorem cutCount_le_card {ι : Type*} [Fintype ι] (P : ι → Prop) :
    cutCount P ≤ Fintype.card ι :=
  (Finset.card_filter_le _ _).trans_eq Finset.card_univ

theorem cutCount_mono {ι : Type*} [Fintype ι] {P Q : ι → Prop} (h : ∀ i, P i → Q i) :
    cutCount P ≤ cutCount Q :=
  Finset.card_le_card fun i hi => Finset.mem_filter.mpr
    ⟨Finset.mem_univ i, h i (Finset.mem_filter.mp hi).2⟩

private theorem cutCount_indicator {ι : Type*} [Fintype ι] (P : ι → Prop) :
    cutCount P = ∑ i, if P i then 1 else 0 := by
  simpa only [cutCount,Nat.cast_id] using (Finset.sum_boole (R := ℕ) P Finset.univ).symm

theorem cutCount_prod {ι β : Type*} [Fintype ι] [Fintype β] (P : ι × β → Prop) :
    cutCount P = ∑ s, cutCount (fun r => P (s,r)) := by
  simp only [cutCount_indicator,Fintype.sum_prod_type]

theorem cutCount_prefix {p b : ℕ} (hb : b ≤ p) :
    cutCount (fun r : Fin p => r.val < b) = b := by
  by_cases h : b < p
  · let stop : Fin p := ⟨b,h⟩
    unfold cutCount
    trans (Finset.Iio stop).card
    · apply congrArg Finset.card
      ext r
      simp [stop,Fin.lt_def]
    · exact Fin.card_Iio _
  · have e : b = p := by omega
    subst b
    simp [cutCount]

theorem residue_count {k p a : ℕ} (hk : 0 < k) (ha : a ≤ k*p) (c : Fin k) :
    a/k ≤ cutCount (fun r : Fin p => c.val + k*r.val < a) ∧
      cutCount (fun r : Fin p => c.val + k*r.val < a) ≤ a/k+1 := by
  have hb : a/k ≤ p := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using ha)
  constructor
  · rw [← cutCount_prefix hb]
    apply cutCount_mono
    intro r hr
    have first : (r.val+1)*k ≤ (a/k)*k := Nat.mul_le_mul_right k hr
    have inside := Nat.div_mul_le_self a k
    have hc := c.isLt
    nlinarith
  · by_cases h : a/k+1 ≤ p
    · rw [← cutCount_prefix h]
      apply cutCount_mono
      intro r hr
      by_contra! far
      have large := Nat.mul_le_mul_right k far
      have inside := Nat.lt_div_mul_add (a := a) hk
      nlinarith
    · exact (cutCount_le_card _).trans (by simp;omega)

variable {α κ : Type*} [LinearOrder κ]

/-- The two block sorts and their fixed deal put every threshold into a
row-major window of width at most `k*k`. -/
theorem deal_window (k p : ℕ) (hk : 0 < k) (key : α → κ) (x : Fin (k*(k*p)) → α) (t : κ) :
    ∃ lo hi : ℕ, hi = lo+k*k ∧
      (∀ i : Fin (k*(k*p)), i.val < lo →
        key ((deal k p).eval key ((columns k (k*p)).eval key x) i) < t) ∧
      (∀ i : Fin (k*(k*p)), hi ≤ i.val →
        ¬key ((deal k p).eval key ((columns k (k*p)).eval key x) i) < t) := by
  let H := k*p
  let first := (columns k H).eval key x
  let A (s : Fin k) := cutCount (fun j : Fin H => key (x (finProdFinEquiv (s,j))) < t)
  let B (c : Fin k) := cutCount (fun j : Fin H => key (first (dealInput k p (c,j))) < t)
  let base := ∑ s, A s/k
  have amax (s : Fin k) : A s ≤ k*p := (cutCount_le_card _).trans (by simp [H])
  have count (c : Fin k) : B c =
      ∑ s : Fin k, cutCount (fun r : Fin p => c.val+k*r.val < A s) := by
    let P (j : Fin H) := key (first (dealInput k p (c,j))) < t
    change cutCount P = _
    rw [← cutCount_equiv (finProdFinEquiv : Fin k × Fin p ≃ Fin H) P,cutCount_prod]
    apply Finset.sum_congr rfl
    intro s _
    apply congrArg cutCount
    funext r
    apply propext
    dsimp only [P]
    rw [dealInput_apply]
    exact (columns k H).lt_cut_iff key x s
      (finCongr (Nat.mul_comm p k) (finProdFinEquiv (r,c))) t
  have bounds (c : Fin k) : base ≤ B c ∧ B c ≤ base+k := by
    rw [count]
    constructor
    · exact Finset.sum_le_sum fun s _ => (residue_count hk (amax s) c).1
    · calc
        _ ≤ ∑ s : Fin k, (A s/k+1) := Finset.sum_le_sum fun s _ => (residue_count hk (amax s) c).2
        _ = base+k := by simp [base,Finset.sum_add_distrib]
  refine ⟨k*base,k*(base+k),by ring,?_,?_⟩
  · intro i
    obtain ⟨⟨c,j⟩, rfl⟩ := (rowMajor k H).surjective i
    intro before
    apply ((deal k p).lt_cut_iff key first c j t).mpr
    change j.val < B c
    apply lt_of_lt_of_le _ (bounds c).1
    change c.val+k*j.val < k*base at before
    by_contra! after
    have := Nat.mul_le_mul_left k after
    omega
  · intro i
    obtain ⟨⟨c,j⟩, rfl⟩ := (rowMajor k H).surjective i
    intro after hit
    have upper : j.val < B c := ((deal k p).lt_cut_iff key first c j t).mp hit
    have next : j.val+1 ≤ base+k := upper.trans_le (bounds c).2
    have := Nat.mul_le_mul_left k next
    change k*(base+k) ≤ c.val+k*j.val at after
    have hc := c.isLt
    nlinarith

end
end Hierarchy.Tagged.SortLift

end OAI
