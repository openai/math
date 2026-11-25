import OAI.Computability.BorderVNP.ShortenSeedIntervalsNetwork
import OAI.Computability.BorderVNP.ShortenSeedIntervalsPools
import OAI.Computability.BorderVNP.ShortenAddressPartition
import Mathlib.Data.Sigma.Order

/-!
# Allocating the actual intervals at every seed

Within each bin the charged bits are numbered in lexicographic cable-name
and bit-ordinal order. Direction `i` uses pool `i` of the permuted bin, with
one common, whole-block prefix at every direction. An uncharged cable uses
only its tail.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing
open scoped Classical BigOperators

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {A : Type} (bin : N.Edge → Option A)

/-- The charged bits in a bin, tagged by their public old cable name. -/
abbrev BinBits (a : A) := Σ e : {c : N.Edge // bin c = some a}, Fin (N.width e.val)

/-- Integral bin population before any pool cuts. -/
noncomputable def count (a : A) := Fintype.card (BinBits N bin a)

/-- The population counts all and only the widths of the bin's old cables. -/
theorem count_eq_sum (a : A) : count N bin a = ∑ e, if bin e = some a then N.width e else 0 := by
  unfold count BinBits
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun e => bin e = some a) _ (fun e => by simp) N.width]

private noncomputable abbrev cableOrder : LinearOrder N.Edge :=
  LinearOrder.lift' (Fintype.equivFin N.Edge) (Fintype.equivFin N.Edge).injective

attribute [local instance] cableOrder

/-- Enumerate all the bin's bits, with each cable consecutive and its bits increasing. -/
noncomputable def rank (a : A) : BinBits N bin a ≃ Fin (count N bin a) :=
  (Fintype.orderIsoFinOfCardEq (Lex (BinBits N bin a)) rfl).symm.toEquiv

/-- The bin numbering is increasing on every old cable. -/
theorem rank_mono (a : A) (e : {c : N.Edge // bin c = some a}) :
    Monotone fun k : Fin (N.width e.val) => (rank N bin a ⟨e,k⟩).val := by
  intro k l h
  apply (Fintype.orderIsoFinOfCardEq (Lex (BinBits N bin a)) rfl).symm.monotone
  exact Sigma.Lex.right _ _ h

variable [NeZero D] (perm : Fin D → Equiv.Perm A) (m : ℕ)

/-- Number of whole width-`m` blocks available on every direction of a seed. -/
noncomputable def blocks (a : A) : ℕ :=
  Epoch.leastCount (fun i : Fin D => count N bin (perm i a) / D) / m

/-- Actual width selected by the seed in each of its bins. -/
noncomputable def common (a : A) : ℕ := blocks N bin perm m a * m

/-- Total matched width is precisely the pooled-bit count used in (6.3). -/
theorem pooledBits_eq (a : A) :
    Epoch.pooledBits m (fun i : Fin D => count N bin (perm i a)) = D * common N bin perm m a := by
  simp [Epoch.pooledBits, common, blocks, Nat.mul_comm]

/-- Width per direction, expressed as pooled bits divided by the dimension. -/
theorem common_eq_pooled_div (a : A) :
    common N bin perm m a = Epoch.pooledBits m (fun i : Fin D => count N bin (perm i a)) / D := by
  rw [pooledBits_eq, Nat.mul_div_cancel_left _ (NeZero.pos D)]

/-- Length of the prefix selected in pool `i` of actual bin `c`. -/
noncomputable def take (c : A) (i : Fin D) : ℕ := common N bin perm m ((perm i).symm c)

/-- Every matched prefix fits inside its own direction pool. -/
theorem take_le (c : A) (i : Fin D) : take N bin perm m c i ≤ count N bin c / D := by
  let a := (perm i).symm c
  let f := fun j : Fin D => count N bin (perm j a) / D
  have hmin : Epoch.leastCount f ≤ f i :=
    Finset.min'_le _ _ (Finset.mem_image_of_mem f (Finset.mem_univ i))
  exact (Nat.div_mul_le_self (Epoch.leastCount f) m).trans (by simpa [f, a] using hmin)

/-- Physical band containing one bit of one old cable. -/
noncomputable def label (e : N.Edge) (k : Fin (N.width e)) : Band D :=
  match h : bin e with
  | none => none
  | some c => poolLabel (count N bin c / D) (take N bin perm m c)
      (rank N bin c ⟨⟨e,h⟩, k⟩).val

/-- On a charged cable the bit's pool is read from its sorted bin ordinal. -/
theorem label_at {c : A} (e : {e : N.Edge // bin e = some c}) (k : Fin (N.width e.val)) :
    label N bin perm m e.val k = poolLabel (count N bin c / D) (take N bin perm m c)
      (rank N bin c ⟨e,k⟩).val := by
  unfold label
  split
  · rename_i he
    cases he.symm.trans e.property
  · rename_i b he
    obtain rfl := Option.some.inj (he.symm.trans e.property)
    rfl

private theorem label_none (e : N.Edge) (h : bin e = none) (k : Fin (N.width e)) :
    label N bin perm m e k = none := by
  unfold label
  split
  · rfl
  · rename_i b he
    cases he.symm.trans h

/-- The split layout has a matched and residual band per direction and one tail per cable. -/
noncomputable abbrev layout := N.bands (label N bin perm m)

/-- The number of pieces per old cable is bounded independently of its bit width. -/
theorem card_layout : Fintype.card (layout N bin perm m).Edge = Fintype.card N.Edge * (2 * D + 1) := by
  change Fintype.card (N.Edge × Band D) = _
  simp [Band, Nat.mul_comm]

/-- Each old cable has exactly one available piece name per band, including empty pieces. -/
theorem pieces_per_cable (e : N.Edge) :
    Fintype.card {c : (layout N bin perm m).Edge // c.1 = e} = 2 * D + 1 := by
  let E : {c : (layout N bin perm m).Edge // c.1 = e} ≃ Band D := {
    toFun c := c.val.2
    invFun b := ⟨(e,b), rfl⟩
    left_inv c := by
      rcases c with ⟨⟨u,b⟩,h⟩
      change u = e at h
      subst u
      rfl
    right_inv _ := rfl }
  simpa [Band, Nat.mul_comm] using Fintype.card_congr E

/-- At either endpoint every band is a single contiguous interval of old bit ordinals. -/
theorem label_convex (e : N.Edge) {k l t : Fin (N.width e)} (hkl : k ≤ l) (hlt : l ≤ t)
    {band : Band D} (hk : label N bin perm m e k = band) (ht : label N bin perm m e t = band) :
    label N bin perm m e l = band := by
  cases h : bin e with
  | none => exact (label_none N bin perm m e h l).trans ((label_none N bin perm m e h k).symm.trans hk)
  | some c =>
    let e' : {e : N.Edge // bin e = some c} := ⟨e,h⟩
    rw [label_at N bin perm m e' k] at hk
    rw [label_at N bin perm m e' t] at ht
    rw [label_at N bin perm m e' l]
    have h₁ := rank_mono N bin c e' hkl
    have h₂ := rank_mono N bin c e' hlt
    cases band with
    | none => rw [poolLabel_tail (take_le N bin perm m c)] at hk ⊢; exact hk.trans h₁
    | some z =>
      rcases z with ⟨i,b⟩
      cases b
      · rw [poolLabel_residual (take_le N bin perm m c)] at hk ht ⊢
        exact ⟨hk.1.trans h₁, h₂.trans_lt ht.2⟩
      · rw [poolLabel_prefix (take_le N bin perm m c)] at hk ht ⊢
        exact ⟨hk.1.trans h₁, h₂.trans_lt ht.2⟩

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
