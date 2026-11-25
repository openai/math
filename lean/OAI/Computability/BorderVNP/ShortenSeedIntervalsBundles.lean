import OAI.Computability.BorderVNP.ShortenSeedIntervals
import OAI.Computability.BorderVNP.ShortenBundleCost

/-!
# The common matched ordinals and actual seed bundles

A matched physical cable is exactly one prefix of an old cable in the seed's
permuted bin. Concatenate the pieces by their old cable names. At both
terminals the resulting word uses the same ordinal in the same pool prefix.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing
open scoped Classical BigOperators

variable {D : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {A : Type} (bin : N.Edge → Option A) (perm : Fin D → Equiv.Perm A) (m : ℕ)

/-- Direction field in a physical band name, used only on selected prefixes. -/
def direction (b : Band D) : Fin D := b.elim 0 Prod.fst

/-- Select exactly the matched prefixes in the seed's `D` permuted bins. -/
noncomputable def partition : AddressPartition (layout N bin perm m) A where
  part a := Finset.univ.filter fun c =>
    c.2 = some (direction c.2, true) ∧ bin c.1 = some (perm (direction c.2) a)
  unique := by
    intro a b c h₁ h₂
    have h := (Finset.mem_filter.mp h₁).2.2.symm.trans (Finset.mem_filter.mp h₂).2.2
    exact (perm (direction c.2)).injective (Option.some.inj h)

/-- Every selected old cable belongs to the correct permuted bin. -/
theorem bin_selected {a : A} (e : ↥((partition N bin perm m).part a)) :
    bin e.val.1 = some (perm (direction e.val.2) a) := (Finset.mem_filter.mp e.property).2.2

private abbrev AxisEdges (a : A) (d : Fin D) :=
  {e : ↥((partition N bin perm m).part a) // direction e.val.2 = d}

private noncomputable def selectedEquiv (a : A) (d : Fin D) :
    {e : N.Edge // bin e = some (perm d a)} ≃ AxisEdges N bin perm m a d where
  toFun e := ⟨⟨(e.val, some (d,true)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, e.property⟩⟩, rfl⟩
  invFun e := ⟨e.val.val.1, (bin_selected N bin perm m e.val).trans (by rw [e.property])⟩
  left_inv _ := rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    change (e.val.val.1, some (d,true)) = e.val.val
    refine Prod.ext (by rfl) ?_
    have h := (Finset.mem_filter.mp e.val.property).2.1
    rw [e.property] at h
    exact h.symm

private noncomputable def oldPrefix (a : A) (d : Fin D) :
    (Σ e : {c : N.Edge // bin c = some (perm d a)},
      N.BandBits (label N bin perm m) e.val (some (d,true))) ≃
    {t : BinBits N bin (perm d a) // label N bin perm m t.1.val t.2 = some (d,true)} where
  toFun t := ⟨⟨t.1,t.2.val⟩,t.2.property⟩
  invFun t := ⟨t.val.1,⟨t.val.2,t.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def orderedPrefix (a : A) (d : Fin D) :
    (Σ e : {e : N.Edge // bin e = some (perm d a)},
      Fin ((layout N bin perm m).width (e.val, some (d,true)))) ≃ Fin (blocks N bin perm m a * m) := by
  let c := perm d a
  let toBits := Equiv.sigmaCongrRight fun (e : {c' : N.Edge // bin c' = some c}) =>
    (N.bandOrder (label N bin perm m) e.val (some (d,true))).toEquiv
  let toRank := (rank N bin c).subtypeEquiv (p := fun t =>
      label N bin perm m t.1.val t.2 = some (d,true))
    (q := fun k => poolLabel (count N bin c / D) (take N bin perm m c) k.val = some (d,true))
    fun t => by rw [label_at N bin perm m t.1 t.2]
  let toPrefix := prefixOrder (take_le N bin perm m c)
    (Nat.mul_div_le (count N bin c) D) d
  exact toBits.trans ((oldPrefix N bin perm m a d).trans (toRank.trans
    (toPrefix.trans (finCongr (by simp [take, c, common])))))

/-- The matched prefix of an actual old cable, regarded as a selected interval in this direction. -/
noncomputable def prefixEdge (a : A) (d : Fin D) (e : {e : N.Edge // bin e = some (perm d a)}) :
    {z : ↥((partition N bin perm m).part a) // direction z.val.2 = d} :=
  selectedEquiv N bin perm m a d e

/-- One seed's bundle, with the common integer prefix ordinal used at both ends. -/
noncomputable def bundle (positive : N.Edge → Bool) (a : A) :
    Bundle (layout N bin perm m) ((partition N bin perm m).part a) (blocks N bin perm m a * m) where
  axis e := direction e.val.2
  positive e := positive e.val.1
  order d :=
    let W := fun e : AxisEdges N bin perm m a d => Fin ((layout N bin perm m).width e.val.val)
    (Equiv.sigmaCongrLeft (β := W) (selectedEquiv N bin perm m a d)).symm.trans
      (orderedPrefix N bin perm m a d)

/-- At a matched prefix the joint terminal reads the old sorted bit ordinal minus the pool start. -/
theorem bundle_order_rank (positive : N.Edge → Bool) (a : A) (d : Fin D)
    (e : {e : N.Edge // bin e = some (perm d a)})
    (k : Fin ((layout N bin perm m).width (e.val,some (d,true)))) :
    ((bundle N bin perm m positive a).order d ⟨prefixEdge N bin perm m a d e,k⟩).val =
      (rank N bin (perm d a) ⟨e, (N.bandOrder (label N bin perm m) e.val (some (d,true)) k).val⟩).val -
        d.val * (count N bin (perm d a) / D) := by
  let W := fun e : AxisEdges N bin perm m a d => Fin ((layout N bin perm m).width e.val.val)
  let push := Equiv.sigmaCongrLeft (β := W) (selectedEquiv N bin perm m a d)
  change (orderedPrefix N bin perm m a d (push.symm (push ⟨e,k⟩))).val = _
  rw [push.symm_apply_apply]
  unfold orderedPrefix
  rfl

/-- Charged length selected by all seeds equals the sum of their matched bit counts times lengths. -/
theorem selectedLength_eq [Fintype A] {H : Type*} [PseudoMetricSpace H]
    (place : N.Site → H) (length : A → ℝ)
    (hℓ : ∀ e c, bin e = some c → dist (place (N.src e)) (place (N.dst e)) = length c)
    (hperm : ∀ d a, length (perm d a) = length a) :
    Epoch.selectedLength (layout N bin perm m) place (partition N bin perm m).selected =
      ∑ a, length a * Epoch.pooledBits m (fun d : Fin D => count N bin (perm d a)) := by
  let t := partition N bin perm m
  let L := layout N bin perm m
  let weight := fun e : ↥t.selected =>
    (L.width e.val : ℝ) * dist (place (L.src e.val)) (place (L.dst e.val))
  change (∑ e : ↥t.selected, weight e) = _
  rw [← t.edgeIndex.sum_comp weight, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  have hdist (e : ↥(t.part a)) :
      dist (place (L.src e.val)) (place (L.dst e.val)) = length a :=
    (hℓ _ _ (bin_selected N bin perm m e)).trans (hperm _ _)
  change (∑ e : ↥(t.part a), (L.width e.val : ℝ) *
    dist (place (L.src e.val)) (place (L.dst e.val))) = _
  simp_rw [hdist]
  rw [← Finset.sum_mul, ← Nat.cast_sum, pooledBits_eq]
  rw [(bundle N bin perm m (fun _ => true) a).totalWidth]
  exact mul_comm _ _

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
