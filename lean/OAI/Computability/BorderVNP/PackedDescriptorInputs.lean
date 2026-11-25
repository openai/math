import OAI.Computability.BorderVNP.PackedBandLookup
import OAI.Computability.BorderVNP.PackedStableActiveOffsets
import OAI.Computability.BorderVNP.ShortenSeedDescriptorFrozen
import OAI.Computability.BorderVNP.PackedCutCircuit

/-! # Source words for every cut of an actual pack

The cable table uses sparse stable names. Its physical representative has only the occupied
cables, ordered by their row IDs. Combining the stable offsets, scattered band endpoints
and the frozen-tail rule supplies each of the four inputs of the clipping circuit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CutCircuit

open Crossing Shortening Shortening.SeedIntervals ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D M : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (slot : N.Edge ↪ Fin M) {A : Type} (bin : N.Edge → Option A)

/-- The bin labeling transported to the physical dense presentation. -/
noncomputable def denseBin : (Names.denseLayout N slot).Edge → Option A :=
  bin ∘ (Names.denseSlot N slot).symm

/-- The public sparse ID is retained when the real cables are relabeled by dense rank. -/
noncomputable def denseRows : (Names.denseLayout N slot).Edge ↪ Fin M :=
  (Names.denseSlot N slot).symm.toEmbedding.trans slot

/-- No bin width changes when a physical layout is reordered. -/
theorem dense_count (a : A) :
    count (Names.denseLayout N slot) (denseBin N slot bin) a = count N bin a := by
  classical
  rw [count_eq_sum,count_eq_sum,← (Names.denseSlot N slot).sum_comp]
  apply Finset.sum_congr rfl
  intro e _
  change (if bin ((Names.denseSlot N slot).symm (Names.denseSlot N slot e)) = some a
      then (Names.denseLayout N slot).width (Names.denseSlot N slot e) else 0) = _
  rw [Equiv.symm_apply_apply]
  split_ifs
  · exact Names.width_slot N _ _ e
  · rfl

/-- Sparse occupied/charged input rows represent the reordered physical layout as well. -/
theorem dense_represents {σ : Type*} {k w : ℕ} (p : PublicPopulation.Pins (Fin M) σ k w)
    (code : A ↪ Fin (2^k)) (x : σ → Bool) (h : PublicPopulation.Represents p N bin slot code x) :
    PublicPopulation.Represents p (Names.denseLayout N slot) (denseBin N slot bin)
      (denseRows N slot) code x where
  active e := h.active _
  absent u hu := h.absent u (fun ⟨e,he⟩ => hu ⟨Names.denseSlot N slot e,by
    simpa [denseRows] using he⟩)
  address e a he := h.address _ a he
  width e a he := (h.width _ a he).trans (by
    obtain ⟨f,rfl⟩ := (Names.denseSlot N slot).surjective e
    rw [Equiv.symm_apply_apply]
    exact (Names.width_slot N _ _ f).symm)

/-- Both charged and frozen rows produce one actual cut descriptor in public ID order. -/
noncomputable def liveDescriptor [NeZero D] (perm : Fin D → Equiv.Perm A) (m : ℕ)
    (names : A → ℕ) (e : N.Edge) (b : Band D) : CutDescriptor :=
  let L := Names.denseLayout N slot
  let c := Names.denseSlot N slot e
  match hb : bin e with
  | none => frozenDescriptor L 0 c b
  | some a => descriptor L (denseBin N slot bin) perm m names
      (⟨c,by simpa [c,denseBin] using hb⟩ : {c // denseBin N slot bin c = some a}) b

/-- An uncharged physical cable uses the intact tail descriptor. -/
theorem live_frozen [NeZero D] (perm : Fin D → Equiv.Perm A) (m : ℕ) (names : A → ℕ)
    (e : N.Edge) (h : bin e = none) (b : Band D) :
    liveDescriptor N slot bin perm m names e b =
      frozenDescriptor (Names.denseLayout N slot) 0 (Names.denseSlot N slot e) b := by
  unfold liveDescriptor
  split
  · rfl
  · rename_i a ha
    cases h.symm.trans ha

/-- A charged physical cable receives the descriptor of its actual labeled bin. -/
theorem live_charged [NeZero D] (perm : Fin D → Equiv.Perm A) (m : ℕ) (names : A → ℕ)
    (e : N.Edge) (a : A) (h : bin e = some a) (b : Band D) :
    liveDescriptor N slot bin perm m names e b =
      descriptor (Names.denseLayout N slot) (denseBin N slot bin) perm m names
        (⟨Names.denseSlot N slot e,by simpa only [denseBin,Function.comp_apply,Equiv.symm_apply_apply] using h⟩ :
          {c // denseBin N slot bin c = some a}) b := by
  unfold liveDescriptor
  split
  · rename_i ha
    cases ha.symm.trans h
  · rename_i a' ha
    obtain rfl := Option.some.inj (h.symm.trans ha)
    rfl

/-- The offset of a live cable plus its own width fits in its bin. -/
theorem offset_width_le (a : A) (e : N.Edge) (h : bin e = some a) :
    cableOffset N bin a e + N.width e ≤ count N bin a := by
  classical
  rw [cableOffset_eq_sum,count_eq_sum]
  have hsingle : N.width e = ∑ f : N.Edge, if f = e then N.width f else 0 := by simp
  conv_lhs => rhs; rw [hsingle]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro f _
  by_cases he : f = e
  · subst f
    simp [h]
  · by_cases hb : bin f = some a <;> by_cases ht : cableName N f < cableName N e <;> simp [he,hb,ht]

/-- No cut extends past the input bin, including when one of its direction pools is empty. -/
theorem bandEnd_le {D : ℕ} (n : ℕ) (take : Fin D → ℕ) (h : ∀ d, take d ≤ n/D)
    (b : Band D) (r : Bool) : PoolCircuit.bandEnd n (n/D) take b r ≤ n := by
  have hD : D*(n/D) ≤ n := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self n D
  have hx (k : ℕ) (hk : k ≤ D) : k*(n/D) ≤ n := (Nat.mul_le_mul_right _ hk).trans hD
  have hs (d : Fin D) : d.val*(n/D)+take d ≤ n :=
    (Nat.add_le_add_left (h d) _).trans ((Nat.succ_mul d.val (n/D)) ▸ hx _ d.isLt)
  rcases b with _ | ⟨d,t⟩
  · cases r
    · exact hD
    · exact le_rfl
  · cases t <;> cases r
    · exact hs d
    · exact hx _ d.isLt
    · exact hx _ d.isLt.le
    · exact hs d

/-- Every live row fits the word width whenever bin totals and individual cable widths fit. -/
theorem live_fits [NeZero D] (perm : Fin D → Equiv.Perm A) (m w : ℕ) (names : A → ℕ)
    (fit : ∀ a, count N bin a < 2^w) (e : N.Edge) (he : N.width e < 2^w) (b : Band D) :
    let d := liveDescriptor N slot bin perm m names e b
    d.start + d.width < 2^w ∧ d.lo < 2^w ∧ d.hi < 2^w := by
  let L := Names.denseLayout N slot
  let c := Names.denseSlot N slot e
  let f := denseBin N slot bin
  have hw : L.width c = N.width e := Names.width_slot N _ _ e
  cases hb : bin e with
  | none =>
    dsimp only
    rw [live_frozen N slot bin perm m names e hb b]
    change 0 + L.width c < 2^w ∧ 0 < 2^w ∧ (if b.isNone then L.width c else 0) < 2^w
    rw [Nat.zero_add,hw]
    exact ⟨he,Nat.two_pow_pos _,by split <;> first | exact he | exact Nat.two_pow_pos _⟩
  | some a =>
    have ha : f c = some a := by simpa only [f,c,denseBin,Function.comp_apply,Equiv.symm_apply_apply] using hb
    have hc : count L f a < 2^w := (dense_count N slot bin a).trans_lt (fit a)
    let cuts := bandCuts (count L f a) (count L f a / D) (take L f perm m a) b
    dsimp only
    rw [live_charged N slot bin perm m names e a hb b]
    change cableOffset L f a c + L.width c < 2^w ∧ cuts.1 < 2^w ∧ cuts.2 < 2^w
    exact ⟨(offset_width_le L f a c ha).trans_lt hc,
      (bandEnd_le _ _ (take_le L f perm m a) b false).trans_lt hc,
      (bandEnd_le _ _ (take_le L f perm m a) b true).trans_lt hc⟩

end Packing.CutCircuit

end BorderVNP
end Computability
end OAI
