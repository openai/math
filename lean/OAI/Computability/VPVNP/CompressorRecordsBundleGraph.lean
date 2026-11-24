import OAI.Computability.VPVNP.CompressorRecordsBundleScan
import OAI.Computability.VPVNP.CompressorRecordsBundleWords
import OAI.Computability.VPVNP.CompressorRecordsBundleLists

/-!
# Classification of all actual old arcs in a shrinking pass

The complete native scan assigns every absolute outgoing slot to its thick-wire
or CD bundle and writes its relative sorting key. Distinct parallel wires retain
their original array indices. The combined bucket column can serve immediately
as the owner array of the bounded-append pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleRAM

open Compression BurstRAM PrimedStackRAM BundleKeys
open scoped Fin.CommRing

variable {V : Type} {n a g w : ℕ}
variable (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g))) (order : V ≃ Fin n)
local notation "P" => orderedDyadicPacking G order
local notation "A" => n*2^(packingLaneBits a g)*2^a

/-- Test whether both endpoints of an old arc are thick under the shrinking placement, making
the arc a thick payload wire. -/
def bothThick (e : OldArc V a g) : Bool :=
  decide ((P).thick (sourcePosition e) ∧ (P).thick (sourcePosition ((P).actual e)))

private theorem bucket_number (layout : Bool) (e : OldArc V a g) :
    bucketFromRows (numBundles n a g) (2^a) e.1.2.val
      (siteRow G order layout (sourcePosition e))
      (siteRow G order layout (sourcePosition ((P).actual e))) =
      (BundleLists.bucketIndex (Shrink.packedIndex order) (BundleLists.bucketOf P e)).val := by
  by_cases h : (P).thick (sourcePosition e) ∧ (P).thick (sourcePosition ((P).actual e))
  · let wire : (P).ThickWire := ⟨e,h⟩
    rw [thick_bucket G order layout wire, BundleLists.bucketOf_thick P wire,
      BundleLists.bucketIndex_thick_val, Shrink.packedIndex_val]
    rfl
  · let m : (P).Motif := ⟨e,h⟩
    rw [motif_bucket G order layout m, BundleLists.bucketOf_motif P m,
      BundleLists.bucketIndex_motif_val, Shrink.packedIndex_val]
    rfl

private theorem key_fits (e : OldArc V a g) : keyAt order (bothThick G order e) e < A := by
  let C := Shrink.colors a
  let J := Shrink.J a
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.zero_lt_of_lt (order e.1.1.1).isLt)
  have hA : A = n * 2^J * 2^a * (2^C * 2^a) * 2^g := by
    simp only [packingLaneBits, pow_add, C, J, Shrink.colors, Shrink.J]; ring
  rw [hA]
  unfold bothThick
  by_cases h : (P).thick (sourcePosition e) ∧ (P).thick (sourcePosition ((P).actual e))
  · let wire : (P).ThickWire := ⟨e,h⟩
    let fib : (P).ThickFiber e.1 := ⟨wire,rfl⟩
    rw [decide_eq_true h, thick_key G order e.1 fib]
    exact (Fin.isLt _).trans_le ((Nat.le_mul_of_pos_left _ (by positivity :
      0 < n*2^J*2^a)).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g)))
  · let m : (P).Motif := ⟨e,h⟩
    rw [decide_eq_false h, motif_key G order m]
    have hk := ((P).baseMotifIndex order (bitWordFinEquiv J) ((P).baseMotif m)).isLt
    apply hk.trans_le
    exact (show n*(2^J*(2^a*(2^C*2^a))) = n*2^J*2^a*(2^C*2^a) by ring).le.trans
      (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g))

/-- Numerical bucket and key columns indexed by the original absolute arc number. -/
structure Classified (p : Fin 11 → Word w) (m : Memory w) : Prop where
  owner : ∀ (i : Word w), i.val < A → m (p 9+i).val =
    BundleLists.wordOwner P (oldArcOrder order) (Shrink.packedIndex order) i
  key : ∀ e : OldArc V a g, (m (p 10 + Fin.ofNat _ (oldArcOrder order e).val).val).val =
    keyAt order (bothThick G order e) e

/-- The typed key is the bounded mask/slot key on the entire thick fiber. -/
theorem Classified.thick_key {p : Fin 11 → Word w} {m : Memory w} (h : Classified G order p m)
    (b : Shrink.Packed V a g × Fin (2^a)) (z : (P).ThickFiber b) :
    (m (p 10 + Fin.ofNat _ (oldArcOrder order z.val.val).val).val).val = ((P).thickFiberIndex b z).val := by
  rw [h.key, show bothThick G order z.val.val = true from decide_eq_true z.val.property]
  exact BundleKeys.thick_key G order b z

/-- All motif keys are indexed using the zero-residual-lane representative of the CD arc. -/
theorem Classified.motif_key {p : Fin 11 → Word w} {m : Memory w} (h : Classified G order p m)
    (z : (P).Motif) :
    (m (p 10 + Fin.ofNat _ (oldArcOrder order z.val).val).val).val =
      ((P).baseMotifIndex order (bitWordFinEquiv (Shrink.J a)) ((P).baseMotif z)).val := by
  rw [h.key, show bothThick G order z.val = false from decide_eq_false z.property]
  exact BundleKeys.motif_key G order z

theorem classified_run (p : Fin 11 → Word w) (layout : Bool) (m : Memory w)
    (hp : Params p a (Shrink.colors a) (Shrink.J a) g (numBundles n a g))
    (regions : Regions p m A)
    (read : ∀ e : OldArc V a g, ∀ i : Word w, i.val = (oldArcOrder order e).val →
      ReadsPlacement p m i (siteRow G order layout (sourcePosition e))
        (siteRow G order layout (sourcePosition ((P).actual e)))) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program (1+visit.length) (some (Fin.ofNat _ 0)) m
        (List.replicate A []) = some rs ∧ ScanResult p A 0 A m rs ∧
      Classified G order p (after m (eventLog rs)) := by
  intro M
  obtain ⟨rs,he,h⟩ := scan_run p A 0 A m regions (by omega)
  refine ⟨rs,he,h,⟨?_,?_⟩⟩
  · intro i hi
    let e := (oldArcOrder order).symm ⟨i.val,hi⟩
    have hv : i.val = (oldArcOrder order e).val :=
      (congrArg Fin.val ((oldArcOrder order).apply_symm_apply ⟨i.val,hi⟩)).symm
    have hc := (classify_oldArc order hp e hv (read e i hv)).1
    rw [bucket_number G order layout e] at hc
    change after m (eventLog rs) (outAddr p 0 i) = _
    rw [h.readback 0 i (Nat.zero_le _) (by simpa only [Nat.zero_add] using hi)]
    change bucket p m i = _
    exact hc.trans (by simp [BundleLists.wordOwner, encodedPlacement, hi,e])
  · intro e
    let i := Fin.ofNat (2^w) (oldArcOrder order e).val
    have hv : i.val = (oldArcOrder order e).val :=
      Nat.mod_eq_of_lt ((oldArcOrder order e).isLt.trans_le regions.fits)
    have hi : i.val < 0 + A := by rw [hv, Nat.zero_add]; exact Fin.isLt _
    change (after m (eventLog rs) (outAddr p 1 i)).val = _
    rw [h.readback 1 i (Nat.zero_le _) hi]
    change (key p m i).val = _
    rw [(classify_oldArc order hp e hv (read e i hv)).2]
    have hb : ((siteRow G order layout (sourcePosition e)).thick &&
        (siteRow G order layout (sourcePosition ((P).actual e))).thick) =
          bothThick G order e := by simp [siteRow, bothThick]
    rw [hb]
    exact Nat.mod_eq_of_lt ((key_fits G order e).trans_le regions.fits)

end CompressorRecords.BundleRAM

end VPVNP
end Computability
end OAI
