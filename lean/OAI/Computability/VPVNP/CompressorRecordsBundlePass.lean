import OAI.Computability.VPVNP.CompressorRecordsBundleGraph
import OAI.Computability.VPVNP.CompressorRecordsBundleInputs
import OAI.Computability.VPVNP.CompressorSlotFrames

/-!
# Native classification and list construction in a shrinking pass

The classification worker follows the old graph's outgoing incidence and reads
both endpoints' placement rows. Its owner output supplies the physical input of
the bounded-append worker. The two passes together charge fourteen calls plus
probes per old outgoing port. Widths remain indexed by these same absolute IDs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleRAM

open BurstRAM PrimedStackRAM Compression BundleKeys

variable {w a g : ℕ}
variable (X : State a (packingLaneBits a g))
local notation "N" => Fintype.card X.Base
local notation "A" => N * 2^(packingLaneBits a g) * 2^a

/-- Complete classification from the two constructed directories, with the precise
source width still addressable by old absolute ID wherever the width column is
reserved outside the two new columns. -/
theorem classify_directory (T : IncidenceDirectory w) (p : Fin 11 → Word w)
    (shrPub : Fin 14 → Word w) (layout : Bool) (m : Memory w)
    (inc : T.ActualColumns X m) (placement : ShrinkRAM.PlacementColumns X.slots X.baseIndex shrPub layout m)
    (hp : Params p a (Shrink.colors a) (Shrink.J a) g (numBundles N a g)) (reg : Regions p m A)
    (hOut : p 5 = T.actualOut) (hThick : p 6 = shrPub 11) (hOwner : p 7 = shrPub 10)
    (hAssigned : p 8 = shrPub 12) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program (1+visit.length) (some (Fin.ofNat _ 0)) m (List.replicate A []) = some rs ∧
      ScanResult p A 0 A m rs ∧ Classified X.slots X.baseIndex p (after m (eventLog rs)) :=
  classified_run X.slots X.baseIndex p layout m hp reg fun e _ hi ↦
    ReadsPlacement.of_directory X T inc placement hp.degree hOut hThick hOwner hAssigned reg.fits e hi

theorem ScanResult.width_at {p : Fin 11 → Word w} {m : Memory w} {rs : List (Report w)}
    (h : ScanResult p A 0 A m rs) (T : IncidenceDirectory w) (inc : T.ActualColumns X m)
    (apart : ∀ e : OldArc X.Base a g, ∀ t : Fin 2, ∀ i : Word w, i.val < A →
      (T.width + Fin.ofNat _ (oldArcOrder X.baseIndex e).val).val ≠ outAddr p t i)
    (e : OldArc X.Base a g) :
    after m (eventLog rs) (T.width + Fin.ofNat _ (oldArcOrder X.baseIndex e).val).val =
      Fin.ofNat _ (X.packingWidth e) := by
  rw [h.preserve _ (fun t i _ hi ↦ apart e t i (by simpa only [Nat.zero_add] using hi))]
  have he : Fin.ofNat (2^w) (oldArcOrder X.baseIndex e).val =
      IncidenceDirectory.actualPort X (packingInputEdges X.Base a g e) := by
    rw [oldArcOrder_val, Shrink.oldNumber_original]
    rfl
  rw [he]; exact inc.width (packingInputEdges X.Base a g e)

/-- The classifier's bucket column supplies every owner word needed to append all
old arc IDs. The combined cost uses the same old-port count for both passes. -/
theorem classify_and_collect (T : IncidenceDirectory w) (p : Fin 11 → Word w)
    (shrPub : Fin 14 → Word w) (layout : Bool) (m : Memory w)
    (inc : T.ActualColumns X m) (placement : ShrinkRAM.PlacementColumns X.slots X.baseIndex shrPub layout m)
    (hp : Params p a (Shrink.colors a) (Shrink.J a) g (numBundles N a g)) (reg : Regions p m A)
    (hOut : p 5 = T.actualOut) (hThick : p 6 = shrPub 11) (hOwner : p 7 = shrPub 10)
    (hAssigned : p 8 = shrPub 12) (q : Fin 6 → Word w) (qreg : RowRegions q)
    (hinput : q 1 = p 9) (hA : (q 0).val = A)
    (hcount : (q 2).val = numBundles N a g + numBundles N a g)
    (hcap : PackingData.pieceCount (2^a) (Shrink.colors a) ≤ (q 4).val)
    (zero : ∀ u : Word w, u < q 2 → m (countAt q u).val = 0)
    (apart : ∀ u : Word w, u < q 2 → ∀ t : Fin 2, ∀ i : Word w, i.val < A →
      (countAt q u).val ≠ outAddr p t i) :
    let M := (template visit 0).instantiate w p
    let L := (template collectPreimage 3).instantiate w q
    let arcs := oldArcOrder (a := a) (g := g) X.baseIndex
    let sites := Shrink.packedIndex (a := a) (g := g) X.baseIndex
    ∃ rs ls, runSegment M.program (1+visit.length) (some (Fin.ofNat _ 0)) m (List.replicate A []) = some rs ∧
      runSegment L.program 23 (some 0) (after m (eventLog rs)) (List.replicate A []) = some ls ∧
      ScanResult p A 0 A m rs ∧ Classified X.slots X.baseIndex p (after m (eventLog rs)) ∧
      PreimagesAt q (BundleLists.wordOwner X.packingData arcs sites)
        (after (after m (eventLog rs)) (eventLog ls)) A ∧
      (∀ addr, OutsidePreimageWrites q addr →
        after (after m (eventLog rs)) (eventLog ls) addr = after m (eventLog rs) addr) ∧
      (∀ b : BundleLists.Bucket X.Base (BitWord (Shrink.J a)) (BitWord g) (2^a),
        let u := Fin.ofNat (2^w) (BundleLists.bucketIndex sites b).val
        rowRepresents (after (after m (eventLog rs)) (eventLog ls)) (countAt q u) (rowAt q u)
          (BundleLists.arcList X.packingData arcs sites b)) ∧
      RAMBuckets.cost Report.probes rs + RAMBuckets.cost Report.probes ls = 14*A := by
  classical
  intro M L arcs sites
  obtain ⟨rs,he,hr,hc⟩ := classify_directory X T p shrPub layout m inc placement hp reg hOut hThick hOwner hAssigned
  let afterClass := after m (eventLog rs)
  have owners (i : Word w) (hi : i < q 0) :
      ownerAt q afterClass i = BundleLists.wordOwner X.packingData arcs sites i := by
    unfold ownerAt; rw [hinput]
    exact hc.owner i (hA ▸ hi)
  have zeros (u : Word w) (hu : u < q 2) : afterClass (countAt q u).val = 0 :=
    (hr.preserve _ (fun t i _ hi ↦ apart u hu t i (by simpa only [Nat.zero_add] using hi))).trans (zero u hu)
  have hcolors : 2 ≤ Shrink.colors a := by unfold Shrink.colors; have := Nat.two_pow_pos a; omega
  obtain ⟨ls,hl,hpre,hrows,_,hcost,_⟩ := BundleLists.fill_run X.packingData arcs sites hcolors
    q qreg hA hcount hcap afterClass owners zeros
  refine ⟨rs,ls,he,hl,hr,hc,hpre,(collectPreimages_cursor_frame (k := 0) qreg hl).2,hrows,?_⟩
  change RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs + _ = _
  rw [hr.cost, hcost]
  omega

end CompressorRecords.BundleRAM

end VPVNP
end Computability
end OAI
