import OAI.Computability.VPVNP.CompressorRecordsBundlePass
import OAI.Computability.VPVNP.CompressorBundleRankedTable
import OAI.Computability.VPVNP.ShrinkStatePass

/-!
# The first four native passes for a shrinking state

Starting with the incidence and placement directories, the four passes classify
the arcs, append their IDs, gather their sorting keys, and write their ranks.
The output rank and original width of every port are now both directly
addressed by its actual outgoing ID. Each pass starts in the post-memory of
the preceding one.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.PackingData BundleKeys
open BundleGather BundleRank

variable {w a g : ℕ}
variable (X : State a (packingLaneBits a g))
local notation "N" => Fintype.card X.Base
local notation "A" => N * 2^(packingLaneBits a g) * 2^a
local notation "D" => (2:ℕ)^a
local notation "C" => Shrink.colors a
local notation "J" => Shrink.J a
local notation "cap" => pieceCount D C
local notation "P" => X.packingData
local notation "arcs" => oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex

variable (T : IncidenceDirectory w) (p : Fin 11 → Word w) (q : Fin 6 → Word w)
variable (out dest : Word w)
local notation "K" => KeyTable.dyadic (q 5) (p 10) out T.width (Fin.val (q 4)) N a g
local notation "R" => rankPublic q (p 10) out dest

/-- Post-memory at each pass boundary is computed from the preceding reports. -/
structure RankedDirectoryRun (m : Memory w) (cs ls gs rs : List (Report w)) : Prop where
  classify : runSegment ((template visit 0).instantiate w p).program (1+visit.length)
    (some 0) m (List.replicate A []) = some cs
  append : runSegment ((template collectPreimage 3).instantiate w q).program 23 (some 0)
    (after m (eventLog cs)) (List.replicate A []) = some ls
  lists : PreimagesAt q (BundleLists.wordOwner P arcs sites) (after (after m (eventLog cs)) (eventLog ls)) A
  gather : runSegment ((template Fixed.visit 0).instantiate w (Fixed.parameters K)).program 29 (some 0)
    (after (after m (eventLog cs)) (eventLog ls)) (List.replicate A []) = some gs
  gatherCursor : endState (some 0) gs = some (Fin.ofNat _ A)
  gatherWork : ∀ r ∈ gs, r.events.length = 28 ∧ r.probes = 3
  rank : let f := after (after (after m (eventLog cs)) (eventLog ls)) (eventLog gs)
    let v := PortRankRAM.visit cap
    SlotOwners.FilledRun ((template v 0).instantiate w R).program (1+v.length) (cap+4) v.length A dest
      (fun j ↦ PortRankRAM.result R f (Fin.ofNat _ j) cap) f rs
  keys : let f := after (after (after (after m (eventLog cs)) (eventLog ls)) (eventLog gs)) (eventLog rs)
    ∀ e : OldArc X.Base a g, f ((p 10).val+(arcs e).val) =
      Fin.ofNat _ (keyAt X.baseIndex (bothThick X.slots X.baseIndex e) e)
  frame : ∀ addr,
    (∀ (t : Fin 2) (i : Word w), i.val < A → addr ≠ outAddr p t i) →
    OutsidePreimageWrites q addr → addr < out.val → addr < dest.val →
    after (after (after (after m (eventLog cs)) (eventLog ls)) (eventLog gs)) (eventLog rs) addr = m addr
  cost : RAMBuckets.cost Report.probes cs + RAMBuckets.cost Report.probes ls +
    RAMBuckets.cost Report.probes gs + RAMBuckets.cost Report.probes rs = (cap+23)*A

private theorem key_sizes (ha : A ≤ 2^w) : N*(2^J*(D*(2^C*D))) ≤ 2^w ∧ 2^C*D ≤ 2^w := by
  have arith : A = N*(2^J*(D*(2^C*D)))*2^g := by
    simp only [packingLaneBits, Shrink.J, Shrink.colors,pow_add]; ring
  have h := (Nat.le_mul_of_pos_right (N*(2^J*(D*(2^C*D)))) (Nat.two_pow_pos g)).trans (arith ▸ ha)
  have hN : 0 < N := Fintype.card_pos
  exact ⟨h,((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos a)).trans
    ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos J)).trans (Nat.le_mul_of_pos_left _ hN))).trans h⟩

/-- All four native report sequences, their combined cost, and the final
`shrinkNumber`, `shrinkOrder` and width entries. -/
theorem ranked_directory (shrPub : Fin 14 → Word w) (layout : Bool) (m : Memory w)
    (inc : T.ActualColumns X m) (placement : ShrinkRAM.PlacementColumns X.slots X.baseIndex shrPub layout m)
    (hp : Params p a C J g (numBundles N a g)) (reg : Regions p m A)
    (hOut : p 5 = T.actualOut) (hThick : p 6 = shrPub 11) (hOwner : p 7 = shrPub 10)
    (hAssigned : p 8 = shrPub 12) (qreg : RowRegions q) (hinput : q 1 = p 9) (hA : (q 0).val = A)
    (hcount : (q 2).val = numBundles N a g + numBundles N a g)
    (zero : ∀ u : Word w, u < q 2 → m (countAt q u).val = 0)
    (apart : ∀ u : Word w, u < q 2 → ∀ t : Fin 2, ∀ i : Word w, i.val < A →
      (countAt q u).val ≠ outAddr p t i)
    (kreg : (K).Layout) (rreg : RankLayout q (p 10) out dest A (2*numBundles N a g))
    (keysOutside : ∀ j < A, OutsidePreimageWrites q ((p 10).val+j))
    (widthFits : T.width.val+A ≤ 2^w)
    (widthClass : ∀ e : OldArc X.Base a g, ∀ t : Fin 2, ∀ i : Word w, i.val < A →
      (T.width + Fin.ofNat _ (arcs e).val).val ≠ outAddr p t i)
    (widthAppend : ∀ j < A, OutsidePreimageWrites q (T.width.val+j))
    (widthRank : separated T.width.val A dest.val A) :
    ∃ cs ls gs rs, RankedDirectoryRun X T p q out dest m cs ls gs rs ∧
      let f := after (after (after (after m (eventLog cs)) (eventLog ls)) (eventLog gs)) (eventLog rs)
      (∀ b (x : (P).MotifFiber b), f (dest.val+(arcs x.val.val).val) = Fin.ofNat _ (X.shrinkNumber b x).val) ∧
      (∀ b (x : (P).ThickFiber b), f (dest.val+(arcs x.val.val).val) = Fin.ofNat _ (X.shrinkOrder b x).val) ∧
      (∀ e : OldArc X.Base a g, f (T.width.val+(arcs e).val) = Fin.ofNat _ (X.packingWidth e)) ∧
      ∀ e : OldArc X.Base a g, f ((q 1).val+(arcs e).val) =
        Fin.ofNat _ (BundleLists.bucketIndex sites (BundleLists.bucketOf P e)).val := by
  classical
  obtain ⟨cs,ls,hc,hl,scan,cls,pre,frame,_,cost⟩ := classify_and_collect X T p shrPub layout m inc
    placement hp reg hOut hThick hOwner hAssigned q qreg hinput hA hcount kreg.motifFits zero apart
  let classMem := after m (eventLog cs)
  let lists := after classMem (eventLog ls)
  obtain ⟨fitM,fitT⟩ := key_sizes X reg.fits
  have lookup (e : OldArc X.Base a g) :
      lists ((p 10).val+(arcs e).val) = classMem (p 10+Fin.ofNat _ (arcs e).val).val := by
    have fit := kreg.keysFit
    change (p 10).val+A ≤ 2^w at fit
    rw [Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt (by have := (arcs e).isLt; omega)]
    exact frame _ (keysOutside _ (arcs e).isLt)
  have hkM (x : (P).Motif) : lists ((p 10).val+(arcs x.val).val) =
      (motifKey P X.baseIndex (bitWordFinEquiv J) x).castLE fitM := by
    rw [lookup]; exact Fin.ext (cls.motif_key X.slots X.baseIndex x)
  have hkT (x : (P).ThickWire) : lists ((p 10).val+(arcs x.val).val) = (thickKey P x).castLE fitT := by
    rw [lookup]; exact Fin.ext (cls.thick_key X.slots X.baseIndex x.val.1 ⟨x,rfl⟩)
  obtain ⟨gs,rs,hg,done,rank,read,total⟩ := fixed_ranked_table P arcs sites q (p 10) out T.width dest
    (State.two_le_packingColors a) X.baseIndex (bitWordFinEquiv J) fitM fitT kreg rreg qreg hA hcount lists pre hkM hkT
  have count : Fixed.entryCount K = A := by
    change numBundles N a g * (2^C*D/4+cap) = _
    rw [Nat.mul_add]; exact bundle_rows_total N a g
  have gathered : runSegment ((template Fixed.visit 0).instantiate w (Fixed.parameters K)).program 29
      (some 0) lists (List.replicate A []) = some gs := count ▸ hg.executed
  have gatherCursor : endState (some 0) gs = some (Fin.ofNat _ A) := count ▸ hg.cursor
  refine ⟨cs,ls,gs,rs,⟨hc,hl,pre,gathered,gatherCursor,hg.work,rank,fun e ↦ ?_,?_,?_⟩,read.motif,read.thick,fun e ↦ ?_,fun e ↦ ?_⟩
  · have hi := (arcs e).isLt
    have keep := rank.frame _ (rreg.keys.outside hi)
    have keep' := (done.inputs K kreg (le_refl _)).2.1 _ hi
    refine keep.trans (keep'.trans ((lookup e).trans ?_))
    exact Fin.ext ((cls.key e).trans (Nat.mod_eq_of_lt ((cls.key e) ▸ (classMem _).isLt)).symm)
  · intro addr outside hrows hkeys hdest
    exact (rank.frame addr (.inl hdest)).trans ((done.outside K kreg (le_refl _) addr (.inl hkeys)).trans
      ((frame addr hrows).trans (scan.preserve addr (fun t i _ hi ↦ outside t i (by simpa only [Nat.zero_add] using hi)))))
  · rw [cost,Nat.add_assoc,total,← Nat.add_mul]; congr 1; unfold Shrink.colors; omega
  · let j := (arcs e).val
    have keep := rank.frame (T.width.val+j) (widthRank.outside (arcs e).isLt)
    have keep' := (done.inputs K kreg (le_refl _)).2.2 j (arcs e).isLt
    have ht := scan.width_at X T inc widthClass e
    rw [Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt (by have := (arcs e).isLt; omega)] at ht
    exact keep.trans (keep'.trans ((frame _ (widthAppend j (arcs e).isLt)).trans ht))

  · let i := Fin.ofNat (2^w) (arcs e).val
    have hi := (arcs e).isLt
    have hv : i.val = (arcs e).val := Nat.mod_eq_of_lt (hi.trans_le reg.fits)
    have hown := pre.owners i (show i.val < (q 0).val by rw [hv,hA]; exact hi)
    have hb : numBundles N a g+numBundles N a g ≤ 2^w := hcount ▸ (q 2).isLt.le
    rw [BundleLists.wordOwner_at P arcs sites reg.fits hb e] at hown
    have hfit := qreg.ownersBeforeCounts
    change lists (q 1+i).val = _ at hown
    rw [Fin.val_add,hv,Nat.mod_eq_of_lt (by have := (q 3).isLt; omega)] at hown
    exact (rank.frame _ (rreg.owners.outside hi)).trans
      ((done.outside K kreg (le_refl _) _ (rreg.keepOwners.outside hi)).trans hown)

end CompressorRecords.BundleRAM

end VPVNP
end Computability
end OAI
