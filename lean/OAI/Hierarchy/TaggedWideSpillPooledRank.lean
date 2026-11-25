import OAI.Hierarchy.TaggedWireSpillRowOrder
import OAI.Hierarchy.TaggedWireTurnOffsets
import OAI.Hierarchy.ProtocolRAMTurnStepOrder
import OAI.Hierarchy.ProtocolRAMDateSpillRank

namespace OAI
/-! # Actual scanned starts in the dated electrical routing matrix -/
noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillRank
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open WireTelescope ProtocolRAM ProtocolRAM.Calendar CoreRoute ProtocolRAM.RouteSettlement ProtocolRAMTurnPrefix ProtocolRAMTurnReplayed
open scoped Classical Fin.CommRing
set_option quotPrecheck false
variable {W h d k K edges : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k→Fin K} (B : Mount (S:=S) π place edges)
    (inj : Function.Injective place) (pad : LinearAlgebra.SpectralBooks.ChordGraph.Chord K) (o : Orders h d k)
    (spill : Bank) (m : Memory W)
local notation "D" => B.datedLayout inj pad
local notation "enum" => spillEnum B o
local notation "rank" => (D).nativeOrder enum
local notation "stock" => fun g=>actual spill m (PurchaseInventory.slot g)
local notation "bits" => (D).bits stock
local notation "key" => NativeSlot.edge (D).routes rank
local notation "width" => NativeSlot.amount (D).routes bits rank

/-- The first physical column of the weighted scan enumerates precisely the
oriented router occurrences. The removed permanent prefix carries zero mass. -/
theorem native_start (i : Fin (coreCount o)) :
    TaggedShorterCommonScan.earlier (wireAt B o) (loadAt o spill m) i.val (wireAt B o i)=
    NativeSlot.start (D).routes bits rank (rank (i.natAdd edges)).1 (rank (i.natAdd edges)).2 := by
  have keys (a : Fin (coreCount o)) : key (a.natAdd edges)=wireAt B o a := by
    refine ((D).native_edge enum (a.natAdd edges)).trans ?_
    simp only [SettledMatrix.Layout.nativeEdge,finSumFinEquiv_symm_apply_natAdd,wireAt]
    rfl
  have head (a : Fin edges) : width (a.castAdd (coreCount o))=0 := by
    refine ((D).native_width enum stock (a.castAdd (coreCount o))).trans ?_
    simp only [SettledMatrix.Layout.nativeWidth,finSumFinEquiv_symm_apply_castAdd]
    rfl
  have widths (a : Fin (coreCount o)) : width (a.natAdd edges)=loadAt o spill m a := by
    refine ((D).native_width enum stock (a.natAdd edges)).trans ?_
    simp only [SettledMatrix.Layout.nativeWidth,finSumFinEquiv_symm_apply_natAdd]
    rfl
  unfold NativeSlot.start
  rw [Sigma.eta,Equiv.symm_apply_apply]
  change _ = TaggedShorterCommonScan.earlier key width (edges+i.val) (key (i.natAdd edges))
  exact ((earlier_tail key width (wireAt B o) (loadAt o spill m) head keys widths i (wireAt B o i)).symm).trans
    (congrArg (TaggedShorterCommonScan.earlier key width (edges+i.val)) (keys i).symm)

theorem RankRead.router_start {lo : ℕ} {out : Memory W}
    (read : RankRead B o lo spill m out) (i : Fin (coreCount o)) :
    out (ranks lo (edges+coreCount o) edges+4*(edges+i.val)+3)=
      (NativeSlot.start (D).routes bits rank (rank (i.natAdd edges)).1 (rank (i.natAdd edges)).2 : Word W) :=
  (read.rank i).trans (congrArg (fun x : ℕ=>(x:Word W)) (native_start B inj pad o spill m i))

local notation "goodrow" g => Sum.inr (Sum.inl g)

/-- The authenticated address of a particular oriented occurrence. -/
def goodIndex (g : Commodity (Fin (2^h)) (Stages h d) k) (q : Fin ((D).data.steps (goodrow g)).length) : Fin (coreCount o) :=
  corePrefix o ⟨g,((orientedIndex ((D).data.goods.tail g) ((D).data.goods.head g)
    (B.ordinary g)).symm q).cast (ProtocolRAMTurnGeometry.length_ordinary B g)⟩

theorem goodIndex_occurrence (g : Commodity (Fin (2^h)) (Stages h d) k) (q : Fin ((D).data.steps (goodrow g)).length) :
    enum (goodIndex B inj pad o g q)=.inl ⟨g,(orientedIndex ((D).data.goods.tail g) ((D).data.goods.head g) (B.ordinary g)).symm q⟩ := by
  simp only [goodIndex,spillEnum,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem goodIndex_word (g : Commodity (Fin (2^h)) (Stages h d) k) (q : Fin ((D).data.steps (goodrow g)).length) :
    edges+(goodIndex B inj pad o g q).val=ProtocolRAMTurnGeometry.origin (edges:=edges) o (goodrow g)+
      ProtocolRAMTurnStepOrder.offset (CoreRoute.arity g)
        (decide (¬(D).data.goods.tail g<(D).data.goods.head g)) q.val := by
  let x:=(orientedIndex ((D).data.goods.tail g) ((D).data.goods.head g) (B.ordinary g)).symm q
  let c:=x.cast (ProtocolRAMTurnGeometry.length_ordinary B g)
  change edges+(corePrefix o ⟨g,c⟩).val=_
  refine ((congrArg (edges+·) (corePrefix_val o ⟨g,c⟩)).symm.trans
    (ProtocolRAMTurnGeometry.goods_at (edges:=edges) o g c).symm).trans ?_
  apply congrArg (_+·)
  refine (ProtocolRAMTurnStepOrder.inverse_ordinal ((D).data.goods.tail g) ((D).data.goods.head g)
    (B.ordinary g) q).trans ?_
  exact congrArg (fun n=>ProtocolRAMTurnStepOrder.offset n
    (decide (¬(D).data.goods.tail g<(D).data.goods.head g)) q.val)
    (ProtocolRAMTurnGeometry.length_ordinary B g)

def goodHop (g : Commodity (Fin (2^h)) (Stages h d) k) (q : Fin ((D).data.steps (goodrow g)).length) : Σi,Fin ((D).routes i).length :=
  (Equiv.sigmaCongrLeft (β:=fun x=>Fin ((D).data.steps x).length) (D).num).symm ⟨goodrow g,q⟩

theorem goodIndex_hop (g : Commodity (Fin (2^h)) (Stages h d) k) (q : Fin ((D).data.steps (goodrow g)).length) :
    rank ((goodIndex B inj pad o g q).natAdd edges)=goodHop B inj pad g q := by
  let e:=Equiv.sigmaCongrLeft (β:=fun x=>Fin ((D).data.steps x).length) (D).num
  apply congrArg e.symm
  change (D).data.occurrences ((Equiv.sumCongr (Equiv.refl _) enum)
    (finSumFinEquiv.symm ((goodIndex B inj pad o g q).natAdd edges)))=⟨goodrow g,q⟩
  simp only [finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,Sum.map_inr,goodIndex_occurrence]
  exact congrArg (Sigma.mk (goodrow g)) ((orientedIndex ((D).data.goods.tail g) ((D).data.goods.head g) (B.ordinary g)).apply_symm_apply q)

theorem RankRead.router_at_good {lo : ℕ} {out : Memory W}
    (read : RankRead B o lo spill m out) (g : Commodity (Fin (2^h)) (Stages h d) k)
    (q : Fin ((D).data.steps (goodrow g)).length) :
    out (ranks lo (edges+coreCount o) edges+4*(edges+(goodIndex B inj pad o g q).val)+3)=
      (NativeSlot.start (D).routes bits rank (goodHop B inj pad g q).1 (goodHop B inj pad g q).2 : Word W) := by
  refine (RankRead.router_start B inj pad o spill m read (goodIndex B inj pad o g q)).trans ?_
  exact congrArg (fun z : Σi,Fin ((D).routes i).length =>
    (NativeSlot.start (D).routes bits rank z.1 z.2 : Word W)) (goodIndex_hop B inj pad o g q)

end Hierarchy.ProtocolRAMDateSpillRank
end

end OAI
