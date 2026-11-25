import OAI.Hierarchy.ProtocolRAMDateSpillRank
import OAI.Hierarchy.ProtocolRAMTurnLiveGeometry

namespace OAI
/-! # Exact edge keys on each chronological visit of an active original commodity -/
noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillRank
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.Calendar.CoreRoute ProtocolRAMTurnPrefix ProtocolRAMTurnReplayed
open scoped Classical Fin.CommRing
variable {W h d k K edges : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k→Fin K} (B : Mount (S:=S) π place edges) (inj : Function.Injective place)
    (pad : Chord K) (o : CoreRoute.Orders h d k)

theorem RankRead.key_on (lo : ℕ) {spill : Bank} {original m : Memory W}
    (ready : RankRead B o lo spill original m) (word : edges+coreCount o≤2^W)
    (g : Commodity (Fin (2^h)) (Stages h d) k) (j : Fin (CoreRoute.arity g)) :
    let q:=ProtocolRAMTurnGeometry.origin (edges:=edges) o (.inr (.inl g))+j.val
    (ProtocolRAMTurnReplayed.key lo (edges+coreCount o)).read m (q:Word W)=
      (ProtocolRAMTurnOccurrence.edgeAt B inj pad o q:Word W) := by
  intro q
  let i:=CoreRoute.corePrefix o ⟨g,j⟩
  have ix : i.val=(CoreRoute.slotOrder o (.inl ⟨g,j⟩)).val := (CoreRoute.corePrefix_val o _).symm
  have atWord : q=edges+i.val := (ProtocolRAMTurnGeometry.goods_at o g j).trans (congrArg (edges+·) ix.symm)
  have observed:=ready.key i
  have iLt : edges+i.val<edges+coreCount o:=Nat.add_lt_add_left i.isLt _
  have small:=iLt.trans_le word
  have fit:=iLt.trans_le (ProtocolRAMPackedRanked.group_capacity (edges+coreCount o))
  have physical : (ProtocolRAMTurnReplayed.key lo (edges+coreCount o)).read m (q:Word W)=((wireAt B o i).val:Word W) := by
    rw [atWord]
    change m (lo+(↑(edges+i.val):Word W).val%2^ProtocolRAMPackedRanked.groupBits (edges+coreCount o))=_
    simpa only [Fin.val_cast_of_lt small,Nat.mod_eq_of_lt fit] using observed
  have full:=spillEnum_edge B o i
  have e : fullIndex o i=slotOrder o (.inl ⟨g,j⟩) :=
    Fin.ext ((fullIndex_val o i).trans ix)
  rw [e] at full
  have edge : (wireAt B o i).val=ProtocolRAMTurnOccurrence.edgeAt B inj pad o q := by
    rw [show q=edges+(slotOrder o (.inl ⟨g,j⟩)).val from ProtocolRAMTurnGeometry.goods_at o g j,
      ProtocolRAMTurnOccurrence.liveSlot B inj pad o (.inl ⟨g,j⟩)]
    simpa only [CoreRoute.enum,Equiv.trans_apply,Equiv.symm_apply_apply,wireAt] using congrArg Fin.val full.symm
  exact physical.trans (congrArg (fun a : ℕ => (a : Word W)) edge)

end Hierarchy.ProtocolRAMDateSpillRank

end
end OAI
