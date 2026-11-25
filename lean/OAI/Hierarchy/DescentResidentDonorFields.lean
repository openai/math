import OAI.Hierarchy.DescentDonorFreshRAM
import OAI.Hierarchy.DescentDonorNativeParts

namespace OAI
/-! # The literal six inputs of the measured donor window -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Resident
open DescentSIMDLookup DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentPackedZip
open DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {H G M K w : ℕ} (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape)
local notation "N" => s.blocks*(2*s.cap)
local notation "P" => DescentHaloWalkRAM.breadth s.degree
local notation "b" => DescentSignedCableCodec.width s.degree s.cap

structure Sources (s : DepotRAM.Shape) (K : ℕ) where
  terrain : Expr
  signed : Fin (s.blocks*(2*s.cap))→Expr
  owner : Bank
  peers : Ports s.degree
  cableTables : Fin (s.blocks*(2*s.cap))→Tables
  ownerTables : Fin (s.degree+1)→Tables
  ranks : DescentHaloPackedRebase.Headers (DescentHaloWalkRAM.breadth s.degree)
  hubs : DescentHaloPackedRebase.Headers (DescentHaloWalkRAM.breadth s.degree)
  fresh : Fresh.Banks K

variable (R : Sources s K)

def «fields» (H G M : ℕ) : Fields where
  raw:=R.terrain
  signed:=Gather.assembly R.cableTables R.signed
  owners:=Gather.assembly R.ownerTables (Owners.expression R.peers R.owner H)
  ranks:=DescentHaloPackedRebase.context R.ranks
  hub:=DescentHaloPackedRebase.context R.hubs
  fresh:=Fresh.body R.fresh R.terrain H G M (SixBirths.width z M)

structure Fits (H G M w base : ℕ) : Prop where
  signed : Gather.Bounds (w:=w) (d:=b) (M:=M) R.cableTables R.signed base
  owners : Gather.Bounds (w:=w) (d:=(Owners.digits s.blocks s.degree s.short*3)*s.blocks) (M:=M)
    R.ownerTables (Owners.expression R.peers R.owner H) base
  peers : Accessible R.peers R.owner H G M w base
  sizeOwner : H*chunks G M≤R.owner.size
  owner : R.owner.Fits w base
  ranks : DescentHaloPackedRebase.Fits R.ranks H G M w base
  hubs : DescentHaloPackedRebase.Fits R.hubs H G M w base
  fresh : Fresh.Room s z R.fresh R.terrain H G M w base

structure Immutable (B prof C pad scale : ℕ) (m : Memory w) : Prop where
  signed : ∀i,Static (R.cableTables i) (Gather.setField (d:=b) i) M m
  owners : ∀i,Static (R.ownerTables i) (Gather.setField (d:=(Owners.digits s.blocks s.degree s.short*3)*s.blocks) i) M m
  fresh : Fresh.Fixed (H:=H) (G:=G) (M:=M) s z R.fresh B prof C pad scale m

variable (B prof C pad scale : ℕ) (hm : 0<M)
    (u : Fin H→Fin G→Panel s.blocks s.degree (2*s.cap) s.short) (lay : Bool)
    (sig : Fin H→Fin G→Fin s.blocks→Fin (2*s.cap)→Cell (DescentSignedCableCodec.width s.degree s.cap))
    (roster : Fin H→Fin s.degree→Option (Fin H))
    (order flags : Fin H→Fin (DescentHaloWalkRAM.breadth s.degree)→Fin (DescentHaloWalkRAM.breadth s.degree+1))
    (top : Fin ((K*H)*chunks G M)→Cell (SixBirths.topology z M))
    (born : Fin ((K*H)*chunks G M)→Cell (SixBirths.width z M))
local notation "here" => fun h g=>Owners.render s.blocks s.degree (2*s.cap) s.short B prof (Owners.register lay (u h g))

def parts (h : Fin H) (g : Fin G) : Parts s :=
  operands s lay (u h g) (sig h g) (Owners.registers here roster h g) (order h) (flags h)
    (fun x t=>Stage.numericSupply z B prof s.widths C pad scale hm (u h g) h g x t K top born)

theorem loaded (m : Memory w) (base : ℕ) (room : Fits s z R H G M w base)
    (fixed : Immutable (H:=H) (G:=G) (M:=M) s z R B prof C pad scale m)
    (terrain : Source R.terrain (fun h g=>Owners.register lay (u h g)) M m)
    (signedRows : ∀i,Source (R.signed i) (fun h g=>sig h g (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) M m)
    (mates : Mounted R.peers roster m G M) (home : Reads R.owner here M m)
    (ordinals : DescentHaloPackedRebase.Reads R.ranks order M G m) (hubs : DescentHaloPackedRebase.Reads R.hubs flags M G m)
    (keys : ∀i,m (R.fresh.topology.base+i.val)=((top i).val:Word w))
    (births : ∀i,SixBirths.cut (SixBirths.width z M) (m (R.fresh.births.base+i.val)).val=born i) :
    Loaded s («fields» s z R H G M) (parts s z B prof C pad scale hm u lay sig roster order flags top born) M m := by
  refine ⟨terrain,?_,?_,?_,?_,?_⟩
  · let v (h : Fin H) (g : Fin G) (i : Fin (s.blocks*(2*s.cap))):=sig h g (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
    have actual:=Gather.collected R.cableTables R.signed base room.signed m fixed.signed v signedRows (List.finRange (s.blocks*(2*s.cap)))
    simpa only [«fields»,parts,operands,Gather.assembly,List.mem_finRange,ite_true,v,cableBits] using actual
  · apply Owners.from_registers R.peers R.owner R.ownerTables base room.owners room.peers room.sizeOwner room.owner roster here m mates home fixed.owners
  · exact DescentHaloPackedRebase.source R.ranks base room.ranks order m ordinals
  · exact DescentHaloPackedRebase.source R.hubs base room.hubs flags m hubs
  · exact Fresh.source s z R.fresh R.terrain B prof C pad scale hm base room.fresh m fixed.fresh u (fun _ _=>lay) top born terrain keys births

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Resident

end OAI
