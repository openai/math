import OAI.Hierarchy.DescentPhysicalResetSceneRead
import OAI.Hierarchy.DescentResetStemMaskedPorts

namespace OAI
/-! # The memory between the paid reset-parent upload and the signed stem scan -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM
open DescentResetStemPackedIssue
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront) (base : ℕ) (s : v.Scene) {w : ℕ} (space : v.SceneRoom base s w)
local notation "P" => v.peer
local notation "entry" => v.parentEnd base
local notation "floor" => v.parentStart base
local notation "F" => v.received base s space

def stemEntry (m : Memory w) :=
  DescentResetParentDate.memory floor (P).hosts v.newHosts (P).shapes s.stems.flags
    (v.preParent base s space m) ((v.front_order base).2.1.trans_lt space.stems.final)

theorem received_from_entry (m : Memory w) :
    (F).image m=Mixed.Projected.image entry (v.parent base).base v.metaBits (P).oldHosts v.newHosts
      (P).groups v.blocks v.oldLanes (P).lanes s.stems.parse s.stems.side s.stems.operands s.stems.ports
      (v.stemEntry base s space m) := rfl

theorem entry_word (m : Memory w) (a : ℕ) (early : a<entry) :
    (F).image m a=v.stemEntry base s space m a := by
  have run:=Mixed.Projected.any_full entry (v.parent base).base v.metaBits (P).oldHosts v.newHosts
    (P).groups v.blocks v.oldLanes (P).lanes s.stems.parse s.stems.side s.stems.operands s.stems.ports
    (v.stemEntry base s space m) space.stems.positive space.stems.blocks space.stems.sources
    space.stems.ports (v.front_order base).2.2 (by rw [v.stem_boundary s.stems base];exact space.stems.final)
  exact run.2.1 a (.inl early)

include space in
theorem floor_before : base≤floor := by
  obtain ⟨pre,donors,peers,raw⟩:=v.peer_boundaries base s space
  exact (((pre.trans donors).trans peers).trans raw).trans (Nat.le_add_right ..)

theorem parent_prior (m : Memory w) (a : ℕ) (early : a<base) :
    v.preParent base s space m a=m a := by
  have cuts:=v.retained_cuts base s space m
  exact (cuts.1 a (early.trans_le (v.floor_before base s space))).symm.trans (cuts.2.2.2.2 a early)

theorem parent_neighbor (m : Memory w) (j : Fin 3) (i : Fin (P).hosts) :
    let lo:=v.peers base
    let adr:=(P).rawPeers lo+j.val*(P).hosts+i.val
    v.preParent base s space m adr=DescentResetPeerUnionRAM.Program.output lo (P).oldHosts (P).shapes (P).oldDegree
      (P).bits (P).evidenceLanes (P).evidenceGroups s.peers.old s.peers.test s.peers.src (v.prePeers base s space m) adr := by
  intro lo adr
  have times:=Nat.mul_le_mul_right (P).hosts (Nat.succ_le_of_lt j.isLt)
  rw [Nat.succ_mul] at times
  have small : adr<(P).three lo :=by
    change (P).rawPeers lo+j.val*(P).hosts+i.val<(P).rawPeers lo+3*(P).hosts
    have hi:=i.isLt
    omega
  obtain ⟨_,a,b,c⟩:=(P).ordered lo
  have low:=small.trans_le ((((a.trans b).trans c)).trans (Nat.le_add_right ((P).endAddress lo) v.newHosts))
  exact ((v.retained_cuts base s space m).1 adr low).symm.trans (v.neighbor_read base s space m j i)

theorem entry_original (m : Memory w) (a : ℕ) (early : a<base) (prior : a<entry) :
    v.stemEntry base s space m a=m a :=
  (v.entry_word base s space m a prior).symm.trans ((v.retained_cuts base s space m).2.2.2.2 a early)

theorem entry_neighbor (m : Memory w) (j : Fin 3) (i : Fin (P).hosts)
    (early : (P).rawPeers (v.peers base)+j.val*(P).hosts+i.val<entry) :
    let lo:=v.peers base
    let adr:=(P).rawPeers lo+j.val*(P).hosts+i.val
    v.stemEntry base s space m adr=DescentResetPeerUnionRAM.Program.output lo (P).oldHosts (P).shapes (P).oldDegree
      (P).bits (P).evidenceLanes (P).evidenceGroups s.peers.old s.peers.test s.peers.src (v.prePeers base s space m) adr :=
  (v.entry_word base s space m _ early).symm.trans (v.neighbor_read base s space m j i)

theorem entry_reads {H G M bits : ℕ} (m : Memory w) (bank : Bank) (x : Fin H→Fin G→Cell bits)
    (read : DescentPackedColony.Reads bank x M m) (fit : bank.Fits w base) (size : H*chunks G M≤bank.size) :
    DescentPackedColony.Reads bank x M (v.stemEntry base s space m) :=by
  intro p
  have low:bank.base+(row H G M p).val<base:=(Nat.add_lt_add_left ((row H G M p).isLt.trans_le size) _).trans_le fit.2.2
  have before:base≤entry:=(v.floor_before base s space).trans (v.front_order base).1
  exact (v.entry_original base s space m _ low (low.trans_le before)).trans (read p)

theorem entry_mounted {D H G M : ℕ} (m : Memory w) (ports : DescentPackedColony.Ports D) (bank : Bank)
    (roster : Fin H→Fin D→Option (Fin H)) (read : DescentPackedColony.Mounted ports roster m G M)
    (fit : DescentPackedColony.Accessible ports bank H G M w base) :
    DescentPackedColony.Mounted ports roster (v.stemEntry base s space m) G M :=by
  have same (b : Bank) (fitb : b.Fits w base) (j : ℕ) (inside : j<b.size) :
      v.stemEntry base s space m (b.base+j)=m (b.base+j) :=by
    have h₀:=(Nat.add_lt_add_left inside b.base).trans_le fitb.2.2
    exact v.entry_original base s space m _ h₀ (h₀.trans_le ((v.floor_before base s space).trans (v.front_order base).1))
  refine ⟨fun p i=>(same _ (fit.ids i) _ ((row H G M p).isLt.trans_le (fit.idsRoom i))).trans (read.ids p i),?_,
    fun u=>(same _ fit.offsets _ (u.isLt.trans_le fit.offRoom)).trans (read.offsets u),
    fun p=>(same _ fit.chunks _ ((row H G M p).isLt.trans_le fit.chunkRoom)).trans (read.chunks p)⟩
  intro h i
  have address:h.val*D+i.val<H*D:=by
    calc
      h.val*D+i.val<h.val*D+D:=Nat.add_lt_add_left i.isLt _
      _=(h.val+1)*D:=(Nat.succ_mul ..).symm
      _≤H*D:=Nat.mul_le_mul_right _ h.isLt
  exact (same _ fit.roster _ (address.trans_le fit.rosterRoom)).trans (read.roster h i)

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
