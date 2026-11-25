import OAI.Hierarchy.DescentPhysicalResetStemEntry
import OAI.Hierarchy.DescentResetStemStoredChart

namespace OAI
/-! # The compact actor, hub, prior host and raw-neighbor registers in the dated stem memory -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty DescentSixParty.ResetInput DescentDenseHostOrder DescentCommonHost DescentPackedColony DescentResetStemMaskedPorts
open DescentSIMDLookup DescentDyadicSpan ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront) (base : ℕ) (s : v.Scene) {w : ℕ} (space : v.SceneRoom base s w)
local notation "P₀" => v.peer
local notation "floor" => v.parentStart base

/-- The three heterogeneous bank descriptors all point to the literal cells written
by the paid three-peer union. -/
def rawNeighborBank (i : Fin 3) : Bank :=
  ⟨(P₀).rawPeers (v.peers base)+i.val*(P₀).hosts,Nat.clog 2 (P₀).hosts⟩

def stemRegisters (hub : Bank) : DescentResetStemTemplatePorts.Banks :=
  ⟨s.inverse,v.parent base,v.rawNeighborBank base,hub⟩

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits} {price ε : ℝ}
    {h C height : ℕ} (Z : ResetInput A price ε h C height) (T : Terminals Z)
local notation "pool" => roster Z.graph (Z.k-T.commonDepth) height
local notation "Vnew" => ↥(Z.commonNames T)
variable (vertex : Z.V↪Fin v.peer.oldHosts)
local notation "N" => (P₀).oldHosts*(Finset.card pool)
local notation "raw" => Z.rawHostRank T vertex
local notation "denseId" => Z.denseHostRank T vertex

theorem stem_registers_read (previous : Memory w) (hub : Bank) (isHub : Z.V→Bool)
    (shape : (Finset.card pool)=(P₀).shapes) (capacity : Fintype.card Vnew≤v.newHosts)
    (network : Fin N→Fin 3→Option (Fin N))
    (counted : previous s.count.base=(Fintype.card Vnew:Word w))
    (inverse : ∀u,previous (s.inverse.base+((denseId) u).val)=((raw u).val:Word w))
    (bitmap : ∀j : Fin N,previous (s.stems.flags.base+j.val)=if ∃u,raw u=j then 1 else 0)
    (oldHub : ∀u,previous (hub.base+(vertex u).val)=((isHub u).toNat:Word w))
    (lowCount : s.count.base<base) (lowInv : s.inverse.base+Fintype.card Vnew≤base)
    (lowMask : s.stems.flags.base+N≤base) (lowHub : hub.base+(P₀).oldHosts≤base)
    (neighbors : ∀(i : Fin 3) (j : Fin N),
      let lo:=v.peers base
      let adr:=(P₀).rawPeers lo+i.val*(P₀).hosts+j.val
      DescentResetPeerUnionRAM.Program.output lo (P₀).oldHosts (P₀).shapes (P₀).oldDegree
        (P₀).bits (P₀).evidenceLanes (P₀).evidenceGroups s.peers.old s.peers.test s.peers.src
          (v.prePeers base s space previous) adr=(target (network j i):Word w)) :
    let last:=v.stemEntry base s space previous
    DescentResetStemKeyReindex.Directory (v.parent base).base (Z.parentIndex T vertex) last ∧
      Stored (v.stemRegisters base s hub) s.count (Z.rawAtIndex T vertex) (Z.parentIndex T vertex)
        network (priorHub vertex isHub) last ∧
      ∀j : Fin v.newHosts,Fintype.card Vnew≤j.val→last ((v.parent base).base+j.val)=0 := by
  let low:=v.preParent base s space previous
  have total : N=(P₀).hosts:=by rw [shape];rfl
  have keep:=v.parent_prior base s space previous
  have order:=v.floor_before base s space
  have size : N≤ s.stems.flags.size:=total.trans_le space.stems.bitmap
  have end_ : DescentResetParentDate.endAddress floor N v.newHosts<2^w:=by
    rw [total]
    exact (v.front_order base).2.1.trans_lt space.stems.final
  have read:=
    Z.parent_stored_chart T vertex floor s.count s.stems.flags s.inverse hub (v.rawNeighborBank base)
      capacity low isHub network space.stems.prev size end_
      (fun i=>(keep _ ((Nat.add_lt_add_left i.isLt _).trans_le lowMask)).trans (bitmap i))
      ((keep _ lowCount).trans counted)
      (fun u=>(keep _ ((Nat.add_lt_add_left ((denseId) u).isLt _).trans_le lowInv)).trans (inverse u))
      (fun i j=>(v.parent_neighbor base s space previous i (Fin.cast total j)).trans (neighbors i j))
      (fun u=>(keep _ ((Nat.add_lt_add_left (vertex u).isLt _).trans_le lowHub)).trans (oldHub u))
      (lowCount.trans_le order) (lowInv.trans order)
      (fun i=>by
        have hi:=Nat.mul_le_mul_right (P₀).hosts (Nat.succ_le_of_lt i.isLt)
        rw [Nat.succ_mul] at hi
        have step : (P₀).three (v.peers base)≤floor:=by
          obtain ⟨_,h₁,h₂,h₃⟩:=(P₀).ordered (v.peers base)
          exact ((h₁.trans h₂).trans h₃).trans (Nat.le_add_right ..)
        refine le_trans ?_ step
        change (P₀).rawPeers (v.peers base)+i.val*(P₀).hosts+N≤(P₀).rawPeers (v.peers base)+3*(P₀).hosts
        omega) (lowHub.trans order)
  have image_eq : DescentResetParentDate.memory floor N v.newHosts (Finset.card pool) s.stems.flags low end_=
      v.stemEntry base s space previous:=by
    have transport {hosts hosts' shapes shapes' : ℕ} (eqHosts : hosts=hosts') (eqShapes : shapes=shapes')
        (room : DescentResetParentDate.endAddress floor hosts v.newHosts<2^w)
        (room' : DescentResetParentDate.endAddress floor hosts' v.newHosts<2^w) :
        DescentResetParentDate.memory floor hosts v.newHosts shapes s.stems.flags low room =
          DescentResetParentDate.memory floor hosts' v.newHosts shapes' s.stems.flags low room' := by
      subst hosts'; subst shapes'; rfl
    exact transport total shape end_ _
  have bank_eq : DescentResetParentAperture.parent floor N v.newHosts=v.parent base:=by rw [total]; rfl
  dsimp only at read ⊢
  rw [image_eq,bank_eq] at read
  exact read

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
