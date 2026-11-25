import OAI.Hierarchy.DescentPhysicalResetPeers

namespace OAI
/-! # The four sorted raw peers on the completed reset aperture -/
namespace Hierarchy.DescentDatedAddressBook.PeerAperture
open DescentResetPeerUnionRAM DescentSIMDLookup DescentPackedColony DescentSortedRoster ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (p : PeerAperture) (u : p.Inputs) (base : ℕ) (m : Memory w) (room : p.Room u base w)

include room in
/-- Sort the same three emitted raw peer words together with the receiver,
including true self-loops and vacant old/new rectangles. -/
theorem four_words (peers : Fin p.hosts→Fin 3→Option (Fin p.hosts))
    (three : ∀v j,p.memory u base m (p.rawPeers base+j.val*p.hosts+v.val)=(target (peers v j):Word w))
    (v : Fin p.hosts) (j : Fin 4) :
    p.memory u base m ((p.ports base).roster.base+(v.val*4+j.val))=
      (target (indexed (selfPeers peers) v j):Word w) := by
  let prior:=Program.output base p.oldHosts p.shapes p.oldDegree p.bits p.evidenceLanes
    p.evidenceGroups u.old u.test u.src m
  have input : ∀(h : Fin p.hosts) (q : Fin 3),prior (p.rawPeers base+q.val*p.hosts+h.val)=(target (peers h q):Word w) :=
    fun h q=>(p.three_word u base m room q h).symm.trans (three h q)
  have sorted : p.self base < 2^w := ((p.ordered base).2.2.1.trans (p.ordered base).2.2.2).trans_lt room.total
  have size : p.hosts < 2^w := by
    have roof:=room.total
    change p.threshold base+2*p.hosts+DescentDyadicSpan.span p.hosts < 2^w at roof
    omega
  have saved:=(DescentResetSelfPortsRAM.run (p.rawPeers base) (p.three base) p.hosts p.groups p.lanes
    prior peers le_rfl size room.width input sorted).2.1.roster v j
  have size₄:=DescentResetSelfPortsRAM.roster_fits (p.three base) p.hosts p.groups p.lanes sorted
  have index : v.val*4+j.val < p.hosts*4 :=
    (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right 4 v.isLt)
  have earlier:=(p.publish u base m room).2.2.2.2 ((p.ports base).roster.base+(v.val*4+j.val))
    ((Nat.add_lt_add_left (index.trans_le size₄.2) _).trans_le size₄.1.2.2)
  exact earlier.trans saved

end
end Hierarchy.DescentDatedAddressBook.PeerAperture

end OAI
