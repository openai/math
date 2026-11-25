import OAI.Hierarchy.DescentDatedCompactPeerTables

namespace OAI
/-! The signed tail preserves the compact peer lookup from the common installed prefix. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty DescentSIMDLookup DescentPackedZip DescentPackedChildNeighbor
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM

theorem retained_peer (s : SignedExtent) (I : s.Input) (base : ℕ) {w : ℕ} (m : Memory w)
    (fits : s.Fits I base w) (space : s.roof base < 2^w) (z : s.Socket)
    (values : Fin s.hosts → Fin s.groups → Cell s.fieldBits)
    (installedPeer : Source (s.peerField I base z) values s.lanes (s.installed I base m)) :
    (s.peerField I base z).Fits w (s.roof base) ∧
      Source (s.peerField I base z) values s.lanes (s.phaseImage I base m) := by
  have peer : (s.peerField I base z).Fits w (s.tailStart base) :=
    SIMD.fitted _ _ (s.peer_chart_room I base fits space z) _
  have inside : s.tailStart base ≤ s.roof base := (s.prefix_room base).trans_eq (s.calibrated base)
  have enough : s.phaseEnd base < 2^w := (s.calibrated base).trans_lt space
  have tail := DescentOrdinarySignedDate.Layout.any (s.layout I base) (s.tailStart base)
    s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes I.newDegree s.hosts s.groups w
    (s.installed I base m) fits.header fits.query fits.items enough
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ inside peer,?_⟩
  intro row
  rw [s.phase_output I base m]
  exact (ProtocolRAM.eval_below _ _ _ _ peer (fun a ha => tail.2.1 a (.inl ha))).trans (installedPeer row)

end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
