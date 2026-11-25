import OAI.Hierarchy.DescentPhysicalResetSceneInputs
import OAI.Hierarchy.DescentResetTrunkScalarBanks

namespace OAI
/-! # Address bounds for the native masked stem registers -/
namespace Hierarchy.DescentResetStemMaskedPorts
open DescentResetStemTemplatePorts (Banks)
open ProtocolRAM

/-- The instructions fit whenever their bank descriptors end below the scan.
The actual row counts are only needed for the separate value theorem. -/
theorem fits_only {K palette w stop : ℕ} (B : Banks) (number : Bank) (oldH : ℕ)
    (template : Fin K→Option (Fin palette×Fin palette))
    (count : number.Fits w stop) (here : B.here.Fits w stop) (parent : B.parent.Fits w stop)
    (near : ∀i,(B.neighbors i).Fits w stop) (hub : B.hub.Fits w stop) :
    (ports B number oldH template).All (Expr.Fits w stop) := by
  have gated (e : Expr) (c : ℕ) (safe : e.Fits w stop) : (guard number e c).Fits w stop :=
    ⟨trivial,⟨count,trivial⟩,safe,trivial⟩
  have first : (hereAt B number).Fits w stop := gated _ _ ⟨here,trivial⟩
  exact ⟨first,fun i=>⟨near i,first⟩,
    fun j=>gated _ _ (DescentResetStemTemplatePorts.endpoint_fits _ _ _ _ _ parent),
    fun j=>gated _ _ (DescentResetStemTemplatePorts.endpoint_fits _ _ _ _ _ parent),
    fun _=>gated _ _ ⟨hub,parent,trivial⟩⟩
end Hierarchy.DescentResetStemMaskedPorts

namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentDyadicSpan ProtocolRAM
noncomputable section

/-- The three peer arrays can share a scalar address interval even though their
bank descriptors round up to dyadic size. The final peer reservation includes that padding. -/
theorem masked_neighbor_fit (v : CandidateFront) (floor : ℕ) {w : ℕ}
    (word : v.parentEnd floor < 2^w) (i : Fin 3) : (v.rawNeighborBank floor i).Fits w (v.parentEnd floor) := by
  let a := v.peers floor
  let p := v.peer
  have last : p.rawPeers a+3*p.hosts = p.three a := rfl
  have ord := p.ordered a
  have early : p.rawPeers a ≤ p.threshold a :=
    (Nat.le_add_right _ _).trans (last.le.trans (ord.2.1.trans ord.2.2.1))
  have boundary : p.endAddress a ≤ v.parentEnd floor :=
    (show p.endAddress a ≤ v.parentStart floor from Nat.le_add_right ..).trans (v.front_order floor).1
  exact DescentSixParty.ClosedReset.Window.scalar_bank_room
    ((Nat.add_le_add_right (Nat.add_le_add_right early (2*p.hosts)) (span p.hosts)).trans boundary) word i

/-- All endpoint, predecessor, peer and old-hub reads used by the actual emitted
stem expressions lie below the parent phase boundary. -/
theorem masked_ports_fit (v : CandidateFront) (floor : ℕ) (old : v.Originals floor)
    (flags count inverse : Bank) {w : ℕ} (word : v.parentEnd floor < 2^w)
    (countFit : count.Fits w (v.parentEnd floor)) (inverseFit : inverse.Fits w (v.parentEnd floor))
    (hubFit : old.oldHub.Fits w (v.parentEnd floor)) :
    (v.fromOriginals floor old flags count inverse).stems.ports.All (Expr.Fits w (v.parentEnd floor)) := by
  have parent := (DescentResetParentAperture.fits (base:=v.parentStart floor)
    (slots:=v.peer.hosts) (pad:=v.newHosts) word).2.2.2
  exact DescentResetStemMaskedPorts.fits_only ⟨inverse,v.parent floor,v.rawNeighborBank floor,old.oldHub⟩
    count v.peer.oldHosts (v.signedTemplate old.evidence) countFit inverseFit parent (v.masked_neighbor_fit floor word) hubFit

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
