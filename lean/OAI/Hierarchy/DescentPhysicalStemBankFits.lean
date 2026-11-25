import OAI.Hierarchy.DescentCanonicalFrontScene

namespace OAI
/-! # Register bounds already certified by the real masked stem expressions -/
namespace Hierarchy.DescentResetStemMaskedPorts
open DescentResetStemTemplatePorts ProtocolRAM
theorem room_of_operands {K H P S w stop : ℕ} (B : Banks) (number : Bank)
    (template : Fin K→Option (Fin S×Fin S)) (sample : Fin K)
    (ready : (ports B number P template).All (Expr.Fits w stop))
    (here : H≤B.here.size) (parent : H≤B.parent.size)
    (peers : ∀i,P*S≤(B.neighbors i).size) (prior : P≤B.hub.size) :
    Room B H P S w stop ∧ number.Fits w stop :=by
  have seen := ready.here
  have old := ready.hub sample
  exact ⟨⟨seen.2.2.1.1,here,old.2.2.1.2.1,parent,fun i=>(ready.near i).1,peers,old.2.2.1.1,prior⟩,
    seen.2.1.1⟩
end Hierarchy.DescentResetStemMaskedPorts

namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentResetStemTemplatePorts DescentDyadicSpan ProtocolRAM
variable (v : CandidateFront) (base : ℕ) (old : v.Originals base) (flags number inverse : Bank)
local notation "sc" => v.fromOriginals base old flags number inverse
local notation "regs" => v.stemRegisters base sc old.oldHub

/-- The compact inverse page contains one word for every actual actor. The
parent page has room for the entire padded host scan. -/
theorem stem_room_active {w rows : ℕ} (safe : v.SceneRoom base sc w) (sample : Fin (2*v.oldTicketCount))
    (active : rows ≤ v.newHosts) (here : rows ≤ inverse.size) (prior : v.peer.oldHosts≤old.oldHub.size) :
    Room regs rows v.peer.oldHosts v.peer.shapes w (v.parentEnd base) ∧ number.Fits w (v.parentEnd base) :=
  DescentResetStemMaskedPorts.room_of_operands regs number (v.signedTemplate old.evidence) sample
    safe.stems.ports here (active.trans (span_ge _)) (fun _=>span_ge v.peer.hosts) prior

theorem stem_room {w : ℕ} (safe : v.SceneRoom base sc w) (sample : Fin (2*v.oldTicketCount))
    (here : v.newHosts ≤ inverse.size) (prior : v.peer.oldHosts ≤ old.oldHub.size) :
    Room regs v.newHosts v.peer.oldHosts v.peer.shapes w (v.parentEnd base) ∧ number.Fits w (v.parentEnd base) :=
  v.stem_room_active base old flags number inverse safe sample le_rfl here prior


end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
