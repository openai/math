import OAI.Hierarchy.DescentCanonicalRawProgram
import OAI.Hierarchy.DescentContactPeerDirectoryReached

namespace OAI
/-! # The donor and contact programs use one set of previously issued physical operands -/
namespace Hierarchy.DescentContactDonorFront.Shape
open DescentContactSenderDate ProtocolRAM
noncomputable section
set_option quotPrecheck false
abbrev Input (s : Shape) := Prior s.degree s.lows s.cap s.n s.residual

def move {s t : Shape} (which : s=t) (src : s.Input) : t.Input := which ▸ src

theorem declared {s t : Shape} (which : s=t) (src : s.Input) {base addr : ℕ} (placed : base=addr) (w : ℕ) :
    s.program base src w=t.program addr (move which src) w := by
  subst t;subst addr;rfl

theorem contact_congr {s t : Shape} {base addr seats other bits k w : ℕ}
    (which : s=t) (place : base=addr) (number : seats=other)
    (src : s.Input) (board : NonlinearExpanders.Graph s.n k) (graph : NonlinearExpanders.Graph t.n k)
    (same : HEq board graph)
    (room : (s.markers base seats bits).Space (s.oldBoard src) (s.priorSensor base) w)
    (fit : (t.markers addr other bits).Space (t.oldBoard (move which src)) (t.priorSensor addr) w) :
    (s.markers base seats bits).program board (s.oldBoard src) (s.priorSensor base) room=
      (t.markers addr other bits).program graph (t.oldBoard (move which src)) (t.priorSensor addr) fit := by
  subst t;subst addr;subst other
  cases eq_of_heq same
  rfl
end
end Hierarchy.DescentContactDonorFront.Shape

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentSIMDLookup
open DescentContactDonorFront DescentResetLocalRoster ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (oldM nextM field metaBits : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR calendar
local notation "H" => S.hostSize i
local notation "Ht" => GroupStage.depthBound D n f g
local notation "cap" => (calendar.take i).prod*256
local notation "r" => B.reset.k-B.terminals.commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster B.reset.graph r Ht).card
local notation "bits" => (A).peer.bits
local notation "donor" => peerDonorShape B H oldM field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
variable (paid : input.placement.cap=(calendar.take i).prod*256) (floor : ℕ) (old : EarlierBanks D k ((calendar.take i).prod*256) n)
local notation "eqShape" => canonical_donor B oldM nextM field metaBits calendar paid
local notation "U" => (Shape.move eqShape old.donor)
local notation "next" => (A).oldKeys floor
local notation "L" => peerLayout B next H oldM (A).privateBits ((A).stemField+2) bits
local notation "lo" => (L).endAddress
local notation "e" => calendarOriginals S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR
  calendar floor old
variable (flags count inverse : Bank) {w : ℕ}
local notation "scene" => (A).fromOriginals floor e flags count inverse

theorem canonical_donor_program (room : (A).SceneRoom floor scene w) :
    ((A).donorPhase floor scene room).program=(donor).program lo U w :=
  Shape.declared eqShape old.donor (canonical_raw_end B oldM nextM field metaBits calendar floor) w

theorem canonical_contact_program (room : (A).SceneRoom floor scene w)
    (space : ((donor).markers lo shelf bits).Space ((donor).oldBoard U) ((donor).priorSensor lo) w) :
    ((A).contactPhase floor scene room).program=
      ((donor).markers lo shelf bits).program B.reset.graph ((donor).oldBoard U) ((donor).priorSensor lo) space := by
  exact Shape.contact_congr eqShape (canonical_raw_end B oldM nextM field metaBits calendar floor)
    B.public_hub_slots.symm old.donor ctl.board B.reset.graph B.graph.symm room.contact space

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
