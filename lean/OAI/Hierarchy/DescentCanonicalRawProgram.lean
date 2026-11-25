import OAI.Hierarchy.DescentCanonicalPeerGeometry
import OAI.Hierarchy.DescentResetPeerOldReadings
import OAI.Hierarchy.DescentCanonicalFrontScene

namespace OAI
/-! # The calendar prints the same private, two signed and trunk probes as the attained reset -/
namespace Hierarchy.DescentResetPeerUnionRAM.RawTables
open DescentDenseHostOrder DescentResetStemDecoder
noncomputable section
set_option quotPrecheck false
private def oldTemplate {n h : ℕ} (board : NonlinearExpanders.Graph n h) (r height : ℕ)
    (s : Bool) (j : Fin (2*DescentFallbackShapeTable.rows r (2^n))) :=
  localTemplate board r height s j.val

theorem original_template {n n' h r r' : ℕ} (board : NonlinearExpanders.Graph n h)
    (other : NonlinearExpanders.Graph n' h) (dim : n=n') (graphs : HEq board other)
    (residual : r=r') (height : ℕ) :
    HEq (oldTemplate board r height) (oldTemplate other r' height) := by
  subst n'; subst r'
  cases eq_of_heq graphs
  rfl

/-- Addresses, arities and all four literal tables determine the native code. -/
theorem program_congr {n n' h k k' ar ar' : ℕ} (a : NonlinearExpanders.Graph n h)
    (b : NonlinearExpanders.Graph n' h) (dim : n=n') (boards : HEq a b) (key : k=k')
    (height : ℕ) (first second : Layout) (same : first=second) (heads : ar=ar')
    (template : Bool→Fin ar→Option (Fin first.shapes×Fin first.shapes))
    (other : Bool→Fin ar'→Option (Fin second.shapes×Fin second.shapes)) (rows : HEq template other) (w : ℕ) :
    program a k height first template w=program b k' height second other w := by
  subst n'; subst k'; subst ar'; subst second
  cases eq_of_heq boards
  cases eq_of_heq rows
  rfl
end
end Hierarchy.DescentResetPeerUnionRAM.RawTables

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentSIMDLookup
open DescentResetLocalRoster ProtocolRAM
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
variable (floor : ℕ) (old : EarlierBanks D k ((calendar.take i).prod*256) n)
local notation "E" => (calendarOriginals S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR
  calendar floor old).evidence
local notation "area" => (A).rawTables floor
local notation "next" => (A).oldKeys floor
local notation "geom" => peerLayout B next H oldM (A).privateBits ((A).stemField+2) (A).peer.bits

theorem canonical_raw_program (w : ℕ) :
    RawTables.program (E).board (E).rootBits (E).depth area (E).template w=
      RawTables.program B.reset.graph r Ht geom (peerTemplate B) w := by
  have key : k=r:=by rw [B.keyWidth,B.commonDepth,Nat.add_sub_cancel_left]
  have heads : 2*DescentFallbackShapeTable.rows k (2^n)=2*DescentFallbackShapeTable.rows r (2^B.reset.n) :=by
    rw [←key,B.dimension]
  exact RawTables.program_congr ctl.board B.reset.graph B.dimension.symm B.graph.symm key Ht _ _
    (canonical_peer_layout B oldM nextM field metaBits calendar floor) heads _ _
    (RawTables.original_template ctl.board B.reset.graph B.dimension.symm B.graph.symm key Ht) w

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
