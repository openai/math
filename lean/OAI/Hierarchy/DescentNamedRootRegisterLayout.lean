import OAI.Hierarchy.DescentDatedRootRegisterJoin
import OAI.Hierarchy.DescentDatedRolePriorFrames
import OAI.Hierarchy.DescentNamedFinalInputs
import OAI.Hierarchy.DescentResetHubRectangle

namespace OAI
/-! # The actual named date uses the admitted prior-root rectangle and its saved addresses -/
namespace Hierarchy.DescentSixParty.ClosedReset
open DescentCompiler DescentDenseHostOrder DescentPrimitiveBirth
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset cap ctl)
local notation "r" => B.reset.k-B.terminals.commonDepth
local notation "h₀" => GroupStage.depthBound D n f g

/-- Retain all public word and lane parameters of the dated compiler and identify
its source hosts, target coordinates and rotor with the genuine mathematical reset. -/
def rootRegisterLayout (Q : Layout) : Layout:=
  { Q with
    placement := { Q.placement with
      oldHosts := S.hostSize i
      newHosts := S.hostSize (i+1)
      shapes := (DescentDenseHostOrder.roster B.reset.graph r h₀).card
      groups := S.groupCount (i+1)
      blocks := 2^k }
    residual := r
    rotorBits := B.reset.n }


end
end Hierarchy.DescentSixParty.ClosedReset

namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty DescentDenseHostOrder
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset cap ctl)
variable (p drift degree payload e prev M nextM : ℕ) (old : Prior) (base : ℕ)
local notation "V" => fromBoard G S ctl.board k tail i p f g drift degree payload e prev M nextM C ctl.bitsR old base

theorem born_layout (degreeRead : old.venue.degree=D) :
    B.rootRegisterLayout (V).birth=(V).birth:=by
  have axis : B.reset.k-B.terminals.commonDepth=k:=by rw [B.keyWidth,B.commonDepth];omega
  have slots := B.public_hub_slots
  rw [axis] at slots
  simp only [ClosedReset.rootRegisterLayout,fromBoard,AtomSchedule.retainedPlacementCalendar,
    degreeRead,axis,B.dimension,slots]

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentPrimitiveBirth DescentSIMDLookup DescentSixParty.Chronology DescentFallbackPeriod.Projected
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "V" => a.successor
local notation "Q" => (V).birth
local notation "mid" => (V).middle
local notation "rc" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w

private theorem cast_fields {A B X Y : ℕ} {K : Type} (f : Fin A→Fin B→K) (ea : X=A) (eb : Y=B) :
    HEq f (fun (x : Fin X) (y : Fin Y)=>f (x.cast ea) (y.cast eb)):=by
  subst X;subst Y;rfl

/-- Only scalar layout coordinates enter this equality. The two axes of each
lookup are the old source host and the high block in the measured root packet. -/
theorem original_guards (base H J M r n D : ℕ) (head : base=(rc).headerEnd u.book)
    (hosts : H=(mid).rootHosts) (groups : J=(mid).rootGroups) (lanes : M=(mid).rootLanes)
    (residual : r=(mid).rootDepth) (bits : n=(mid).rotorBits) (degree : D=(mid).rootDegree) :
    HEq (DescentPrimitiveBirth.guards base H J M r n D) z.guards:=by
  subst base;subst H;subst J;subst M;subst r;subst n;subst D
  exact cast_fields _ z.guardRoots (congrArg (·+1) z.guardDepth)

open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "beforeRoots" => a.throughStencil u.shape floor u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "beforeTicks" => a.throughStencilTicks u.shape floor u.count u.hub u.g u.Y u.sourceRows u.oldDegree w

/-- The prepared rotor pages survive the actual operand, venue, retained and
classification passes on this date. -/
theorem reached_guard_frame (ready : u.Ready) (fit : z.Room) {before measured mid₀ : Memory w}
    (earlier : (beforeRoots).Exec before measured beforeTicks)
    (operands : u.throughOperandDate.Runs before mid₀) (j : ℕ) (inside : j<(rc).preparedEnd u.book) :
    z.classImage mid₀ j=(rc).preparedImage u.book u.bookFits measured j:=by
  have bound : (rc).preparedEnd u.book≤(V).finalEnd (a.rebased floor):=by
    rw [ready.rootEnd]
    obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=ready.ordered
    omega
  have after : (V).finalEnd (a.rebased floor)≤(V).fullEnd (a.rebased floor):=by
    obtain ⟨first,last⟩:=(V).complete_after (a.rebased floor)
    exact first.trans last
  apply (z.low_class mid₀ fit j (inside.trans_le (bound.trans after))).trans
  apply (z.venue_prior_frame fit mid₀ j (inside.trans_le bound)).trans
  apply u.prefix_unchanged ready _ operands j inside
  intro P R K machine
  exact Procedure.Exec.then earlier ((rc).prepared_any u.book u.bookFits measured).1 machine

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
