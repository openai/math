import OAI.Hierarchy.DescentProfiledPositionBudget
import OAI.Hierarchy.DescentNamedProfiledNumbers
import OAI.Hierarchy.DescentRegisteredOrdinaryOperandRates
import OAI.Hierarchy.DescentRegisteredPrimitiveRoof
import OAI.Hierarchy.DescentRegisteredOrdinarySurvivors

namespace OAI
/-! # An ordinary offer comes from a cut of the original named execution -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentCompiler DescentCompiler.TerminalScale DescentMixedRouter DescentResetInvoice
open Chronology Chronology.RegisterTimeline DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing ProtocolRAM Filter
open ThreeFlat Routing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (k i p f g : ℕ)
local notation "wire_" => S.epochPower^S.priceExponent
local notation "s_" => S.firstWidth G.b p
local notation "q_" => (1/((s_:ℝ)*(wire_:ℝ)):ℝ)
local notation "fee_" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u_" => q_*(wire_:ℝ)
local notation "pins_" A:arg X:arg => (Σ _ : Fin S.copies,Fin (Fintype.card (Port A (X:Catalyst.Approximation F _ A).width)))

attribute [local irreducible] Origin.source Origin.archivePackage

structure OrdinaryCut where
  copies : ℕ
  inputs : ℕ
  original : Approximation F copies inputs
  n : ℕ
  degree : ℕ
  C : ℕ
  R : ℕ
  price_nonnegative : 0≤u_
  fee_nonnegative : 0≤fee_
  radix : S.radix=2^k
  run : Epochs G price_nonnegative fee_nonnegative (h:=degree) (C:=C)
    (Ht:=GroupStage.depthBound (atRound S.rounds) n f g) (t:=S.rounds) S.height
    (initial original S.copies s_ (S.groupCount 0) k (S.initialDigits radix))
  selection : (Epochs.finish G price_nonnegative fee_nonnegative run).Choice
  branch : Branch original G S (p:=p) (n:=n) (h:=degree) (C:=C) (f:=f) (g:=g) radix R run selection
  world : MarkedWorld F 0 (pins_ inputs original) (fun _=>s_*1)
  sourceGrain : ℕ
  sourceDegree : ℕ
  source : Reached world G q_ fee_ S k i sourceGrain sourceDegree wire_ s_
  rate : ℝ
  input : StageInput world G rate fee_
  nonnegative : 0≤fee_
  choice : (input.result nonnegative).Choice
  norm : Normalize ((input.result nonnegative).state choice)
  targetGrain : ℕ
  targetDegree : ℕ
  target : Reached norm.result G q_ fee_ S k (i+1) targetGrain targetDegree wire_ s_
  ticket : OrdinaryLink source nonnegative input choice norm target
  before : Path branch.origin.source source
  after : Path target branch.target
  joined : (Path.ordinary before ticket).append after=branch.path

namespace OrdinaryCut
variable {G S k i p f g} (c : OrdinaryCut G S k i p f g)
def Pins := pins_ c.inputs c.original
end OrdinaryCut

variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
  (t reset τ drift degreeMax B h : ℕ)
local notation "J_" => Nat.log 2 h/(2*B)
local notation "tail_" => tail τ J_
local notation "cell_" => groupBits t J_ (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "schedule_" M:arg =>stageNumbers G t J_ f g reset M tail_

structure ProfiledOrdinaryOffer where
  slot : ProfiledPosition G board op t f g reset τ drift degreeMax B h
  cut : OrdinaryCut G (schedule_ slot.sites) cell_ slot.age slot.p f g
  seats : slot.menu.seats slot.age≤(schedule_ slot.sites).batch
  firstWidth : (schedule_ slot.sites).firstWidth G.b slot.p≤h

namespace ProfiledOrdinaryOffer
variable {G board op t f g reset τ drift degreeMax B h}
local notation "offers_" H:arg =>ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B H
variable (x : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h)
local notation "z_" => x.slot
local notation "Sx_" => schedule_ (z_).sites
local notation "P_" => (z_).position.ports

def Pins :=x.cut.Pins
def books := OrdinaryBooks.atDate G Sx_ op g cell_ (z_).age (z_).p tail_ drift (z_).degree h ((z_).menu.seats (z_).age) P_
def base := x.books.onTicket x.cut.ticket g tail_ (z_).p f h ((z_).menu.seats (z_).age) (P_).venue.lanes (P_).io.roster (z_).menu.ordinary
def stageFloor := x.base.stageStart (z_).position.floor
def model : PhysicalOrdinary F x.Pins := x.base.registeredFrom P_ x.stageFloor
def endAt :=x.model.fullEnd (z_).position.floor


theorem core :
    x.model.staticCore x.stageFloor=
      PhysicalOrdinary.StaticCore.atAge G Sx_ g cell_ (z_).age (z_).p h ((z_).menu.seats (z_).age) (z_).position.floor (P_).io.roster :=
  Branch.registered_static_core x.cut.original G Sx_ x.cut.branch x.cut.ticket x.cut.before x.cut.after x.cut.joined
    op tail_ drift (z_).degree h ((z_).menu.seats (z_).age) (z_).position.floor P_ (z_).menu.ordinary

theorem model_floor : x.model.stageStart (z_).position.floor=x.stageFloor:=rfl
theorem prices : x.model.OperandWidths h :=
  DatePorts.ordinary_operand_widths P_ x.cut.ticket op g tail_ (z_).p f drift (z_).degree h ((z_).menu.seats (z_).age)
    (z_).position.floor (z_).menu.ordinary

theorem primitive_shape : PhysicalOrdinary.RegistryPrimitiveShape G Sx_ g cell_ (z_).age (z_).p op tail_ drift
    (z_).degree h ((z_).menu.seats (z_).age) P_ x.stageFloor x.base:=
  Branch.registered_primitive_geometry x.cut.original G Sx_ x.cut.branch x.cut.ticket x.cut.before x.cut.after x.cut.joined
    op tail_ drift (z_).degree h ((z_).menu.seats (z_).age) (P_).venue.lanes P_ (P_).io.roster (z_).menu.ordinary x.stageFloor (z_).active

theorem span_le : x.endAt-(z_).position.floor≤x.model.fullCeiling:=by
  have spent :=x.model.full_spent (z_).position.floor
  unfold endAt
  omega

end ProfiledOrdinaryOffer
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage
