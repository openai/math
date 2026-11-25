import OAI.Hierarchy.DescentRecordedRootBook
import OAI.Hierarchy.DescentPhysicalResetRoots
import OAI.Hierarchy.DescentResetActorCalendar

namespace OAI
/-! Fixed root tables and actor instructions selected at the public reset date. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentSixParty.ResetInput.SourceFrame DescentPackedColony
open DescentPlainTerminal.Suffix DescentFallbackPeriod DescentResetGates DescentContacts DescentSIMDLookup
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable (a : PhysicalReset)
local notation "v" => a.successor
local notation "d" => (v).middle
local notation "n" => (d).rotorBits
local notation "r" => (d).rootDepth

/-- The rotor alphabet is shared across proposals. Its clocks, field sizes and addresses
are numerals determined by the schedule and the previous public site directory. -/
structure Atlas where
  boardDegree : ℕ
  instructionBits : ℕ
  board : NonlinearExpanders.Graph n boardDegree
  packet : ℕ
  C : ℕ
  groupDigits : ℕ
  batches : ℕ
  layerBits : ℕ
  factor : ℕ
  primitive : CanonicalTag (2^n)→Cell instructionBits
  directions : Ports a.ports
  hostIndex : Bank

variable {a} (z : a.Atlas) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (roots : a.RootInputs)
local notation "phase" => a.stencilPhase sh floor count hub g Y
local notation "E" => a.estimator floor
local notation "rc" w => a.rootPhase sh floor count hub g Y roots w

def atlasBook (w : ℕ) :=
  let code : DescentResetHostSize.Code r:=⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  let page : RootPage r (2^n):=(false,.inr (code,none))
  (rc w).issuedBook E (phase).S (phase).X (phase).base (phase).bank g z.directions z.hostIndex (.lit (a.c/2))
    a.depthCut a.classBound a.fullBudget (phase).S.total a.ports z.board z.packet z.C z.groupDigits z.batches z.layerBits
    z.factor z.primitive page

/-- Exact equality of public dimensions is enough to type the previously selected actor queries. -/
structure ActorFit : Prop where
  count : (v).actor.shapes=(DescentDenseHostOrder.roster z.board r roots.Ht).card

variable (w : ℕ)
def atlasActors (size : ActorFit z roots) : (v).actor.Inputs :=
  let book:=atlasBook z sh floor count hub g Y roots w
  let line : Bank:=⟨(phase).output,Nat.clog 2 ((v).actor.hosts*(v).actor.chunksPerHost)⟩
  ⟨count,(E).depthRows,book.common (rc w).projectionEnd (v).actor.hosts,a.ports,2^roots.Ht,
    fun j=>headerControl r a.ports (ActorSetup.shapeAt z.board r roots.Ht (j.cast size.count)),
    fun j=>opcode r (ActorSetup.shapeAt z.board r roots.Ht (j.cast size.count)),.lookup line .row⟩

theorem atlas_previous :
    let book:=atlasBook z sh floor count hub g Y roots w
    book.previousNeighbors=(phase).X.roster ∧ book.previousHubs=(phase).X.hubs ∧
    book.shapes=2^roots.Ht ∧ book.originalBits=some (phase).S.n :=⟨rfl,rfl,rfl,rfl⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
