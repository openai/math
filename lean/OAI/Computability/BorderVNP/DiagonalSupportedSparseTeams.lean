import OAI.Computability.BorderVNP.DiagonalJointBootedSupport
import OAI.Computability.BorderVNP.DiagonalJointSparseReadback

/-! # The supported signed teams read the exact sparse cells of every complete tuple -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine CellMacro.Generator BorderVNP.Cube
open PinStart CellDispatch ScheduleClock
open scoped Classical
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option maxHeartbeats 1300000

variable {R r t d link inner n w dim box lanes selectors symbols : ℕ} {Edge : Type}
    (id : TableEntry dim box lanes selectors symbols → ℕ)
    {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w}
    {args : Fin (R+1) → UnitAddresses} {pin : Fin d → Bool}
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)
local notation3 (prettyPrint := false) "X" => {ext // PositiveExterior G args pin w ext ∧
  preCallSupport (fun x u => (B x u).start) id ext}
local notation3 (prettyPrint := false) "bt(" x ", " u ")" => B ⟨Subtype.val x,(Subtype.property x).1⟩ u
local notation3 (prettyPrint := false) "U(" x ")" => fun u => BootedPinStart.start (bt(x,u))
local notation3 (prettyPrint := false) "used(" x ")" => fun u => BootedPinStart.used (bt(x,u))
local notation3 (prettyPrint := false) "logical(" src ")" => fun i => SparseExterior.logicalCell
  ((SparseSource.arguments src).placed i) ((SparseSource.arguments src).extra i) ((SparseSource.arguments src).field i)

/-- Select one true private continuation at each supported team. On all
joint preparations, regardless of later rejection or a zero scalar, its
dispatched cell at an owned ordinal is exactly the cell decoded from the
sparse packet prepared on that tuple. The same prefix may be compared
with any number of different complete tuples. -/
theorem exists_sparse_teams (limit burst : ℕ) (cap : TeamScales.width n (1/2) ≤ burst)
    (charges : PhaseCharges)
    (fits : charges.core+charges.before+charges.argumentsCalls+charges.finish+charges.reader ≤ limit)
    (measured : ∀ x : X, JointClock id (U(x)) (used(x)) charges)
    (source : ∀ (x : X) (a : JointPrefix id (U(x))) u, SparseSource id (U(x)) (a u)) :
    ∃ next : (x : X) → (u : Fin (R+1)) →
      let b := bt(x,u)
      PositiveContinuation id SparseExterior.driver n (pub u) b.start.routines b.start.bank b.memory b.pins b.used limit,
    ∀ (x : X) (a : JointPrefix id (U(x))) u,
      let team := supportedTeam id B limit burst cap next x u
      let frame := Frame.ofMemory team.pub (team.postMemory (a u))
      ∀ i < frame.count, readings (team.postMemory (a u)) (frame.address i)=frame.team →
        (team.generated (a u)).cell i = (logical(source x a u)) i := by
  let ok (x : X) : jointSupport id (U(x)) :=
    (preCallSupport_iff (fun z u => (B z u).start) x.val x.property.1).mp x.property.2
  let candidate (x : X) (u : Fin (R+1)) :=
    joint_sparse_continuation_on_inputs id (U(x)) (used(x)) charges (ok x) fits (measured x) (source x) u
  refine ⟨fun x u => (candidate x u).choose,?_⟩
  exact fun x a u => (candidate x u).choose_spec a

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
