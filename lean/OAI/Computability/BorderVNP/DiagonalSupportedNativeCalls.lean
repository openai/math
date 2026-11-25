import OAI.Computability.BorderVNP.DiagonalSupportedSparseTeams

/-! # The selected native sparse continuations and their readbacks -/

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

variable (limit burst : ℕ) (cap : TeamScales.width n (1/2)≤burst)

universe u v

/-- A selected native continuation with its absolute boot bound and
the exact post-call readout certified for that continuation. -/
structure SelectedCalls (paidBound : Prop) {Continuations : Type u} (readback : Continuations → Prop) where
  /-- The original absolute boot times fit the deployed limit. -/
  paid : paidBound
  /-- The continuations selected on all genuinely productive exteriors. -/
  next : Continuations
  /-- The cell readback on every attained tuple for these same continuations. -/
  reads : readback next

private abbrev selectedBy {cost : Type v} {fits measured : cost → Prop}
    {continuations : Type u} {reads : continuations → Prop} (paid : Prop)
    (_ : ∀ c, fits c → measured c → ∃ k, reads k) := SelectedCalls paid reads

/-- Sparse sources of the actual complete tuples at the common physical boot. -/
abbrev NativeSources := ∀ (x : X) (p : JointPrefix id (U(x))) u, SparseSource id (U(x)) (p u)

/-- The selected family uses exactly the joint sparse team's native readback
predicate, on the prefix domain measured by the original boot. -/
abbrev NativeCalls (source : NativeSources id B) :=
  selectedBy (∀ x u, (B x u).used≤limit)
    (fun charges fits measured => exists_sparse_teams id B limit burst cap charges fits measured source)

/-- Select the continuations once, before inspecting any private result. -/
noncomputable def nativeCalls (source : NativeSources id B)
    (paid : ∀ v u, (B v u).used≤limit) (charges : PhaseCharges)
    (fits : charges.core+charges.before+charges.argumentsCalls+charges.finish+charges.reader≤limit)
    (measured : ∀ x : X, JointClock id (U(x)) (used(x)) charges) : NativeCalls id B limit burst cap source :=
  let checked := exists_sparse_teams id B limit burst cap charges fits measured source
  ⟨paid,checked.choose,checked.choose_spec⟩

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
