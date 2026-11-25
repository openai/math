import OAI.Computability.BorderVNP.DiagonalIssuedDispatch
import OAI.Computability.BorderVNP.DiagonalRoutedCoreReadback
import OAI.Computability.BorderVNP.DiagonalSupportedNativeCalls

/-! # Issued all-zero private banks on the supported native continuations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine CellMacro.Generator BorderVNP.Cube
open PinStart CellDispatch ScheduleClock
open scoped Classical
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option maxHeartbeats 2600000

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
    (source : NativeSources id B)


open Crossing Packing.Inherited Packing.BottomReports Packing.CellAddresses
open Cube.Physical Cube.Physical.NativeAssignments DiagonalTallyCellReports

variable (selected : NativeCalls id B limit burst cap source)
    {D axisCount : ℕ} {P Hist Raw : Type} [Fintype P] {bits : P → ℕ}
    {N : Hist → Network D P bits} {blocks : Hist → ℕ}
    (core : ∀ h, CoreDirectory (N h) dim axisCount (blocks h) box lanes selectors R)
    (portSource : Raw → Ports bits) (siteOwner : ∀ h,Fin (core h).siteRows → ℕ)
    (bottom : ∀ h, Fin (core h).cells → List Bundle)
    (charts : Raw → (h : Hist) → (core h).Route symbols → Fin (R+1) → ReportLayout)
    (received : ∀ i h v, ReceivedRows (charts i h v) (core h).cells)
local notation3 (prettyPrint := false) "teams" => supportedTeam id B limit burst cap selected.next
local notation3 (prettyPrint := false) "choices" => CoreDirectory.Proposals core charts received
variable {axes digits : ℕ}
    (prepare : JointBeforeCells (supportedTeam id B limit burst cap selected.next) ≃ PreparedFields Raw Hist (Fin ((R+1)*axes*digits) → Bool)
      (fun h => (core h).Route symbols) (CoreDirectory.Proposals core charts received))
    (out : PreparedFields Raw Hist (Fin ((R+1)*axes*digits) → Bool)
      (fun h => (core h).Route symbols) (CoreDirectory.Proposals core charts received))
local notation3 (prettyPrint := false) "start" => prepare.symm out
local notation3 (prettyPrint := false) "i₀" => out.1
local notation3 (prettyPrint := false) "h₀" => out.2.1
local notation3 (prettyPrint := false) "route₀" => out.2.2.1
local notation3 (prettyPrint := false) "path" => out.2.2.1.val
local notation3 (prettyPrint := false) "rr" => received i₀ h₀ route₀
local notation3 (prettyPrint := false) "execCore" => core h₀
local notation3 (prettyPrint := false) "reports" =>
  (rr).physicalReportEquiv (N h₀) (execCore).cell (execCore).siteID (execCore).edgeID (execCore).portID
    (execCore).programs (execCore).owners (execCore).slot (portSource i₀) (siteOwner h₀) (bottom h₀) path
    (fun _ _ => false) (rr).cells (fun _ => rfl) out.2.2.2.2
local notation3 (prettyPrint := false) "actualCall" =>
  (rr).sourceCall (N h₀) (execCore).cell (execCore).siteID (execCore).edgeID (execCore).portID
    (execCore).programs (execCore).owners (execCore).slot (portSource i₀) (siteOwner h₀) (bottom h₀) path
    (fun _ _ => false) reports

/-- On the supported continuation chosen for each boot, read the true three-word
owner table, the published sparse source and its preserved per-cell input before
guessing any private wire. This assembles the native all-false issuer required
by the core decoder on the inverse of the same prepared source tuple. -/
noncomputable def NativeCalls.issuedOnPrefix
    (who : Fin (execCore).cells → Fin (R+1)) (base : Fin (R+1) → ℕ)
    (owner : ∀ u (i : Fin ((rr).cells u).length), who ((rr).order ⟨u,i⟩)=u)
    (table : ∀ u, OwnerTable ((teams (start).1 u).pub) ((teams (start).1 u).postMemory ((start).2 u))
      ⟨u.val,base u,(execCore).cells⟩ (PositiveTeam.ownerWord who))
    (readback : ∀ u (i : Fin ((rr).cells u).length),
      (source (start).1 (start).2 u).logicalAt ((rr).order ⟨u,i⟩).val=actualCall u i) :
    CoreDirectory.Issued core portSource siteOwner bottom charts received teams prepare out := by
  exact CoreDirectory.issuedFromDispatch core portSource siteOwner bottom charts received teams prepare out who owner
    (fun u => (source (start).1 (start).2 u).logicalAt) base table (selected.reads (start).1 (start).2) readback

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
