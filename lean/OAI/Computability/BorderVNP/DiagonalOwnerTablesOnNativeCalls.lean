import OAI.Computability.BorderVNP.DiagonalSourceRosterIssuer
import OAI.Computability.BorderVNP.DiagonalBeforeIssuedCalls
import OAI.Computability.BorderVNP.DiagonalIssuedFactFamily
import OAI.Computability.BorderVNP.DiagonalPreparedOwnerTableBase

/-! # The returned owner tables on a measured native call -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve axes groups cap dim tally box lanes selectors symbols : ℕ}
    {Edge Hist : Type} (id : TableEntry axes box lanes selectors symbols → ℕ)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link)
    (headerWidth : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)
    (code : Hist ↪ (Fin reserve → Bool))
    (args : Fin (R+1) → UnitAddresses) (fixed : Block (R+1)) (hw : 0<w)
    (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)
    (decoder : PreparedHistoryDecoder SparseExterior.driver id G pub reg pin L headerWidth code args fixed hw size base fit B)
    (limit burst : ℕ) (privateSize : TeamScales.width n (1/2) ≤ burst)

open Crossing Packing.Inherited Packing.BottomReports Cube.Physical Cube.Physical.NativeAssignments
open DiagonalTallyCellReports RoutingISA.CompactMachine
variable {D nativeGroups : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Hist → Network D P bits} {count : Hist → ℕ}
    (core : ∀ h, CoreDirectory (N h) axes nativeGroups (count h) box lanes selectors R)

variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}
    (roster : SourceRoster core d symbols) (taskBase : ℕ)

variable (routed : ∀ (i : Fin d → Bool) (h : Hist) (c : Fin ((R+1)*dim*tally) → Bool),
    (Σ p : Physical.Broadcast axes groups cap, ParsedPreCall G args pin L fixed hw size base fit headerWidth
      (fun x u => (B x u).start) (fun u => (args u).ibase) (fun u => (args u).hbase)
      (fun u => (args u).starbase) (fun _ _ => rfl) id i ⟨code h,p,c⟩) ≃
      Σ v : (core h).Route symbols, CoreDirectory.Proposals core roster.charts roster.rows i h v)

local notation3 (prettyPrint := false) "parsedFields" => PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool)
  (fun h : Hist => (core h).Route symbols) (CoreDirectory.Proposals core roster.charts roster.rows)
local notation3 (prettyPrint := false) "barePrefix" => (x : {ext // PositiveExterior G args pin w ext}) ×
  ((u : Fin (R+1)) → (B x u).start.Prefix id)
local notation3 (prettyPrint := false) "nativeAt(" z ")" => (u : Fin (R+1)) →
  PinStart.SparseSource id (fun t => (B ((z).1) t).start) ((z).2 u)

local notation3 (prettyPrint := false) "routeAt" => (fun h : Hist => (core h).Route symbols)
local notation3 (prettyPrint := false) "reportAt" => CoreDirectory.Proposals core roster.charts roster.rows
local notation3 (prettyPrint := false) "front(" f ")" => routedBareTuple routed f
local notation3 (prettyPrint := false) "has(" f "," z "," inputs ")" =>
  PLift (∀ u : Fin (R+1), CoreDirectory.IssuedReceipt core roster.ports roster.site roster.bundles roster.charts roster.rows
    f u (pub u) (((Sigma.snd z) u).2.val.2.2) taskBase
    (roster.team (Sigma.fst (Sigma.snd f)) (Sigma.fst (Sigma.snd (Sigma.snd f)))) ((inputs u).logicalAt))

local notation3 (prettyPrint := false) "record(" saved ")" => (fun (g : parsedFields) (z : barePrefix) (ss : nativeAt(z)) =>
  has(g,z,ss) × saved g z ss)
local notation3 (prettyPrint := false) "native(" saved "," acquire ")" => decoder.issuedNativeFamily routed (record(saved)) acquire
local notation3 (prettyPrint := false) "next(" calls ")" => (fun z u => @SelectedCalls.next _ _ _ calls z u)
local notation3 (prettyPrint := false) "team(" calls ")" => supportedTeam id B limit burst privateSize (next(calls))
local notation3 (prettyPrint := false) "prep(" calls ")" =>
  (decoder.supported limit burst privateSize (next(calls)) routeAt reportAt routed).val

/-- Read the owner column from the original issued receipt on the very source
and continuation selected by these measured native calls. -/
theorem PreparedHistoryDecoder.ownerTablesOnCalls
    (saved : parsedFields → (z : barePrefix) → nativeAt(z) → Type*)
    (acquire : ∀ f : parsedFields, Σ source : nativeAt(front(f)), has(f,front(f),source) × saved f (front(f)) source)
    (calls : NativeCalls id B limit burst privateSize (native(saved,acquire))) :
    PreparedOwned.OwnerTablesAt (team(calls)) (prep(calls)) (fun h => (core h).cells) roster.team (fun _ _ => taskBase) := by
  intro f u
  have facts := decoder.issuedFamilyFacts routed limit burst privateSize (next(calls)) (record(saved)) acquire f
  exact (facts.1.down u).ownerTable

/-- The selected public base and all its returned owner rows for the same
actual native call, with its input acquisition retained in the call's type. -/
noncomputable def PreparedHistoryDecoder.ownerBaseOnCalls
    (saved : parsedFields → (z : barePrefix) → nativeAt(z) → Type*)
    (acquire : ∀ f : parsedFields, Σ source : nativeAt(front(f)), has(f,front(f),source) × saved f (front(f)) source)
    (calls : NativeCalls id B limit burst privateSize (native(saved,acquire))) :
    {a : parsedFields → Fin (R+1) → ℕ //
      PreparedOwned.OwnerTablesAt (team(calls)) (prep(calls)) (fun h => (core h).cells) roster.team a} :=
  PreparedOwned.certifiedTableBase (team(calls)) (prep(calls)) (fun h => (core h).cells) roster.team taskBase
    (decoder.ownerTablesOnCalls limit burst privateSize core roster taskBase routed saved acquire calls)

local notation3 (prettyPrint := false) "baseOperation" => decoder.ownerBaseOnCalls limit burst privateSize core roster taskBase routed

/-- The operation on this particular reader and route; keeping its dependent call
arguments under this type lets the calendar specialize it before supplying the cells. -/
noncomputable def PreparedHistoryDecoder.OwnerBaseOperation : Type _ := type_of% baseOperation

/-- The complete base and owner certificate on the given source roster. -/
noncomputable def PreparedHistoryDecoder.ownerBaseOperation :
    decoder.OwnerBaseOperation limit burst privateSize core roster taskBase routed := baseOperation

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
