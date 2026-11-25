import OAI.Computability.BorderVNP.DiagonalAcquiredRosterIssuance
import OAI.Computability.BorderVNP.DiagonalOwnerTablesOnNativeCalls
import OAI.Computability.BorderVNP.DiagonalNativeSelectedContinuation

/-! # Original tables and issued cells on a measured native call -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

universe u

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

variable {decoder limit burst privateSize core roster taskBase routed}

/-- A single retained acquisition supplies the owner table and the genuine
issued cell records on exactly the decoder's measured continuation. -/
noncomputable def PreparedHistoryDecoder.partsOfOwnerAndHeld
    {saved : parsedFields → (z : barePrefix) → nativeAt(z) → Type*}
    (owner : decoder.OwnerBaseOperation limit burst privateSize core roster taskBase routed)
    (held : decoder.HeldIssuance limit burst privateSize core roster taskBase routed saved)
    (acquire : ∀ f : parsedFields, Σ ss : nativeAt(front(f)), has(f,front(f),ss) × saved f (front(f)) ss)
    (calls : NativeCalls id B limit burst privateSize (native(saved,acquire))) :
    let nsel := nativeNext id B limit burst privateSize (native(saved,acquire)) calls
    let actualTeam := supportedTeam id B limit burst privateSize nsel
    let actualPrep := (decoder.supported limit burst privateSize nsel routeAt reportAt routed).val
    (a : parsedFields → Fin (R+1) → ℕ) ×
      PLift (PreparedOwned.OwnerTablesAt actualTeam actualPrep (fun h => (core h).cells) roster.team a) ×
        ((f : parsedFields) → CoreDirectory.Issued core roster.ports roster.site roster.bundles roster.charts roster.rows
          actualTeam actualPrep f) := by
  let ownership := owner saved acquire calls
  exact ⟨ownership.val, ⟨ownership.property⟩, (held.acquire acquire).issuedTable.onCalls calls⟩

local notation3 (prettyPrint := false) "atTeam(" nsel ")" => supportedTeam id B limit burst privateSize nsel
local notation3 (prettyPrint := false) "atPrep(" nsel ")" =>
  (decoder.supported limit burst privateSize nsel routeAt reportAt routed).val

/-- Run the requested operation on one fixed, measured input, with every
owner row and every original issued cell drawn from that same input. -/
noncomputable def PreparedHistoryDecoder.applyNativeSelection
    {saved : parsedFields → (z : barePrefix) → nativeAt(z) → Type*}
    (owner : decoder.OwnerBaseOperation limit burst privateSize core roster taskBase routed)
    (held : decoder.HeldIssuance limit burst privateSize core roster taskBase routed saved)
    (family : (nsel : NativeNext id B limit) → (a : parsedFields → Fin (R+1) → ℕ) →
      PreparedOwned.OwnerTablesAt (atTeam(nsel)) (atPrep(nsel)) (fun h => (core h).cells) roster.team a →
      ((f : parsedFields) → CoreDirectory.Issued core roster.ports roster.site roster.bundles roster.charts
        roster.rows (atTeam(nsel)) (atPrep(nsel)) f) → Sort u)
    (handler : ∀ nsel a owners issued, family nsel a owners issued)
    (acquire : ∀ f : parsedFields, Σ ss : nativeAt(front(f)), has(f,front(f),ss) × saved f (front(f)) ss)
    (calls : NativeCalls id B limit burst privateSize (native(saved,acquire))) :=
  let parts := PreparedHistoryDecoder.partsOfOwnerAndHeld owner held acquire calls
  handler (nativeNext id B limit burst privateSize (native(saved,acquire)) calls)
    parts.1 parts.2.1.down parts.2.2

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
