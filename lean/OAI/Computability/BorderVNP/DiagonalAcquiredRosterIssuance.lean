import OAI.Computability.BorderVNP.DiagonalTypedRosterIssuance

/-! # Issued calls of the selected native source acquisition -/

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

local notation3 (prettyPrint := false) "issue" =>
  decoder.issuerFromRoster limit burst privateSize core roster taskBase routed

local notation3 (prettyPrint := false) "original(" f ")" => routedBareTuple routed f
local notation3 (prettyPrint := false) "receipts(" f "," z "," ns ")" => PLift (∀ u : Fin (R+1),
  CoreDirectory.IssuedReceipt core roster.ports roster.site roster.bundles roster.charts roster.rows f u (pub u)
    ((Sigma.snd z u).2.val.2.2) taskBase (roster.team (Sigma.fst (Sigma.snd f))
      (Sigma.fst (Sigma.snd (Sigma.snd f)))) ((ns u).logicalAt))
local notation3 (prettyPrint := false) "acquisition(" k ")" =>
  (f : parsedFields) → (ns : nativeAt(original(f))) × (receipts(f,original(f),ns) × k f (original(f)) ns)

local notation3 (prettyPrint := false) "deployed(" k "," inputs ")" =>
  decoder.issuedNativeFamily routed (fun (f : parsedFields) (z : barePrefix) (ns : nativeAt(z)) =>
    receipts(f,z,ns) × k f z ns) inputs

/-- The call evidence of this fixed acquisition on each physical field. -/
noncomputable def PreparedHistoryDecoder.AcquiredIssuance
    (kept : parsedFields → (z : barePrefix) → nativeAt(z) → Type*) (source : acquisition(kept)) : Type _ :=
  type_of% (issue kept source)

/-- The original typed private calls in the measured returned team. -/
noncomputable def PreparedHistoryDecoder.IssuedTable
    (kept : parsedFields → (z : barePrefix) → nativeAt(z) → Type*) (source : acquisition(kept)) : Type _ :=
  type_of% (fun calls f => ((issue kept source) calls f).1)

/-- The complete array of original issued cells at a fixed measured native call. -/
noncomputable def PreparedHistoryDecoder.IssuedOnCalls
    (kept : parsedFields → (z : barePrefix) → nativeAt(z) → Type*) (source : acquisition(kept))
    (calls : NativeCalls id B limit burst privateSize (deployed(kept,source))) : Type _ :=
  type_of% (fun f => ((issue kept source) calls f).1)

variable {decoder limit burst privateSize core roster taskBase routed}

/-- Install one actual native acquisition in the retained source operation. -/
noncomputable def PreparedHistoryDecoder.HeldIssuance.acquire
    {kept : parsedFields → (z : barePrefix) → nativeAt(z) → Type*}
    (held : decoder.HeldIssuance limit burst privateSize core roster taskBase routed kept)
    (source : acquisition(kept)) :
    decoder.AcquiredIssuance limit burst privateSize core roster taskBase routed kept source :=
  held source

/-- Read the issued table on the same retained acquisition and continuation. -/
noncomputable def PreparedHistoryDecoder.AcquiredIssuance.issuedTable
    {kept : parsedFields → (z : barePrefix) → nativeAt(z) → Type*} {source : acquisition(kept)}
    (result : decoder.AcquiredIssuance limit burst privateSize core roster taskBase routed kept source) :
    decoder.IssuedTable limit burst privateSize core roster taskBase routed kept source :=
  fun calls f => (result calls f).1

/-- Specialize an issued table at the true continuation using the same sparse acquisition. -/
noncomputable def PreparedHistoryDecoder.IssuedTable.onCalls
    {kept : parsedFields → (z : barePrefix) → nativeAt(z) → Type*} {source : acquisition(kept)}
    (table : decoder.IssuedTable limit burst privateSize core roster taskBase routed kept source)
    (calls : NativeCalls id B limit burst privateSize (deployed(kept,source))) :
    decoder.IssuedOnCalls limit burst privateSize core roster taskBase routed kept source calls :=
  table calls

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
