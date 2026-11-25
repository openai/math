import OAI.Computability.BorderVNP.DiagonalSourceRosterIssuer

/-! # Types for the native issued evidence at a fixed original roster -/

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

/-- The full native issuing operation on one accepted routing decoder. -/
noncomputable def PreparedHistoryDecoder.CandidateIssuance : Type _ :=
  type_of% issue

/-- Name the actual operation without expanding its dependent call arguments. -/
noncomputable def PreparedHistoryDecoder.candidateIssuance :
    decoder.CandidateIssuance limit burst privateSize core roster taskBase routed :=
  issue

/-- The call operation on the particular retained packet evidence of this reader. -/
noncomputable def PreparedHistoryDecoder.HeldIssuance (kept : parsedFields → (z : barePrefix) → nativeAt(z) → Type*) : Type _ :=
  type_of% (issue kept)

/-- Expose the retained packet operation at its named dependent type. -/
noncomputable def PreparedHistoryDecoder.heldIssuance (kept : parsedFields → (z : barePrefix) → nativeAt(z) → Type*) :
    decoder.HeldIssuance limit burst privateSize core roster taskBase routed kept :=
  issue kept

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
