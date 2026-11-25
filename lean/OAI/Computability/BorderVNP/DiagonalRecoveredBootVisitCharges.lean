import OAI.Computability.BorderVNP.DiagonalBootChargeDomains

/-! # Measured native visits recovered on the original boot family -/

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

local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally
local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation "mac" => TeamSiteEvents.macros (w:=w) (siteLibrary SparseExterior.driver) (nativeClock n)
local notation "active" => PinStart.preCallSupport U id
local notation3 (prettyPrint := false) "ib" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "hb" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "sb" => fun u => (args u).starbase
local notation "guess" => (fun (_ : {ext // PositiveExterior G args pin w ext}) (_ : Fin (R+1)) => rfl)

local notation "headers" => positiveExteriorFieldsEquiv G args pin L fixed hw size base fit headerWidth
variable {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
  (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
    (Σ c : Physical.Broadcast axes groups cap,
      ParsedPreCall G args pin L fixed hw size base fit headerWidth (fun x u => (B x u).start)
        (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id i ⟨code q,c,claim⟩) ≃
        Σ v : Route q,Report i q v)
  (decoder : PreparedHistoryDecoder SparseExterior.driver id G pub reg pin L headerWidth code args fixed hw size base fit B)


variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}

local notation3 (prettyPrint := false) "Bare" =>
  ((x : {ext // PositiveExterior G args pin w ext}) × ((u : Fin (R+1)) → (B x u).start.Prefix id))
local notation3 (prettyPrint := false) "Issued" =>
  PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report
local notation3 (prettyPrint := false) "decode" => (decoder.bare Route Report routed).val



open RoutingISA.Evaluator.ScheduleClock RoutingISA.SignedTaskArena

variable (task : SignedTaskArena.Layout) (A : StartupArena) (cost : PhaseCharges)
    (entryWords indexBits tallyDim subt P L₀ F H : ℕ)
local notation3 (prettyPrint := false) "measuredAt(" z ")" =>
  ∀ u : Fin (R+1), PinStart.ChargedVisit id (U (z).1) (fun u => (B (z).1 u).used) cost task A entryWords
    indexBits tallyDim subt P L₀ F H (z).2 u

set_option cleanup.letToHave false in
set_option maxHeartbeats 1400000 in
include decoder in
/-- Inverting the actual finite preparation bijection transports every local
charge to the original bare prefix, preserving every team's reached memory. -/
theorem PreparedHistoryDecoder.chargedVisitsFromIssued
    (source : ∀ f : Issued, measuredAt(routedBareTuple routed f)) :
    AllBootChargedVisits B id cost task A entryWords indexBits tallyDim subt P L₀ F H := by
  intro x a u
  exact decoder.issuedNative routed (fun z : Bare => measuredAt(z)) source ⟨x,a⟩ u

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
