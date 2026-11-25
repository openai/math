import OAI.Computability.BorderVNP.DiagonalRecoveredIssuedPost

/-! # The original boot clock from the observed profile and nominal post -/

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
local notation3 (prettyPrint := false) "frontCost(" x "," a "," u ")" =>
  let team := B x
  let v := PinStart.visits id (fun i => (team i).start) (a u)
  (team u).used+traceCost ((team u).pins (a u).1).val.1+
    traceCost v.profile.val.1+traceCost v.routing.val.1

set_option cleanup.letToHave false in
set_option maxHeartbeats 1700000 in
include decoder in
/-- On each original issued field, pay the front with its own observed
header and decoded history; transport that charge and the post back to the
same original bare tuple. -/
theorem PreparedHistoryDecoder.bareChargesFromMeasuredProfile
    (post : AllIssuedPost id B routed task A cost entryWords indexBits tallyDim subt P L₀ F H)
    (profile : ∀ (h : Hist) (p : Fields) (x : {e // PositiveExterior G args pin w e}),
      (∀ c, JointHeader.observed L x.val c = p.bits) → code h = p.profile →
      ∀ (a : PinStart.JointPrefix id (fun i => (B x i).start)) (u : Fin (R+1)),
        frontCost(x,a,u) ≤ cost.core + cost.before) :
    AllBootChargedVisits B id cost task A entryWords indexBits tallyDim subt P L₀ F H := by
  apply decoder.bareChargesOfPost routed task A cost entryWords indexBits tallyDim subt P L₀ F H post
  unfold AllIssuedFront
  intro f z starts u
  exact routedBareTuple.prefixEarly (B:=B) (cost:=cost) routed profile f u

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
