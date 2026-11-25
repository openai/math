import OAI.Computability.BorderVNP.DiagonalIssuedObservedFields
import OAI.Computability.BorderVNP.DiagonalJointPhysicalPost

/-! # Full native clock on the original returned source tuples -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM CompactMachine CellMacro.Generator TeamContraction.ProcessorSlots
open RoutingISA.SignedTaskArena ScheduleClock

/-- The measured front and constructor on one genuine native prefix, together
with the preserved reader and actual physical receipts for every returning call
and its suffix. All registers, traces and memories come from the same visit. -/
def ChargedVisit {R n w a b h K s : ℕ} (id : Cube.TableEntry a b h K s → ℕ)
    (U : Fin (R+1) → PinStart SparseExterior.driver n w) (used : Fin (R+1) → ℕ)
    (cost : PhaseCharges) (task : SignedTaskArena.Layout) (A : StartupArena)
    (entryWords indexBits dim subt P L F H : ℕ) (run : JointPrefix id U) (u : Fin (R+1)) : Prop :=
  let p := run u
  let v := visits id U p
  let input := afterRoute id U p
  let mac := install SparseExterior.driver n (U u).routines
  used u+traceCost ((U u).pins p.1).val.1+traceCost v.profile.val.1+traceCost v.routing.val.1 ≤
      cost.core+cost.before ∧
  traceCost input.val.1+privateDirectoryTicks (U u).pub input.val.2.2≤cost.argumentsCalls ∧
  ReaderKept A entryWords indexBits (U u).memory ((U u).pins p.1).val.2.2 p.2.val.2.2 ∧
  ∀ call : Returns callOwnedCells (U u).pub mac p.2.val.2.1 p.2.val.2.2,
    ∀ z : Returns (finishExpansion signedOccurrences) (U u).pub mac call.val.2.1 call.val.2.2,
      Nonempty (PhysicalPost (teams:=R+1) (d:=dim) (width:=subt) u task P L F H
        (U u).pub mac call.val.2.1 call.val.2.2 z)

end RoutingISA.Evaluator.PinStart

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

set_option maxHeartbeats 1100000 in
include decoder in
/-- The issued source suffices for every supported native tuple: invert the
public routing and reporting returns, keeping the reached memory of every
team, then assemble the calibrated clock on the original tuple. No terminal
consistency is required of the issued reports. -/
theorem PreparedHistoryDecoder.clockFromIssued
    (source : ∀ f : Issued, measuredAt(routedBareTuple routed f))
    (x : {e // PositiveExterior G args pin w e ∧ active e}) :
    let nodes := B ⟨x.val,x.property.1⟩
    let starts := fun i => (nodes i).start
    let used := fun i => (nodes i).used
    ((∀ (tuple : PinStart.JointPrefix id starts) u, let v := PinStart.visits id starts (tuple u)
        used u+traceCost ((starts u).pins (tuple u).1).val.1+traceCost v.profile.val.1+traceCost v.routing.val.1 ≤
          cost.core+cost.before) →
      (∀ (tuple : PinStart.JointPrefix id starts) u, let arg := PinStart.afterRoute id starts (tuple u)
        traceCost arg.val.1+privateDirectoryTicks (pub u) arg.val.2.2 ≤ cost.argumentsCalls) →
      (∀ (tuple : PinStart.JointPrefix id starts) u, let path := tuple u
        let lib := install SparseExterior.driver n (starts u).routines
        ReaderKept A entryWords indexBits (nodes u).memory ((nodes u).pins path.1).val.2.2 path.2.val.2.2 ∧
        ∀ call : Returns callOwnedCells (pub u) lib path.2.val.2.1 path.2.val.2.2,
          ∀ z : Returns (finishExpansion signedOccurrences) (pub u) lib call.val.2.1 call.val.2.2,
            Nonempty (PinStart.PhysicalPost (teams:=R+1) (d:=tallyDim) (width:=subt) u task P L₀ F H (pub u) lib
              call.val.2.1 call.val.2.2 z)) →
      PinStart.JointClock id starts used cost) →
    PinStart.JointClock id starts used cost := by
  intro nodes starts used close
  let original := decoder.issuedNative routed (fun z : Bare => measuredAt(z)) source
  have observations (tuple : PinStart.JointPrefix id starts) :=
    original ⟨⟨x.val,x.property.1⟩,tuple⟩
  exact close (fun tuple u => (observations tuple u).1) (fun tuple u => (observations tuple u).2.1)
    (fun tuple u => (observations tuple u).2.2)

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
