import OAI.Computability.BorderVNP.DiagonalSupportedIssuedFacts

/-! # Lead pin digits on the fixed source decoder -/

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

local notation3 (prettyPrint := false) "Issued" =>
  PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report
variable (limit burst : ℕ) (privateSize : TeamScales.width n (1/2)≤burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ PinStart.preCallSupport (fun x u => (B x u).start) id ext})
      (u : Fin (R+1)), let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id SparseExterior.driver n (pub u)
        (TeamSiteEvents.macros (w:=w) (siteLibrary SparseExterior.driver) (nativeClock n))
        node.start.bank node.memory node.pins node.used limit)


/-- The prepared source inverse recovers the original lead pin on every
reported tuple. The physical lead reader uses precisely this vector when
it signs the terminal packet for a guarded completion. -/
theorem PreparedHistoryDecoder.supportedLeadDigits (f : Issued) :
    let found := decoder.supported limit burst privateSize next Route Report routed
    let z := found.val.symm f
    List.ofFn (z.2 0).1=List.ofFn ((G.jointGuess (fun u => (args u).ibase) (fun u => (args u).hbase)
      (fun u => (args u).starbase)).symm f.1 0) := by
  obtain ⟨i,q,v,c,a⟩ := f
  exact (((decoder.supported limit burst privateSize next Route Report routed).property i q v c a).2 0).2

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
