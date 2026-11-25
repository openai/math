import OAI.Computability.BorderVNP.DiagonalRoutedIssuedInputs
import OAI.Computability.BorderVNP.DiagonalChargedPostProjection

/-! # Reader operands on every supported return from a measured source -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube Diagonal

section Sources

variable {R r t d link inner n w reserve axes groups cap dim tally box lanes selectors symbols : ℕ}
    {Edge Hist : Type} (gen : Fragment IO) (id : TableEntry axes box lanes selectors symbols → ℕ)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link)
    (headerWidth : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)
    (code : Hist ↪ (Fin reserve → Bool))
    (args : Fin (R+1) → UnitAddresses) (fixed : Block (R+1)) (hw : 0<w)
    (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart gen G pub reg args pin x.val u)

local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation "mac" => TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n)
local notation "active" => PinStart.preCallSupport U id

variable {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
  (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
    (Σ c : Physical.Broadcast axes groups cap,
      ParsedPreCall G args pin L fixed hw size base fit headerWidth (fun x u => (B x u).start)
        (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id i ⟨code q,c,claim⟩) ≃
        Σ v : Route q,Report i q v)
  (decoder : PreparedHistoryDecoder gen id G pub reg pin L headerWidth code args fixed hw size base fit B)

variable {gen id G pub reg pin L headerWidth code args fixed hw size base fit B}

local notation3 (prettyPrint := false) "Bare" =>
  ((x : {ext // PositiveExterior G args pin w ext}) × ((u : Fin (R+1)) → (B x u).start.Prefix id))
local notation3 (prettyPrint := false) "Issued" =>
  PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report
include decoder in
/-- The reader words observed on each reconstructed bare source survive on
every supported prefix of the same boot and continuation. -/
theorem PreparedHistoryDecoder.supportedReaderKept
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ active ext}) (u : Fin (R+1)),
      let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id gen n (pub u) mac node.start.bank node.memory node.pins node.used limit)
    (A : StartupArena) (entryWords indexBits : ℕ) (u : Fin (R+1))
    (observed : ∀ f : Issued, let z := routedBareTuple routed f
      let b := B z.1 u
      ReaderKept A entryWords indexBits b.memory (b.pins (z.2 u).1).val.2.2 (z.2 u).2.val.2.2)
    (z : JointBeforeCells (supportedTeam id B limit burst room next)) :
    let b := B ⟨z.1.val,z.1.property.1⟩ u
    ReaderKept A entryWords indexBits b.memory (b.pins (z.2 u).1).val.2.2 (z.2 u).2.val.2.2 := by
  let predicate := fun y : Bare => let b := B y.1 u
    ReaderKept A entryWords indexBits b.memory (b.pins (y.2 u).1).val.2.2 (y.2 u).2.val.2.2
  exact decoder.issuedNative routed predicate observed ⟨⟨z.1.val,z.1.property.1⟩,z.2⟩

end Sources

section Charged

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

local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation "mac" => TeamSiteEvents.macros (w:=w) (siteLibrary SparseExterior.driver) (nativeClock n)
local notation "active" => PinStart.preCallSupport U id

variable (decoder : PreparedHistoryDecoder SparseExterior.driver id G pub reg pin L headerWidth code args fixed hw size base fit B)
variable {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
  (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
    (Σ c : Physical.Broadcast axes groups cap,
      ParsedPreCall G args pin L fixed hw size base fit headerWidth (fun x u => (B x u).start)
        (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id i ⟨code q,c,claim⟩) ≃
        Σ v : Route q,Report i q v)

variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}

local notation3 (prettyPrint := false) "Issued" =>
  PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report
include decoder in
/-- The measured post of the clock protects the same reader on a supported
return. The decoder fixes the heterogeneous bare prefix types before its
routed source and the later continuation are instantiated. -/
theorem PreparedHistoryDecoder.supportedKeptOfChargedPost
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ active ext}) (u : Fin (R+1)),
      let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id SparseExterior.driver n (pub u) mac node.start.bank node.memory node.pins node.used limit)
    (task : SignedTaskArena.Layout) (A : StartupArena) (entryWords indexBits : ℕ) (u : Fin (R+1))
    {budget tallyDim subt publicCost localCost finishCost readCost : ℕ}
    (post : ∀ f : Issued, let z := routedBareTuple routed f
      PinStart.ChargedPost id (fun v => (B z.1 v).start) budget task A entryWords indexBits
        tallyDim subt publicCost localCost finishCost readCost z.2 u)
    (z : JointBeforeCells (supportedTeam id B limit burst room next)) :
    let b := B ⟨z.1.val,z.1.property.1⟩ u
    ReaderKept A entryWords indexBits b.memory (b.pins (z.2 u).1).val.2.2 (z.2 u).2.val.2.2 :=
  decoder.supportedReaderKept routed limit burst room next A entryWords indexBits u (fun f => (post f).2.1) z

end Charged

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
