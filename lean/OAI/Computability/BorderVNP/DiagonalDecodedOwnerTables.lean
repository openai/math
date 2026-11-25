import OAI.Computability.BorderVNP.DiagonalDecodedPrefixOwnership
import OAI.Computability.BorderVNP.DiagonalNativeJoinedRows

/-! # The controller's returned owner table on every recovered positive prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube

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

local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally
local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation "mac" => TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n)
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
  (decoder : PreparedHistoryDecoder gen id G pub reg pin L headerWidth code args fixed hw size base fit B)

open CellDispatch

/-- Transfer each complete owner table read from the physical route's final argument RAM
to the exact supported returned prefix used by the private compiler. This preserves the count,
global numbering and every owned or unowned control row, including empty rows. -/
theorem PreparedHistoryDecoder.supported_owner_tables
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ active ext}) (u : Fin (R+1)),
      let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id gen n (pub u) mac node.start.bank node.memory node.pins node.used limit)
    (C : Hist → ℕ) (owner : (q : Hist) → Route q → Fin (C q) → Fin (R+1))
    (baseWord : (f : PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report) →
      Fin (R+1) → ℕ)
    (sourceRows : ∀ i q v claim (rows : Report i q v) u,
      let source := (routed i q claim).symm ⟨v,rows⟩
      OwnerTable (pub u) (source.2.2 u).val.2.2 ⟨u.val,baseWord ⟨i,q,v,claim,rows⟩ u,C q⟩
        (PositiveTeam.ownerWord (owner q v))) :
    let team := supportedTeam id B limit burst room next
    let prep := (decoder.supported limit burst room next Route Report routed).val
    ∀ (f : PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report) u,
      let z := prep.symm f
      OwnerTable (team z.1 u).pub ((team z.1 u).postMemory (z.2 u)) ⟨u.val,baseWord f u,C f.2.1⟩
        (PositiveTeam.ownerWord (owner f.2.1 f.2.2.1)) := by
  intro team prep f u
  obtain ⟨i,q,v,claim,rows⟩ := f
  let z := prep.symm ⟨i,q,v,claim,rows⟩
  have cut := (decoder.supported limit burst room next Route Report routed).property i q v claim rows
  have finalMemory := congrArg Prod.snd (congrArg Prod.snd ((cut.2 u).1))
  change OwnerTable (pub u) (z.2 u).2.val.2.2 _ _
  rw [finalMemory]
  exact sourceRows i q v claim rows u

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
