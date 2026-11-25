import OAI.Computability.BorderVNP.DiagonalRoutedReportCutSupport
import OAI.Computability.BorderVNP.DiagonalBootedRouteDecoding

/-! # Recovering the full starting machine and prefix from the supported decoder -/

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


private theorem pair_of_start_digits_return {A A' : PinStart gen n w}
    (eqn : A=A') (p : A.Prefix id) (q : A'.Prefix id)
    (digits : List.ofFn p.1=List.ofFn q.1) (ending : p.2.val=q.2.val) :
    (⟨A,p⟩ : Σ M : PinStart gen n w, M.Prefix id) = ⟨A',q⟩ := by
  subst A'
  have hd := List.ofFn_injective digits
  obtain ⟨pd,pr⟩ := p
  obtain ⟨qd,qr⟩ := q
  change pd=qd at hd
  subst qd
  obtain rfl : pr=qr := Subtype.ext ending
  rfl

set_option maxHeartbeats 450000 in
/-- Even for an abstract bare decoder, its recovered exterior, pin digits
and chronological return determine the whole supported positive prefix.
This identifies every intermediate report or argument return on that prefix. -/
theorem PreparedHistoryDecoder.supported_restored_pair
    (decoder : PreparedHistoryDecoder gen id G pub reg pin L headerWidth code args fixed hw size base fit B)
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ active ext}) (u : Fin (R+1)),
      let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id gen n (pub u) mac node.start.bank node.memory node.pins node.used limit)
    (Route : Hist → Type) (Report : (Fin d → Bool) → (q : Hist) → Route q → Type)
    (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
      (Σ c : Physical.Broadcast axes groups cap,
        ParsedPreCall G args pin L fixed hw size base fit headerWidth U ib hb sb guess id i ⟨code q,c,claim⟩) ≃
          Σ v : Route q,Report i q v)

    (i : Fin d → Bool) (q : Hist) (v : Route q) (c : Fin ((R+1)*dim*tally) → Bool)
    (a : Report i q v) (u : Fin (R+1)) :
    let team := supportedTeam id B limit burst room next
    let found := decoder.supported limit burst room next Route Report routed
    let z := found.val.symm ⟨i,q,v,c,a⟩
    let seen := (routed i q c).symm ⟨v,a⟩
    let hdr := positiveExteriorFieldsEquiv G args pin L fixed hw size base fit headerWidth
    let ext := hdr.symm ⟨(⟨code q,seen.1,c⟩ : Fields),seen.2.1⟩
    let original : (B ext u).start.Prefix id := ⟨_,seen.2.2 u⟩
    (⟨(team z.1 u).start,z.2 u⟩ : Σ M : PinStart gen n w, M.Prefix id)=⟨(B ext u).start,original⟩ := by
  intro team found z seen hdr ext original
  have h := found.property i q v c a
  have e : (⟨z.1.val,z.1.property.1⟩ : {x // PositiveExterior G args pin w x})=ext := Subtype.ext h.1
  have starts := (supportedTeam_start id B limit burst room next z.1 u).trans (congrArg (fun y => (B y u).start) e)
  exact pair_of_start_digits_return gen id starts (z.2 u) original ((h.2 u).2) ((h.2 u).1)


open RoutingISA.Evaluator.SignedPrep DiagonalTallyCellReports

set_option maxHeartbeats 450000 in
/-- Use the report and argument input observed on this route directly
on the corresponding prefix of the selected supported machine. -/
theorem PreparedHistoryDecoder.supported_reportCut
    (decoder : PreparedHistoryDecoder gen id G pub reg pin L headerWidth code args fixed hw size base fit B)
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ active ext}) (u : Fin (R+1)),
      let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id gen n (pub u) mac node.start.bank node.memory node.pins node.used limit)
    (Route : Hist → Type) (Report : (Fin d → Bool) → (q : Hist) → Route q → Type)
    (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
      (Σ c : Physical.Broadcast axes groups cap,
        ParsedPreCall G args pin L fixed hw size base fit headerWidth U ib hb sb guess id i ⟨code q,c,claim⟩) ≃
          Σ v : Route q,Report i q v)

    (i : Fin d → Bool) (q : Hist) (v : Route q) (c : Fin ((R+1)*dim*tally) → Bool)
    (a : Report i q v) (u : Fin (R+1)) {l : ReportLayout} {cs : List (ReportCell l)}
    (rows : ReportAssignments cs) (cur : ReportCursor) (desc : ℕ) :
    let team := supportedTeam id B limit burst room next
    let found := decoder.supported limit burst room next Route Report routed
    let z := found.val.symm ⟨i,q,v,c,a⟩
    let seen := (routed i q c).symm ⟨v,a⟩
    let hdr := positiveExteriorFieldsEquiv G args pin L fixed hw size base fit headerWidth
    let ext := hdr.symm ⟨(⟨code q,seen.1,c⟩ : Fields),seen.2.1⟩
    let original : (B ext u).start.Prefix id := ⟨_,seen.2.2 u⟩
    Nonempty (ReportArgumentCut ((B ext u).start.visited original).reports rows cur desc) →
      Nonempty (ReportArgumentCut ((team z.1 u).start.visited (z.2 u)).reports rows cur desc) := by
  let observation (s : Σ M : PinStart gen n w, M.Prefix id) :=
    Nonempty (ReportArgumentCut (s.1.visited s.2).reports rows cur desc)
  exact (congrArg observation (PreparedHistoryDecoder.supported_restored_pair gen id G pub reg pin L headerWidth code args fixed hw size base fit B
    decoder limit burst room next Route Report routed i q v c a u)).mpr

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
