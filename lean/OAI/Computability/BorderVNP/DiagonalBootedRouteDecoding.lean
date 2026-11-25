import OAI.Computability.BorderVNP.DiagonalSupportedParsedFields
import OAI.Computability.BorderVNP.DiagonalJointBootedSupport

/-! # The pre-call decoder on the physical signed bodies of all supported teams -/

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

/-- The pre-call decoder fixes the entire joint native start before the
post-call clocks, generated cells and paid reader have been chosen. -/
structure PreparedHistoryDecoder where
  /-- Decode and restore the physical exterior and each bare prefix. -/
  bare :
    ∀ (Route : Hist → Type) (Report : (Fin d → Bool) → (q : Hist) → Route q → Type)
    (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
      (Σ c : Physical.Broadcast axes groups cap,
        ParsedPreCall G args pin L fixed hw size base fit headerWidth U ib hb sb guess id i ⟨code q,c,claim⟩) ≃
          Σ v : Route q,Report i q v),
    {decode : ((x : {ext // PositiveExterior G args pin w ext}) × ((u : Fin (R+1)) → (B x u).start.Prefix id)) ≃
      PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report //
      ∀ i q v claim report,
        let z := decode.symm ⟨i,q,v,claim,report⟩
        let recovered := (routed i q claim).symm ⟨v,report⟩
        z.1.val=recovered.2.1.val ∧ ∀ u : Fin (R+1),
          (z.2 u).2.val=(recovered.2.2 u).val ∧ List.ofFn (z.2 u).1=List.ofFn ((G.jointGuess ib hb sb).symm i u)}

section Support

variable {gen id G pub reg pin L headerWidth code args fixed hw size base fit B}

/-- Retain precisely the same joint decoder when the returning teams have
been certified. Its physical-support reindexing only forgets the now witnessed
fact that each team can return. -/
noncomputable def PreparedHistoryDecoder.supported
    (decoder : PreparedHistoryDecoder gen id G pub reg pin L headerWidth code args fixed hw size base fit B) :
  ∀ (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ active ext}) (u : Fin (R+1)),
      let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id gen n (pub u) mac node.start.bank node.memory node.pins node.used limit)
    (Route : Hist → Type) (Report : (Fin d → Bool) → (q : Hist) → Route q → Type)
    (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
      (Σ c : Physical.Broadcast axes groups cap,
        ParsedPreCall G args pin L fixed hw size base fit headerWidth U ib hb sb guess id i ⟨code q,c,claim⟩) ≃
          Σ v : Route q,Report i q v),
    {decode : JointBeforeCells (supportedTeam id B limit burst room next) ≃
      PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report //
      ∀ i q v claim report,
        let z := decode.symm ⟨i,q,v,claim,report⟩
        let recovered := (routed i q claim).symm ⟨v,report⟩
        z.1.val=recovered.2.1.val ∧ ∀ u : Fin (R+1),
          (z.2 u).2.val=(recovered.2.2 u).val ∧ List.ofFn (z.2 u).1=List.ofFn ((G.jointGuess ib hb sb).symm i u)}

 := by
  intro limit burst room next Route Report routed
  let team := supportedTeam id B limit burst room next
  have membership (y : {ext // PositiveExterior G args pin w ext}) :=
    PinStart.preCallSupport_iff (id := id) U y.val y.property
  let start := supportedTeam_start id B limit burst room next
  let before := PinStart.positivePrefixes U membership team start
  let bare := decoder.bare Route Report routed
  refine ⟨before.trans bare.val,?_⟩
  intro i q v claim r
  let issued := bare.val.symm ⟨i,q,v,claim,r⟩
  have fields := bare.property i q v claim r
  exact ⟨(PinStart.positivePrefixes_symm_wire U membership team start issued).trans fields.1,
    fun u => ⟨(PinStart.positivePrefixes_symm_return U membership team start issued u).trans ((fields.2 u).1),
      (PinStart.positivePrefixes_symm_digits U membership team start issued u).trans ((fields.2 u).2)⟩⟩

/-- Reading a supported tuple first forgets the certificate that all teams
can return, then invokes the original pre-call decoder. -/
theorem PreparedHistoryDecoder.supported_apply
    (decoder : PreparedHistoryDecoder gen id G pub reg pin L headerWidth code args fixed hw size base fit B)
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ active ext}) (u : Fin (R+1)),
      let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id gen n (pub u) mac node.start.bank node.memory node.pins node.used limit)
    {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
    (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
      (Σ c : Physical.Broadcast axes groups cap,
        ParsedPreCall G args pin L fixed hw size base fit headerWidth U ib hb sb guess id i ⟨code q,c,claim⟩) ≃
          Σ v : Route q,Report i q v)
    (z : JointBeforeCells (supportedTeam id B limit burst room next)) :
    (decoder.supported limit burst room next Route Report routed).val z =
      (decoder.bare Route Report routed).val
        (PinStart.positivePrefixes U (fun y => PinStart.preCallSupport_iff (id := id) U y.val y.property)
          (supportedTeam id B limit burst room next) (supportedTeam_start id B limit burst room next) z) := rfl

end Support

/-- Recognition on one actual booted team's native preparation decides the
whole published history. The remaining routing inversion works independently
at every valid decoded history, raw pin and proposed subtotal. -/
noncomputable def decodePreparedHistory
    (recognize : ∀ (p : Fields) (z : HeaderExterior L p.bits) (u : Fin (R+1))
      (node : BootedPinStart gen G pub reg args pin z.val u), node.start.Prefix id → ∃ q, code q=p.profile) :
    PreparedHistoryDecoder gen id G pub reg pin L headerWidth code args fixed hw size base fit B := by
  constructor
  intro Route Report routed
  have accepted (raw : Fin d → Bool) (p : Fields) (run : ParsedPreCall G args pin L fixed hw size base fit
      headerWidth U ib hb sb guess id raw p) : ∃ q, code q=p.profile := by
    let headers := positiveExteriorFieldsEquiv G args pin L fixed hw size base fit headerWidth
    let y := headers.symm ⟨p,run.1⟩
    let node := B y 0
    exact recognize p run.1 0 node ⟨(G.jointGuess ib hb sb).symm raw 0,run.2 0⟩
  refine ⟨jointPreparedFields G args pin L fixed hw size base fit headerWidth U ib hb sb guess code accepted routed,?_⟩
  intro i q v claim report
  let prep := jointPreparedFields G args pin L fixed hw size base fit headerWidth U ib hb sb guess code accepted routed
  let z := prep.symm ⟨i,q,v,claim,report⟩
  have row := jointPreparedFields_symm_wire G args pin L fixed hw size base fit headerWidth U ib hb sb guess
    code accepted routed i q v claim report
  refine ⟨row,fun u => ⟨jointPreparedFields_symm_return G args pin L fixed hw size base fit headerWidth U ib hb sb
    guess code accepted routed i q v claim report u,?_⟩⟩
  have digits := jointPreparedFields_symm_pin G args pin L fixed hw size base fit headerWidth U ib hb sb guess
    code accepted routed i q v claim report u
  exact congrArg List.ofFn digits

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
