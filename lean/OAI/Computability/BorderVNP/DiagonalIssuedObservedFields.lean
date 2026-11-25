import OAI.Computability.BorderVNP.DiagonalRoutedIssuedInputs

/-! # The physical header of the restored source tuple -/

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


variable {gen id G pub reg pin L headerWidth code args fixed hw size base fit B}

local notation3 (prettyPrint := false) "Bare" =>
  ((x : {ext // PositiveExterior G args pin w ext}) × ((u : Fin (R+1)) → (B x u).start.Prefix id))
local notation3 (prettyPrint := false) "Issued" =>
  PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool) Route Report
local notation3 (prettyPrint := false) "decode" => (decoder.bare Route Report routed).val


set_option maxRecDepth 6000
set_option maxHeartbeats 1100000

/-- The unfiltered issued header includes its actual raw declaration and all
announced subtotals as well as the padded history. -/
noncomputable def issuedHeader (f : Issued) : Fields :=
  ⟨code f.2.1,((routed f.1 f.2.1 f.2.2.2.1).symm ⟨f.2.2.1,f.2.2.2.2⟩).1,f.2.2.2.1⟩

/-- The native inverse returns exactly the bits of its original header. -/
theorem routedBareTuple.observed (f : Issued) (e : Block (R+1)) :
    JointHeader.observed L (routedBareTuple routed f).1.val e=(issuedHeader routed f).bits := by
  rcases f with ⟨i,q,v,claim,reports⟩
  exact ((routed i q claim).symm ⟨v,reports⟩).2.1.property e

/-- All three header fields of the restored source are the words on the
actual exterior before validating any later private choice. -/
theorem PreparedHistoryDecoder.issued_observed_fields (z : Bare) (p : Fields)
    (seen : ∀ e, JointHeader.observed L z.1.val e=p.bits) :
    p=issuedHeader routed (decoder.issuedEquiv routed z) := by
  let f := decoder.issuedEquiv routed z
  have back : routedBareTuple routed f=z := (decoder.issuedEquiv routed).symm_apply_apply z
  have stored := congrArg (fun x : Bare => JointHeader.observed L x.1.val fixed) back
  exact PositiveFields.bits_injective ((seen fixed).symm.trans (stored.symm.trans (routedBareTuple.observed routed f fixed)))

/-- The original history recovered before the nominal route is the very
history indexing the source, even if the chosen reports are inconsistent. -/
theorem PreparedHistoryDecoder.issued_history_of_profile (z : Bare) (p : Fields) (h : Hist)
    (seen : ∀ e, observed L z.1.val e=p.bits) (encoded : code h=p.profile) :
    (decoder.issuedEquiv routed z).2.1=h := by
  have actual := decoder.issued_observed_fields routed z p seen
  exact code.injective ((congrArg PositiveFields.profile actual).symm.trans encoded.symm)

/-- Recover a source payload indexed by the observed header and its
pre-call geometry history. Its native tuple retains the original banks and
memories, also for a report proposal whose eventual return is empty. -/
noncomputable def PreparedHistoryDecoder.issuedAtProfile (Data : Hist → Fields → Bare → Sort*)
    (build : ∀ f : Issued, Data f.2.1 (issuedHeader routed f) (routedBareTuple routed f))
    (z : Bare) (p : Fields) (h : Hist) (seen : ∀ e, JointHeader.observed L z.1.val e=p.bits)
    (encoded : code h=p.profile) : Data h p z := by
  let E := decoder.issuedEquiv routed
  let witness (a : Bare) := Data (E a).2.1 (issuedHeader routed (E a)) a
  have give (f : Issued) : witness (routedBareTuple routed f) := by
    change Data (E (routedBareTuple routed f)).2.1 (issuedHeader routed (E (routedBareTuple routed f))) _
    rw [show E (routedBareTuple routed f)=f from E.apply_symm_apply f]
    exact build f
  have result : Data (E z).2.1 (issuedHeader routed (E z)) z := decoder.issuedNative routed witness give z
  have profile : (E z).2.1=h := decoder.issued_history_of_profile routed z p h seen encoded
  have fields : p=issuedHeader routed (E z) := decoder.issued_observed_fields routed z p seen
  rw [profile,←fields] at result
  exact result

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
