import OAI.Computability.BorderVNP.DiagonalIssuedPrefixInputs

/-! # Native sources on the actual restored broadcast, pins and reports -/

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


/-- Original complete tuple from the routed report inverse. In particular the
public bank, register file and final report memory of each team are those of
the actual pinned return. -/
noncomputable def routedBareTuple (f : Issued) : Bare :=
  let i := f.1
  let q := f.2.1
  let v := f.2.2.1
  let claim := f.2.2.2.1
  let rows := f.2.2.2.2
  let source := (routed i q claim).symm ⟨v,rows⟩
  let x := (headers).symm ⟨(⟨code q,source.1,claim⟩ : Fields),source.2.1⟩
  ⟨x,fun u => ⟨(G.jointGuess ib hb sb).symm i u,source.2.2 u⟩⟩

/-- Rewrite the bare decoder inverse to the original physical return even
when the cell directories and their dependent witnesses vary with history. -/
theorem PreparedHistoryDecoder.bare_eq_routed (f : Issued) :
    (decode).symm f = routedBareTuple routed f := by
  rcases f with ⟨i,q,v,claim,reports⟩
  exact PreparedHistoryDecoder.bare_restored gen id G pub reg pin L headerWidth code args fixed hw size base fit B routed decoder i q v claim reports

/-- Read every issued field from the same bare tuple and use the actual
native routed returns as the definitional inverse. -/
noncomputable def PreparedHistoryDecoder.issuedEquiv : Bare ≃ Issued where
  toFun := decode
  invFun := routedBareTuple routed
  left_inv z := (decoder.bare_eq_routed routed ((decode) z)).symm.trans ((decode).symm_apply_apply z)
  right_inv f := (congrArg (decode) (decoder.bare_eq_routed routed f).symm).trans ((decode).apply_symm_apply f)

/-- Assemble native input data on each source tuple, before any team crosses
into a private cell. This covers fields as well as ownership receipts whose
types mention the actual final RAM. -/
noncomputable def PreparedHistoryDecoder.issuedNative (Data : Bare → Sort*)
    (build : ∀ f : Issued, Data (routedBareTuple routed f)) (z : Bare) : Data z :=
  (Equiv.piCongrLeft' Data (decoder.issuedEquiv routed)).symm build z

/-- Reading the recovered tuple returns exactly the physical source payload. -/
theorem PreparedHistoryDecoder.issuedNative_routed (Data : Bare → Sort*)
    (build : ∀ f : Issued, Data (routedBareTuple routed f)) (f : Issued) :
    decoder.issuedNative routed Data build (routedBareTuple routed f) = build f :=
  congrFun ((Equiv.piCongrLeft' Data (decoder.issuedEquiv routed)).apply_symm_apply build) f

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
