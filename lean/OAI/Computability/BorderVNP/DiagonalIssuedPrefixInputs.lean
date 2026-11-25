import OAI.Computability.BorderVNP.DiagonalDecodedPrefixOwnership

/-! # Issued physical inputs on every bare and supported native tuple -/

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

/-- Reindex a physical receipt from each original issued report tuple to all
chronological pre-call tuples. The dependent carrier may refer to the team
states, returned RAM, complete report tape and any source produced there. -/
noncomputable def PreparedHistoryDecoder.issuedInputs (Data : Bare → Sort*)
    (assembled : ∀ f : Issued, Data ((decode).symm f)) (z : Bare) : Data z :=
  (Equiv.piCongrLeft' Data decode).symm assembled z

/-- The construction retains the source value and its dependent physical
witnesses at the exact inverse image of the issued fields. -/
theorem PreparedHistoryDecoder.issuedInputs_symm (Data : Bare → Sort*)
    (assembled : ∀ f : Issued, Data ((decode).symm f)) (f : Issued) :
    decoder.issuedInputs routed Data assembled ((decode).symm f)=assembled f :=
  congrFun ((Equiv.piCongrLeft' Data decode).apply_symm_apply assembled) f

variable (limit burst : ℕ) (privateSize : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ PinStart.preCallSupport (fun x u => (B x u).start) id ext}) (u : Fin (R+1)),
      let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id gen n (pub u) (TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n)) node.start.bank node.memory node.pins node.used limit)
local notation3 (prettyPrint := false) "forget" =>
  PinStart.positivePrefixes U (fun x => PinStart.preCallSupport_iff (id:=id) U x.val x.property)
    (supportedTeam id B limit burst privateSize next) (supportedTeam_start id B limit burst privateSize next)
local notation3 (prettyPrint := false) "rest" f =>
  (decoder.supported limit burst privateSize next Route Report routed).val.symm f

/-- The same physical construction on the supported team tuple agrees with the
bare source even when its dependent state or ownership table varies with the
returned pins and report guesses. -/
theorem PreparedHistoryDecoder.issuedInputs_supported (Data : Bare → Type*)
    (assembled : ∀ f : Issued, Data ((decode).symm f)) (f : Issued) :
    (⟨forget (rest f),decoder.issuedInputs routed Data assembled (forget (rest f))⟩ : Sigma Data) =
      ⟨(decode).symm f,assembled f⟩ := by
  rw [PreparedHistoryDecoder.supported_bare_symm gen id G pub reg pin L headerWidth code args fixed hw size base fit B routed decoder limit burst privateSize next f]
  exact congrArg (Sigma.mk ((decode).symm f)) (decoder.issuedInputs_symm routed Data assembled f)

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
