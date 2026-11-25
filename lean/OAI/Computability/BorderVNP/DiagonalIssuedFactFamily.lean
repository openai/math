import OAI.Computability.BorderVNP.DiagonalSupportedIssuedFacts
import OAI.Computability.BorderVNP.DiagonalSupportedNativeCalls

/-! # The native source family retained together with its issued facts -/

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



local notation3 (prettyPrint := false) "front(" f ")" => routedBareTuple routed f
local notation3 (prettyPrint := false) "Inputs(" z ")" =>
  ∀ u, PinStart.SparseSource id (fun j => (B (Sigma.fst z) j).start) (Sigma.snd z u)



set_option maxHeartbeats 1200000 in
/-- Select the booted native source from the same original packet that retains
the owner and placement evidence. This family is available before continuing. -/
noncomputable def PreparedHistoryDecoder.issuedNativeFamily
    (record : Issued → (z : Bare) → Inputs(z) → Type*)
    (packet : ∀ f : Issued, Σ native : Inputs(front(f)), record f (front(f)) native) : NativeSources id B :=
  let data := fun (z : Bare) (ss : Inputs(z)) => record (decoder.issuedEquiv routed z) z ss
  let make : ∀ f : Issued, Σ ns : Inputs(front(f)), data (front(f)) ns := fun f =>
    ⟨(packet f).1,(congrArg (fun g => record g (front(f)) (packet f).1)
      ((decoder.issuedEquiv routed).apply_symm_apply f).symm).mp (packet f).2⟩
  fun x p => (decoder.supportedIssuedSources routed data make x p).1

variable (limit burst : ℕ) (privateSize : TeamScales.width n (1/2)≤burst)
    (next : ∀ (y : {ext // PositiveExterior G args pin w ext ∧ PinStart.preCallSupport (fun x u => (B x u).start) id ext})
      (u : Fin (R+1)), let node := B ⟨y.val,y.property.1⟩ u
      PositiveContinuation id SparseExterior.driver n (pub u)
        (TeamSiteEvents.macros (w:=w) (siteLibrary SparseExterior.driver) (nativeClock n))
        node.start.bank node.memory node.pins node.used limit)

set_option maxHeartbeats 1400000 in
/-- Recover the simultaneous stored data on the very same native family at
every selected supported positive prefix. -/
noncomputable def PreparedHistoryDecoder.issuedFamilyFacts
    (record : Issued → (z : Bare) → Inputs(z) → Type*)
    (packet : ∀ f : Issued, Σ native : Inputs(front(f)), record f (front(f)) native) (f : Issued) :
    let a := (decoder.supported limit burst privateSize next Route Report routed).val.symm f
    let z : Bare := ⟨⟨a.1.val,a.1.property.1⟩,a.2⟩
    record f z (decoder.issuedNativeFamily routed record packet a.1 a.2) :=
  decoder.supportedIssuedFacts routed limit burst privateSize next record packet f

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
