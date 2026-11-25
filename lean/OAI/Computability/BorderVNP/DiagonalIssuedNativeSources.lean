import OAI.Computability.BorderVNP.DiagonalRoutedIssuedInputs
import OAI.Computability.BorderVNP.DiagonalJointSparseReadback

/-! # Restoring the native source and its certified report and geometry together -/

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

set_option maxHeartbeats 900000 in
/-- Retain the exact data chosen at the routed report and the evidence about
its marker rows, signed private width and published report. This operation is
defined on every original bare visit, including arbitrarily chosen reports. -/
noncomputable def PreparedHistoryDecoder.issuedSources
    (Data : (z : Bare) → (Inputs(z)) → Type*)
    (make : ∀ f : Issued, Σ source : Inputs(front(f)), Data (front(f)) source)
    (z : Bare) : Σ source : Inputs(z), Data z source :=
  decoder.issuedNative routed (fun a => Σ source : Inputs(a), Data a source) make z

/-- At a source tuple, all the original sparse inputs and the proofs about
the actual geometric arrays are recovered at once. -/
theorem PreparedHistoryDecoder.issuedSources_routed
    (Data : (z : Bare) → (Inputs(z)) → Type*)
    (make : ∀ f : Issued, Σ source : Inputs(front(f)), Data (front(f)) source)
    (f : Issued) : decoder.issuedSources routed Data make (front(f)) = make f :=
  decoder.issuedNative_routed routed (fun a => Σ source : Inputs(a), Data a source) make f

set_option maxHeartbeats 900000 in
/-- On the positive jointly supported part, the same family of inputs is
available before choosing a private continuation. The retained certificate
is indexed by these precise inputs and their reached team memories. -/
noncomputable def PreparedHistoryDecoder.supportedIssuedSources
    (Data : (z : Bare) → (Inputs(z)) → Type*)
    (make : ∀ f : Issued, Σ source : Inputs(front(f)), Data (front(f)) source)
    (x : {ext // PositiveExterior G args pin w ext ∧ active ext})
    (p : PinStart.JointPrefix id (fun u => (B ⟨x.val,x.property.1⟩ u).start)) :
    let z : Bare := ⟨⟨x.val,x.property.1⟩,p⟩
    Σ source : Inputs(z), Data z source :=
  decoder.issuedSources routed Data make ⟨⟨x.val,x.property.1⟩,p⟩

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
