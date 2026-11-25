import OAI.Computability.BorderVNP.DiagonalBeforeIssuedCalls
import OAI.Computability.BorderVNP.DiagonalIssuedFactFamily

/-! # All source-indexed receipts issue the supported positive private calls -/

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

open Crossing Packing.Inherited Packing.BottomReports Cube.Physical Cube.Physical.NativeAssignments
open DiagonalTallyCellReports RoutingISA.CompactMachine
variable {D nativeGroups : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Hist → Network D P bits} {count : Hist → ℕ}
    (core : ∀ h, CoreDirectory (N h) axes nativeGroups (count h) box lanes selectors R)
    (portSource : (Fin d → Bool) → Ports bits) (ownedSite : ∀ h, Fin (core h).siteRows → ℕ)
    (bottom : ∀ h, Fin (core h).cells → List Bundle)
    (charts : (Fin d → Bool) → (h : Hist) → (core h).Route symbols → Fin (R+1) → ReportLayout)
    (rc : ∀ i h v, ReceivedRows (charts i h v) (core h).cells)
    (who : ∀ h, (core h).Route symbols → Fin (core h).cells → Fin (R+1))
    (owner : ∀ (i : Fin d → Bool) (h : Hist) (v : (core h).Route symbols) (u : Fin (R+1)) (j : Fin ((rc i h v).cells u).length),
      who h v ((rc i h v).order ⟨u,j⟩)=u)
    (taskBase : ℕ)
    (routed : ∀ (i : Fin d → Bool) (h : Hist) (c : Fin ((R+1)*dim*tally) → Bool), (Σ p : Physical.Broadcast axes groups cap,
      ParsedPreCall G args pin L fixed hw size base fit headerWidth (fun x u => (B x u).start)
        (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id i ⟨code h,p,c⟩) ≃
        Σ v : (core h).Route symbols, CoreDirectory.Proposals core charts rc i h v)
    (decoder : PreparedHistoryDecoder SparseExterior.driver id G pub reg pin L headerWidth code args fixed hw size base fit B)

local notation3 (prettyPrint := false) "Router" => (fun h : Hist => (core h).Route symbols)
local notation3 (prettyPrint := false) "Report" => CoreDirectory.Proposals core charts rc
local notation3 (prettyPrint := false) "Bare" => ((x : {ext // PositiveExterior G args pin w ext}) ×
  ((u : Fin (R+1)) → (B x u).start.Prefix id))
local notation3 (prettyPrint := false) "Parsed" => PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool)
  Router Report
local notation3 (prettyPrint := false) "front(" f ")" => routedBareTuple routed f
local notation3 (prettyPrint := false) "Inputs(" z ")" =>
  ∀ u, PinStart.SparseSource id (fun j => (B (Sigma.fst z) j).start) (Sigma.snd z u)
local notation3 (prettyPrint := false) "Has(" f "," z "," ns ")" =>
  PLift (∀ u : Fin (R+1), CoreDirectory.IssuedReceipt core portSource ownedSite bottom charts rc f u (pub u)
    ((Sigma.snd z u).2.val.2.2) taskBase (who (Sigma.fst (Sigma.snd f)) (Sigma.fst (Sigma.snd (Sigma.snd f))))
      ((ns u).logicalAt))

set_option maxHeartbeats 850000 in
/-- Read the original supported tuple once, before choosing a continuation.
Its retained owner words and source cells issue the true all-zero private bank
on every inverse prepared candidate. Both arrays are carried by the same
original sparse source for each native processor. -/
noncomputable def PreparedHistoryDecoder.acquiredIssued
    (saved : Parsed → (z : Bare) → Inputs(z) → Type*)
    (acquire : ∀ f : Parsed, Σ native : Inputs(front(f)), Has(f,front(f),native) × saved f (front(f)) native)
    (limit burst : ℕ) (privateSize : TeamScales.width n (1/2)≤burst) :
    let record := fun (g : Parsed) (z : Bare) (ss : Inputs(z)) => Has(g,z,ss) × saved g z ss
    let deployed := decoder.issuedNativeFamily routed record acquire
    ∀ (calls : NativeCalls id B limit burst privateSize deployed) (f : Parsed),
      let prep := (decoder.supported limit burst privateSize calls.next Router Report routed).val
      let actual := prep.symm f
      let z : Bare := ⟨⟨actual.1.val,actual.1.property.1⟩,actual.2⟩
      CoreDirectory.Issued core portSource ownedSite bottom charts rc (supportedTeam id B limit burst privateSize calls.next)
        prep f × Has(f,z,(deployed actual.1 actual.2)) × saved f z (deployed actual.1 actual.2) := by
  intro record deployed calls f prep actual z
  have facts := decoder.issuedFamilyFacts routed limit burst privateSize calls.next record acquire f
  refine ⟨?_,facts⟩
  exact NativeCalls.issuedOnPrefix id B limit burst privateSize deployed calls core portSource ownedSite bottom charts rc prep f
    (who f.2.1 f.2.2.1) (fun _ => taskBase) (owner f.1 f.2.1 f.2.2.1)
    (fun u => (facts.1.down u).ownerTable) (fun u => (facts.1.down u).source)

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
