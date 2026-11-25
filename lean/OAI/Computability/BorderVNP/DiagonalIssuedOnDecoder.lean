import OAI.Computability.BorderVNP.DiagonalAcquiredIssuedCalls

/-! # Apply the issued-source theorem on the decoder's own startup -/

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


variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}

/-- On the physical decoder the input layout, initial registers, word fit and
boot provenance are determined by that decoder. Only the selected core and
frozen source family remain to be provided at deployment. -/
noncomputable abbrev PreparedHistoryDecoder.issuedAtCore :=
  PreparedHistoryDecoder.acquiredIssued id G pub reg pin L headerWidth code args fixed hw size base fit B
    core portSource ownedSite bottom charts rc who owner taskBase routed decoder

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
