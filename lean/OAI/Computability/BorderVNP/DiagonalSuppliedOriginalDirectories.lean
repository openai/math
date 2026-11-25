import OAI.Computability.BorderVNP.DiagonalBeforeIssuedCalls
import OAI.Computability.BorderVNP.DiagonalIssuedFactFamily
import OAI.Computability.BorderVNP.DiagonalSparsePlacementEvidence

/-! # Keeping the physical launch in the acquired source family -/

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

variable (decoder : PreparedHistoryDecoder SparseExterior.driver id G pub reg pin L headerWidth code args fixed hw size base fit B)

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

local notation3 (prettyPrint := false) "Router" => (fun h : Hist => (core h).Route symbols)
local notation3 (prettyPrint := false) "Report" => CoreDirectory.Proposals core charts rc
local notation3 (prettyPrint := false) "Bare" => ((x : {ext // PositiveExterior G args pin w ext}) ×
  ((u : Fin (R+1)) → (B x u).start.Prefix id))
local notation3 (prettyPrint := false) "Parsed" => PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool)
  Router Report
variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}
/-- Enumerate the *supplied* native launch of every original team. Its
receipt and placement are dependent fields of that very launch. -/
noncomputable def PreparedHistoryDecoder.suppliedOriginalDirectories
    {Keys Slots : Hist → Type} {cells : Hist → ℕ}
    (directory : (h : Hist) → CellPacketGeometry.SiteWords.Directory (Keys h) (Slots h) (cells h+1))
    (routed : ∀ (i : Fin d → Bool) (h : Hist) (c : Fin ((R+1)*dim*tally) → Bool), (Σ p : Physical.Broadcast axes groups cap,
      ParsedPreCall G args pin L fixed hw size base fit headerWidth (fun x u => (B x u).start)
        (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id i ⟨code h,p,c⟩) ≃
        Σ v : (core h).Route symbols, CoreDirectory.Proposals core charts rc i h v) :=
  let front := fun f : Parsed => routedBareTuple routed f
  let localSource := fun (z : Bare) (u : Fin (R+1)) =>
    PinStart.SparseSource id (fun t => (B z.1 t).start) (z.2 u)
  let nativeAt := fun z : Bare => (u : Fin (R+1)) → localSource z u
  let reads := fun (f : Parsed) (z : Bare) (u : Fin (R+1)) (ns : localSource z u) =>
    CoreDirectory.IssuedReceipt core portSource ownedSite bottom charts rc f u (pub u) ((z.2 u).2.val.2.2)
      taskBase (who f.2.1 f.2.2.1) ns.logicalAt
  let held := fun (f : Parsed) (z : Bare) (u : Fin (R+1)) (ns : localSource z u) =>
    SavedSparsePlacement (directory f.2.1) ns.logicalAt
  let record := fun (f : Parsed) (z : Bare) (native : nativeAt z) =>
    PLift (∀ u, reads f z u (native u)) × (∀ u, held f z u (native u))
  fun (packets : ∀ (f : Parsed) (u : Fin (R+1)), Σ ns : localSource (front f) u,
      PLift (reads f (front f) u ns) × held f (front f) u ns) =>
    let acquired (f : Parsed) : (native : nativeAt (front f)) × record f (front f) native :=
      ⟨(fun u => (packets f u).1), ⟨fun u => (packets f u).2.1.down⟩, fun u => (packets f u).2.2⟩
    (acquired,decoder.issuedNativeFamily routed record acquired)

variable {Keys Slots : Hist → Type} {cells : Hist → ℕ}
    (directory : (h : Hist) → CellPacketGeometry.SiteWords.Directory (Keys h) (Slots h) (cells h+1))

/-- The type of the map taking a routed branch and its already issued
per-team packets to the joint native source. -/
noncomputable def PreparedHistoryDecoder.OriginalPacketMap : Type _ :=
  type_of% (decoder.suppliedOriginalDirectories core portSource ownedSite bottom charts rc who taskBase directory)

/-- Keep the type of the original packet map named when installing it on
the much larger concrete calendar. -/
noncomputable def PreparedHistoryDecoder.originalPacketMap :
    PreparedHistoryDecoder.OriginalPacketMap (id:=id) (G:=G) (pub:=pub) (reg:=reg) (pin:=pin)
      (L:=L) (headerWidth:=headerWidth) (code:=code) (args:=args) (fixed:=fixed) (hw:=hw)
      (size:=size) (base:=base) (fit:=fit) (B:=B) core portSource ownedSite bottom charts rc who taskBase directory :=
  decoder.suppliedOriginalDirectories core portSource ownedSite bottom charts rc who taskBase directory

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
