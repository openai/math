import OAI.Computability.BorderVNP.RoutingISASignedPrepRows
import OAI.Computability.BorderVNP.DiagonalPositiveExteriorPrepare

/-! # Joint signed preparations at a fixed public profile and substituted column -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Physical.NativeAssignments DiagonalTallyCellReports
open BorderVNP.FiniteEvaluator

variable {R w : ℕ} (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (decl : LengthDeclaration ar.n ar.header.d) (raw : Symbols ar.header.d → List Bool)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (pub : Fin (R+1) → Arg → Word w) (mac : Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : Fin (R+1) → Bank w) (mem : Fin (R+1) → Memory w)

/-- Data of the three physically validated local stages after a fixed delivery.
The owned cube path bijection is `SharedWriters.physicalOwnedEquiv`, the padding
guards are `SharedWriters.controls_iff_pins`, and `LocalReportData` gives the
actual directory operands for the native report and typed sparse writers. -/
structure DeliveredBuilder where
  /-- Real returning instructions installing the cube lookup tables. -/
  constants : ∀ u, Returns (CubeConstants.install id) (pub u) (mac u) (reg u) (mem u)
  /-- The physical ownership fiber on the installed states. -/
  owned : OwnedRuns ar pub mac (fun u => (constants u).val.2.1) (fun u => (constants u).val.2.2) ≃
    Matching ar owners decl raw
  /-- Each decoded assignment spells its true private choices and received rows. -/
  observes : ∀ z, Cube.Scatter.Assignment.Routed.encode owners (owned z).val =
    (ownedHistory ar pub mac (fun u => (constants u).val.2.1) (fun u => (constants u).val.2.2) z).observed ar decl raw
  /-- Both ends of each unused physical host slot pass the zero tests. -/
  pins : Matching ar owners decl raw → Prop
  /-- Actual host, bundle and control directories for the received cube assignment. -/
  controlsAt : Matching ar owners decl raw → Fin (R+1) → OpenSuffix.Inputs
  paths : ∀ a : Matching ar owners decl raw, let z := owned.symm a
    OpenSuffix.ControlFamily (controlsAt a) pub mac (fun u => (z u).val.2.1) (fun u => (z u).val.2.2) (pins a)
  /-- Physical report and typed operands on the native owned scan output. -/
  localRows : ∀ a : Subtype pins, ∀ u, let z := owned.symm a.val u
    LocalReportData (pub u) (mac u) z.val.2.1 z.val.2.2

end RoutingISA.Evaluator.SignedPrep

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w : ℕ} {Edge : Type}
variable (G : Wiring R r t d link inner n Edge) (L : WireLayout (R+1) r link)
variable (tab : TableLayout) (row : ℕ → TableRow) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
variable (guess : Fin (R+1) → ℕ → Bool) (g : SharedRows.Layout) (ar : CubeArena.Layout)
variable (decl : LengthDeclaration ar.n ar.header.d) (fixed : Block (R+1)) (header : List Bool) (len : header.length=L.header)
variable (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
variable (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))

local notation "Domain" => HeaderExterior L header
local notation "Input" => signedInputs id (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s)
local notation "Prepared" => prepareExpansion epochPlacement (scheduleGroups ar.n (selectorWidth ar.n ar.K ar.h)) Input

/-- Every family of genuine pre-call preparations, including its actual exterior,
is indexed at the fixed public header by one pinned routed assignment and the
independently sampled physical report digits at its true receiving cells. -/
noncomputable def nativePreparedReportEquiv {pin : Fin d → Bool} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {dst ib hb sb : Fin (R+1) → ℕ} {src : HeaderExterior L header → Fin (R+1) → ℕ → ℕ}
    {group : Fin ar.header.d → Fin (R+1)} {anchor : Fin (R+1)}
    (pub : Domain → Fin (R+1) → Arg → Word w) (mac : Domain → Fin (R+1) → TeamOpcode.Macros w 8)
    (bank : Domain → Fin (R+1) → Bank w) (mem : Domain → Fin (R+1) → Memory w)
    (schedule : ∀ x u, Returns (SignedPrep.schedule ar.n ar.K ar.h) (pub x u) (mac x u) (bank x u) (mem x u))
    (empty : ∀ x u, (schedule x u).val.1.flatMap TeamRAM.Event.choices=[])
    (initialized : ∀ x : Domain, SharedRoutePrepared G pin x.val L D pp lp owner origin stride tab row (pub x)
      (fun u => (schedule x u).val.2.2) dst ib hb sb guess)
    (copies : ∀ x : Domain, ReturnedHeaders G pin x.val L w)
    (emitted : ∀ x u, g.Emitted (src x u) (readings (schedule x u).val.2.2)) (fitted : ∀ x u, g.Fits w (src x u))
    (records : tab.records=g.records) (count : tab.count=g.dataCount+g.groups.choose 2)
    (dataCount : (D.directory pp lp).length=g.dataCount) (room : g.banks+g.stride*g.groups^2 ≤ 2^w)
    (frame : ∀ x, SymbolFrame g (src x anchor) ar.header.blocks ar.K ar.h decl group) :
    let E := exteriorNativeRoutesEquiv G L tab row D pp lp guess g decl fixed header len pub mac
      (fun x u => (schedule x u).val.2.1) (fun x u => (schedule x u).val.2.2) initialized copies
      emitted fitted records count dataCount room frame
    ∀ (B : ∀ raw : SharedWords ar decl, let z := E.symm raw
      DeliveredBuilder ar owners decl raw.val id (pub z.1) (mac z.1) (fun u => (z.2 u).val.2.1) (fun u => (z.2 u).val.2.2)),
    let pins := fun raw => (B raw).pins
    (Σ x : Domain, (u : Fin (R+1)) → Returns Prepared (pub x u) (mac x u) (bank x u) (mem x u)) ≃
      Σ q : PinnedDeclared ar owners decl pins, let x := (pinnedMatchingEquiv ar owners decl pins).symm q
        (u : Fin (R+1)) → ReportAssignments ((B x.1).localRows x.2 u).cells := by
  intro E B pins
  let source := exteriorPreparedEquiv G L tab row D pp lp guess g decl fixed header len id pub mac bank mem schedule
    empty initialized copies emitted fitted records count dataCount room frame
  let cut (raw : SharedWords ar decl) := nativeOwnedReportEquiv ar owners decl raw.val id _ _ _ _
    (B raw).constants (B raw).owned (B raw).pins (B raw).controlsAt (B raw).paths (B raw).localRows
  exact source.trans ((Equiv.sigmaCongrRight cut).trans (jointRowReportsEquiv ar owners decl pins
    (fun raw q u => ((B raw).localRows q u).layout) (fun raw q u => ((B raw).localRows q u).cells)))

end TeamContraction

end BorderVNP
end Computability
end OAI
