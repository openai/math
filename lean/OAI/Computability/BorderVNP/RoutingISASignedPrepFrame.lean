import OAI.Computability.BorderVNP.RoutingISASignedPrepEnd
import OAI.Computability.BorderVNP.RoutingISASignedPrepBroadcast

/-! # The physical schedule and its admissible signed builders at one broadcast -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (L : WireLayout (R+1) r link) (ar : CubeArena.Layout) (decl : LengthDeclaration ar.n ar.header.d)
    (fixed : Block (R+1)) (header : List Bool) (pin : Fin d → Bool)
    (pub : HeaderExterior L header → Fin (R+1) → Arg → Word w)
    (mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior L header → Fin (R+1) → Bank w) (mem : HeaderExterior L header → Fin (R+1) → Memory w)

local notation "Domain" => HeaderExterior L header

/-- The actual profile and decoded public scheduling directory on exteriors sharing
one fixed bit header, before any owned-cell choices. -/
structure PreparationFrame where
  length : header.length=L.header
  /-- Memory layout of the native routing table. -/
  tab : TableLayout
  /-- Route record written at each table index. -/
  row : ℕ → TableRow
  /-- Directory of the original private and live deliveries. -/
  dataDir : Packing.Directory.Layout
  /-- Receiving cell and bit offset for each original private entry. -/
  privatePlacement : ℕ → ℕ × ℕ
  /-- Receiving cell and bit offset for each live input slice. -/
  livePlacement : ℕ → ℕ × ℕ
  /-- Team to which the public schedule assigns a cell. -/
  cellOwner : ℕ → Fin (R+1)
  /-- Starting address of the receiving cell banks. -/
  origin : ℕ
  /-- Distance between consecutive receiving cell banks. -/
  stride : ℕ
  /-- Destination address of the copied common broadcast on each team. -/
  destination : Fin (R+1) → ℕ
  /-- Starting address of the substituted column on each team. -/
  inputBase : Fin (R+1) → ℕ
  /-- Starting address of the live column on each team. -/
  columnBase : Fin (R+1) → ℕ
  /-- Starting address of the reference column in each team’s gathered advice. -/
  referenceBase : Fin (R+1) → ℕ
  /-- Substitution bits installed at each team’s selected pin. -/
  guess : Fin (R+1) → ℕ → Bool
  /-- Layout of the shared rows written from the native source memories. -/
  rows : SharedRows.Layout
  /-- The shared-row writer reads each team’s memory on this same exterior. -/
  source : Domain → Fin (R+1) → ℕ → ℕ
  /-- Team assigned to each group in the public declaration. -/
  group : Fin ar.header.d → Fin (R+1)
  /-- Team whose source memory certifies the declaration and the group owners. -/
  anchor : Fin (R+1)
  /-- Native scheduling return on every exterior with this header and every team. -/
  schedule : ∀ x u, Returns (SignedPrep.schedule ar.n ar.K ar.h) (pub x u) (mac x u) (reg x u) (mem x u)
  empty : ∀ x u, (schedule x u).val.1.flatMap TeamRAM.Event.choices=[]
  initialized : ∀ x : Domain, SharedRoutePrepared G pin x.val L dataDir privatePlacement livePlacement cellOwner
    origin stride tab row (pub x) (fun u => (schedule x u).val.2.2) destination inputBase columnBase referenceBase guess
  /-- Native common-header copy and its returned memory on each exterior. -/
  copies : ∀ x : Domain, ReturnedHeaders G pin x.val L w
  emitted : ∀ x u, rows.Emitted (source x u) (readings (schedule x u).val.2.2)
  fitted : ∀ x u, rows.Fits w (source x u)
  records : tab.records=rows.records
  count : tab.count=rows.dataCount+rows.groups.choose 2
  dataCount : (dataDir.directory privatePlacement livePlacement).length=rows.dataCount
  room : rows.banks+rows.stride*rows.groups^2≤2^w
  frame : ∀ x, SymbolFrame rows (source x anchor) ar.header.blocks ar.K ar.h decl group

variable {G L ar decl header pin pub mac reg mem}
    (F : PreparationFrame G L ar decl header pin pub mac reg mem)

/-- The returned native exterior and each team's physical route state for these row words. -/
noncomputable def PreparationFrame.replay (raw : SharedWords ar decl) :=
  (exteriorNativeRoutesEquiv G L F.tab F.row F.dataDir F.privatePlacement F.livePlacement F.guess F.rows decl fixed
    header F.length pub mac (fun x u => (F.schedule x u).val.2.1) (fun x u => (F.schedule x u).val.2.2)
    F.initialized F.copies F.emitted F.fitted F.records F.count F.dataCount F.room F.frame).symm raw

variable (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))

/-- Concrete word-level builder operands at every replayed shared-row array. -/
abbrev PreparationFrame.Builders :=
  ∀ raw : SharedWords ar decl, let z := F.replay fixed raw
    DeliveredBuilder ar owners decl raw.val id (pub z.1) (mac z.1) (fun u => (z.2 u).val.2.1) (fun u => (z.2 u).val.2.2)

local notation "Input" => signedInputs id (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s)
local notation "Prepared" => prepareExpansion epochPlacement (scheduleGroups ar.n (selectorWidth ar.n ar.K ar.h)) Input

/-- The joint pre-call paths on the physical states of this schedule, with the
shared words eliminated and the complete local report assignments retained. -/
noncomputable def PreparationFrame.returnEquiv (B : F.Builders fixed id owners) :
    let pins := fun raw => (B raw).pins
    (Σ x : Domain, (u : Fin (R+1)) → Returns Prepared (pub x u) (mac x u) (reg x u) (mem x u)) ≃
      Σ q : PinnedDeclared ar owners decl pins, let x := (pinnedMatchingEquiv ar owners decl pins).symm q
        (u : Fin (R+1)) → ReportAssignments ((B x.1).localRows x.2 u).cells :=
  nativePreparedReportEquiv G L F.tab F.row F.dataDir F.privatePlacement F.livePlacement F.guess F.rows ar decl fixed
    header F.length id owners pub mac reg mem F.schedule F.empty F.initialized F.copies F.emitted F.fitted
    F.records F.count F.dataCount F.room F.frame B

end TeamContraction

end BorderVNP
end Computability
end OAI
