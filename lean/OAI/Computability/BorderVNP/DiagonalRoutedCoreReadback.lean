import OAI.Computability.BorderVNP.DiagonalPreparedOwnedReportRows
import OAI.Computability.BorderVNP.DiagonalPreparedBankTransport
import OAI.Computability.BorderVNP.DiagonalReceivedCoreSound

/-! # Original routed source rows inside a complete native preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.CoreDirectory

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited
open RoutingISA RoutingISA.Evaluator RoutingISA.CellDispatch DiagonalTallyCellReports CellMacro.Generator
open scoped Classical

variable {D cn cd cb ch cK sym R : ℕ} {P X Raw Hist : Type} [Fintype P] {bits : P → ℕ}
    {N : Hist → Network D P bits} {blocks : Hist → ℕ} (B : ∀ q, CoreDirectory (N q) cn cd (blocks q) cb ch cK R)
    (pin : Raw → Ports bits) (reported : ∀ q,Fin (B q).siteRows → ℕ)
    (bundles : ∀ q, Fin (B q).cells → List Bundle)
    (shape : Raw → (q : Hist) → (B q).Route sym → Fin (R+1) → ReportLayout)
    (received : ∀ i q v, ReceivedRows (shape i q v) (B q).cells)

/-- The report proposals of the jointly decoded source, indexed by actual
owner ordinals before its independent private bank bits are supplied. -/
abbrev Proposals (i : Raw) (q : Hist) (v : (B q).Route sym) :=
  (u : Fin (R+1)) → ReportAssignments ((received i q v).cells u)

local notation3 (prettyPrint := false) "src(" i "," q "," v "," z ")" =>
  (received i q v).assigned (N q) (B q).cell (B q).siteID (B q).edgeID (B q).portID (B q).programs (B q).owners
    (B q).slot (pin i) (reported q) (bundles q) (Subtype.val v) z
local notation3 (prettyPrint := false) "order(" i "," q "," v "," z ")" =>
  (received i q v).physicalReportEquiv (N q) (B q).cell (B q).siteID (B q).edgeID (B q).portID (B q).programs (B q).owners
    (B q).slot (pin i) (reported q) (bundles q) (Subtype.val v) z (received i q v).cells (fun _ => rfl)

variable {dims digits k w : ℕ} {id : TableEntry cn cb ch cK sym → ℕ}
    (S : X → Fin (R+1) → PositiveTeam id SparseExterior.driver k w)
    (prep : JointBeforeCells S ≃ PreparedFields Raw Hist (Fin ((R+1)*dims*digits) → Bool)
      (fun q => (B q).Route sym) (Proposals B shape received))
    (team : (q : Hist) → (B q).Route sym → Fin (B q).cells → Fin (R+1))
    (owned : ∀ i q v u (j : Fin ((received i q v).cells u).length), team q v ((received i q v).order ⟨u,j⟩)=u)

local notation3 (prettyPrint := false) "Fields" => PreparedFields Raw Hist (Fin ((R+1)*dims*digits) → Bool)
  (fun q => (B q).Route sym) (Proposals B shape received)

variable (base : PreparedFields Raw Hist (Fin ((R+1)*dims*digits) → Bool)
    (fun q => (B q).Route sym) (Proposals B shape received) → Fin (R+1) → ℕ)
    (table : ∀ (f : PreparedFields Raw Hist (Fin ((R+1)*dims*digits) → Bool)
      (fun q => (B q).Route sym) (Proposals B shape received)) u,
      let p := prep.symm f
      OwnerTable (S p.1 u).pub ((S p.1 u).postMemory (p.2 u))
        ⟨u.val,base f u,(B f.2.1).cells⟩ (PositiveTeam.ownerWord (team f.2.1 f.2.2.1)))

/-- All the private generators reached on a given public/report proposal have
issued the true typed data of the source. They can be checked at the single
all-zero private vector because the private guesses occur after issuance. -/
abbrev Issued (f : Fields) :=
  let p := prep.symm f
  let i := f.1
  let q := f.2.1
  let v := f.2.2.1
  ReceivedRows.NativeCallInputs (received i q v) (N q) (B q).cell (B q).siteID (B q).edgeID (B q).portID
    (B q).programs (B q).owners (B q).slot (pin i) (reported q) (bundles q) v.val (fun _ _ => false)
    (order(i,q,v,(fun _ _ => false)) f.2.2.2.2) (S p.1) p.2

variable (issued : ∀ f, Issued B pin reported bundles shape received S prep f)

local notation3 (prettyPrint := false) "sizes" => fun q c => externalBase (N q) (B q).cell c (placedSize (N q) (B q).programs)
local notation3 (prettyPrint := false) "count" => fun q => (B q).cells

include issued owned table in
/-- The physical calls determine the q-dependent widths before the source
private choices. This also identifies the width of every empty owned row. -/
theorem issuedWidths (f : Fields) (c : Fin (B f.2.1).cells) :
    let p := prep.symm f
    let u := team f.2.1 f.2.2.1 c
    (((S p.1 u).generated (p.2 u)).cell c.val).privateWires=sizes f.2.1 c := by
  let i := f.1
  let q := f.2.1
  let v := f.2.2.1
  let p := prep.symm f
  exact (received i q v).joined_width (N q) (B q).cell (B q).siteID (B q).edgeID (B q).portID (B q).programs (B q).owners
    (B q).slot (pin i) (reported q) (bundles q) v.val (fun _ _ => false) (order(i,q,v,(fun _ _ => false)) f.2.2.2.2)
    (S p.1) p.2 (team q v) (base f) (table f) (owned i q v) (issued f) c

local notation3 (prettyPrint := false) "widths" => issuedWidths B pin reported bundles shape received S prep team owned base table issued
local notation3 (prettyPrint := false) "joined" => PreparedOwned.join S prep count team base table
local notation3 (prettyPrint := false) "banks" => PreparedOwned.bank S prep count team base table sizes widths

/-- These are the original site directories, raw core choices and boundary
bits read by every cell of a positive preparation. The report order and bank
map are fixed by the native public prefix itself, uniformly over both reports
and claims, before the source guards are evaluated. -/
noncomputable def preparedRoutedRows (i : Raw) (q : Hist) (v : (B q).Route sym × (B q).Bank) :
    PreparedCellRows (Bank := fun h => (B h).Bank) S joined prep banks i q v := by
  let rr := received i q v.1
  let map := order(i,q,v.1,v.2)
  refine PreparedOwned.cellRows S prep count team base table sizes widths i q v (shape i q v.1)
    (src(i,q,v.1,v.2)) map ?_
  intro r claim f
  let p := prep.symm f
  let proposal := map.symm r
  have image := rr.physicalReportImage (N q) (B q).cell (B q).siteID (B q).edgeID (B q).portID (B q).programs (B q).owners
    (B q).slot (pin i) (reported q) (bundles q) v.1.val v.2 (S p.1) p.2 (team q v.1) (base f) (table f) (owned i q v.1)
    rr.cells (fun _ => rfl) proposal (widths f) (issued f)
  change (PreparedOwned.observed S prep count team base table f).ReportImage
    (((PreparedOwned.observed S prep count team base table f).bankEquiv (Equiv.refl _) (sizes q) (widths f)).symm v.2)
    (src(i,q,v.1,v.2)) (map proposal) at image
  simpa only [proposal,Equiv.apply_symm_apply] using image

/-- The actual candidate retains the source layout and all ordered issued
cells of this routed assignment, with the same dependent report types. -/
theorem preparedRoutedRows_source (i : Raw) (q : Hist) (v : (B q).Route sym × (B q).Bank) :
    let a := (preparedRoutedRows B pin reported bundles shape received S prep team owned base table issued i q v).candidate
    a.layout=shape i q v.1 ∧ HEq a.assigned (src(i,q,v.1,v.2)) := ⟨rfl,HEq.rfl⟩

/-- A surviving physical product forces the fixed source guard on the exact
routed assignment and original private bank recovered by the prefix decoder. -/
theorem preparedRoutedSound (i : Raw) (q : Hist) (v : (B q).Route sym × (B q).Bank)
    (ownerAt : ∀ x, reported q ((B q).siteID x)=((B q).cell x).val)
    (legal : ∀ x, ((B q).programs x).birth.Local ∧ ((B q).programs x).program.Schema ∧
      ((B q).programs x).program.RelativeBoxes ∧ ((B q).programs x).program.SignFree) :
    let A := (preparedRoutedRows B pin reported bundles shape received S prep team owned base table issued i q v).candidate
    ∀ rr claim, (A.joined rr claim (A.candidate rr claim).1).privateWeight (A.candidate rr claim).2 ≠ 0 →
      (B q).Guard (pin i) v := by
  intro A rr claim positive
  exact (B q).receivedSound (pin i) (reported q) (bundles q) ownerAt legal v A (received i q v.1)
    rfl rr claim positive

end Cube.Physical.NativeAssignments.CoreDirectory

end BorderVNP
end Computability
end OAI
