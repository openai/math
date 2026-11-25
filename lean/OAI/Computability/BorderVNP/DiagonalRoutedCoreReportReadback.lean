import OAI.Computability.BorderVNP.DiagonalRoutedCoreReadback
import OAI.Computability.BorderVNP.DiagonalCanonicalSameRows

/-! # Reading the original prepared inverse of a native subtotal proposal -/

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

variable (issued : ∀ f, Issued B pin reported bundles shape received S prep f)


variable (i : Raw) (q : Hist) (v : (B q).Route sym × (B q).Bank)
local notation3 (prettyPrint := false) "A" =>
  preparedRoutedRows B pin reported bundles shape received S prep team owned base table issued i q v
local notation3 (prettyPrint := false) "back" r =>
  (order(i,q,v.1,v.2)).symm r
local notation3 (prettyPrint := false) "field(" r "," c ")" => prep.symm ⟨i,q,v.1,c,back r⟩

/-- The inverse report rows used by the native candidate are the ones
decoded by the original received-directory equivalence. -/
theorem preparedRoutedRows_proposal (r : NativeReports (A).candidate.assigned) :
    (A).order.symm r = back r := rfl

/-- Rewriting the layout proof supplied by the issued-row theorem preserves
the exact inverse physical proposal on which the original preparation ran. -/
theorem preparedRoutedRows_castProposal (layout : (A).candidate.layout=shape i q v.1)
    (rows : HEq (A).candidate.assigned (src(i,q,v.1,v.2))) (r : NativeReports (A).candidate.assigned) :
    (order(i,q,v.1,v.2)).symm (reportsOfSameRows layout rows r)=(A).order.symm r := by
  exact congrArg (order(i,q,v.1,v.2)).symm (reportsOfSameRows_self layout rows r)

/-- Transport a source certificate to the actual candidate. The first
proposal specifies the native execution through the original prepared inverse.
The second supplies the retained tape. At the genuine source they coincide. -/
theorem preparedRoutedRows_runs (layout : (A).candidate.layout=shape i q v.1)
    (rows : HEq (A).candidate.assigned (src(i,q,v.1,v.2)))
    (work : Proposals B shape received i q v.1 → Proposals B shape received i q v.1 →
      (Fin ((R+1)*dims*digits) → Bool) → Fin (R+1) → Prop)
    (source : ∀ r c t,work r r c t) (r : NativeReports (A).candidate.assigned)
    (c : Fin ((R+1)*dims*digits) → Bool) (t : Fin (R+1)) :
    work ((A).order.symm r) ((order(i,q,v.1,v.2)).symm (reportsOfSameRows layout rows r)) c t :=
  Eq.mpr (congrArg (fun tape => work ((A).order.symm r) tape c t)
    (preparedRoutedRows_castProposal B pin reported bundles shape received S prep team owned base table
      issued i q v layout rows r)) (source ((A).order.symm r) c t)

/-- A returned physical run on each source prefix applies to the very
team and argument return selected by the candidate. Its tape is rewritten
by the same physical report inverse that determined that prefix. -/
theorem preparedRoutedRows_originalRuns (layout : (A).candidate.layout=shape i q v.1)
    (rows : HEq (A).candidate.assigned (src(i,q,v.1,v.2)))
    (work : Fin (R+1) → (u : PositiveTeam id SparseExterior.driver k w) →
      u.Prefix → Proposals B shape received i q v.1 → (Fin ((R+1)*dims*digits) → Bool) → Prop)
    (source : ∀ (r : Proposals B shape received i q v.1) (c : Fin ((R+1)*dims*digits) → Bool) t,
      let path := prep.symm ⟨i,q,v.1,c,r⟩
      work t (S path.1 t) (path.2 t) r c)
    (r : NativeReports (A).candidate.assigned) (c : Fin ((R+1)*dims*digits) → Bool) (t : Fin (R+1)) :
    work t ((A).candidate.team r c t) (((A).candidate.candidate r c).1 t)
      ((order(i,q,v.1,v.2)).symm (reportsOfSameRows layout rows r)) c :=
  preparedRoutedRows_runs B pin reported bundles shape received S prep team owned base table issued i q v layout rows
    (fun exec tape cc u => let path := prep.symm ⟨i,q,v.1,cc,exec⟩; work u (S path.1 u) (path.2 u) tape cc)
    source r c t

/-- A candidate reads its public operands at the original exterior and its
per-team private argument return at the same prepared inverse. -/
theorem preparedRoutedRows_prefix (r : NativeReports (A).candidate.assigned)
    (c : Fin ((R+1)*dims*digits) → Bool) :
    (A).candidate.team r c = S (field(r,c)).1 ∧
      HEq ((A).candidate.candidate r c).1 (field(r,c)).2 := ⟨rfl,HEq.rfl⟩

/-- The fixed public control frame is read from the same returned prefix for
every proposed report and every subtotal. -/
theorem preparedRoutedRows_frame (frame : ℕ) (original : ∀ x u,((S x u).pub 0).val=frame)
    (r : NativeReports (A).candidate.assigned) (c : Fin ((R+1)*dims*digits) → Bool) (u : Fin (R+1)) :
    frame=(((A).candidate.team r c u).pub 0).val := (original (field(r,c)).1 u).symm

end Cube.Physical.NativeAssignments.CoreDirectory

end BorderVNP
end Computability
end OAI
