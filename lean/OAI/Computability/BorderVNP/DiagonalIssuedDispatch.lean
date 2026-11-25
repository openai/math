import OAI.Computability.BorderVNP.DiagonalIssuedSourceCall
import OAI.Computability.BorderVNP.DiagonalRoutedCoreReadback

/-! # Native issuance through the positive scheduler's actual dispatch table -/

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

local notation3 (prettyPrint := false) "Fields" => PreparedFields Raw Hist (Fin ((R+1)*dims*digits) → Bool)
  (fun q => (B q).Route sym) (Proposals B shape received)


open RoutingISA.CompactMachine VPVNP.BurstRAM
variable (f : PreparedFields Raw Hist (Fin ((R+1)*dims*digits) → Bool)
    (fun q => (B q).Route sym) (Proposals B shape received))
local notation3 (prettyPrint := false) "access" => prep.symm f
local notation3 (prettyPrint := false) "net" => N f.2.1
local notation3 (prettyPrint := false) "core" => B f.2.1
local notation3 (prettyPrint := false) "rr" => received f.1 f.2.1 f.2.2.1
local notation3 (prettyPrint := false) "native" => order(f.1,f.2.1,f.2.2.1,(fun _ _ => false)) f.2.2.2.2
local notation3 (prettyPrint := false) "actualCall" =>
  (rr).sourceCall net (core).cell (core).siteID (core).edgeID (core).portID (core).programs (core).owners (core).slot
    (pin f.1) (reported f.2.1) (bundles f.2.1) f.2.2.1.val (fun _ _ => false) native
/-- The real sparse cell read on the chosen issuing team identifies the native
zero-bank call at its compact ordinal. The dispatcher checks the reached owner
before consulting the source's logical field. -/
noncomputable def issuedFromDispatch
    (who : Fin (core).cells → Fin (R+1))
    (owned : ∀ u (i : Fin ((rr).cells u).length), who ((rr).order ⟨u,i⟩)=u)
    (published : Fin (R+1) → ℕ → CellInput) (base : Fin (R+1) → ℕ)
    (table : ∀ u,OwnerTable (S (access).1 u).pub ((S (access).1 u).postMemory ((access).2 u))
      ⟨u.val,base u,(core).cells⟩ (PositiveTeam.ownerWord who))
    (read : ∀ u, let p := (access).2 u
      let T := S (access).1 u
      let row := Frame.ofMemory T.pub (T.postMemory p)
      ∀ c<row.count,readings (T.postMemory p) (row.address c)=row.team → (T.generated p).cell c=published u c)
    (seen : ∀ u (i : Fin ((rr).cells u).length), published u ((rr).order ⟨u,i⟩).val=actualCall u i) :
    Issued B pin reported bundles shape received S prep f := by
  apply ReceivedRows.NativeCallInputs.ofSourceCall
  intro u i
  let c := (rr).order ⟨u,i⟩
  let row := Frame.ofMemory (S (access).1 u).pub ((S (access).1 u).postMemory ((access).2 u))
  have frame : row=⟨u.val,base u,(core).cells⟩ := (table u).frame
  have size : c.val<row.count := by rw [frame]; exact c.isLt
  have tag := (table u).atRow c.val c.isLt
  have whoAt : who c=u := owned u i
  rw [PositiveTeam.ownerWord,dite_eq_left c.isLt,whoAt] at tag
  have owner : readings ((S (access).1 u).postMemory ((access).2 u)) (row.address c.val)=row.team := by
    rw [frame]
    exact tag
  exact (read u c.val size owner).trans (seen u i)

end Cube.Physical.NativeAssignments.CoreDirectory

end BorderVNP
end Computability
end OAI
