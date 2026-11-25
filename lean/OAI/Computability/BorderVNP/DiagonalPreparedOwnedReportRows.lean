import OAI.Computability.BorderVNP.DiagonalAcceptedGuardedCores
import OAI.Computability.BorderVNP.DiagonalPreparedOwnedJoin

/-! # Report rows on the private bank of the decoded owned dispatch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PreparedOwned

open TeamContraction TeamContraction.ProcessorSlots CellDispatch CellMacro.Generator BorderVNP.Cube DiagonalTallyCellReports
open scoped Classical

variable {R n w axes b h K s dim digits : ℕ} {id : TableEntry axes b h K s → ℕ} {gen : Fragment IO}
    {X Raw Hist : Type} {Route : Hist → Type}
    {Report : (i : Raw) → (q : Hist) → Route q → Type}
    (S : X → Fin (R+1) → PositiveTeam id gen n w)
    (prep : JointBeforeCells S ≃ PreparedFields Raw Hist (Fin ((R+1)*dim*digits) → Bool) Route Report)
    (cells : Hist → ℕ) (owner : (q : Hist) → Route q → Fin (cells q) → Fin (R+1))
    (base : PreparedFields Raw Hist (Fin ((R+1)*dim*digits) → Bool) Route Report → Fin (R+1) → ℕ)
    (table : ∀ (f : PreparedFields Raw Hist (Fin ((R+1)*dim*digits) → Bool) Route Report) u,
      let z := prep.symm f
      OwnerTable (S z.1 u).pub ((S z.1 u).postMemory (z.2 u)) ⟨u.val,base f u,cells f.2.1⟩
        (PositiveTeam.ownerWord (owner f.2.1 f.2.2.1)))
    (size : ∀ q, Fin (cells q) → ℕ)
    (width : ∀ (f : PreparedFields Raw Hist (Fin ((R+1)*dim*digits) → Bool) Route Report) (c : Fin (cells f.2.1)),
      let z := prep.symm f
      let u := owner f.2.1 f.2.2.1 c
      (((S z.1 u).generated (z.2 u)).cell c.val).privateWires=size f.2.1 c)

local notation "Fields" => PreparedFields Raw Hist (Fin ((R+1)*dim*digits) → Bool) Route Report
local notation3 (prettyPrint := false) "J₀" => join S prep cells owner base table
local notation3 (prettyPrint := false) "B₀" => bank S prep cells owner base table size width
local notation3 (prettyPrint := false) "J(" f ")" => observed S prep cells owner base table f

variable (i : Raw) (q : Hist) (v : Route q × ((c : Fin (cells q)) → Fin (size q c) → Bool))
    (layout : Fin (R+1) → ReportLayout) (ss : ∀ u,List (AssignedCell (layout u)))
    (order : Report i q v.1 ≃ NativeReports ss)

/-- Install a received source directory on the public join, using the actual
owner-dispatched sparse call at each report and subtotal proposal. -/
noncomputable def cellRows
    (observedRows : ∀ (rr : NativeReports ss) (cc : Fin ((R+1)*dim*digits) → Bool),
      let f : Fields := ⟨i,q,v.1,cc,order.symm rr⟩
      (J(f)).ReportImage (((J(f)).bankEquiv (Equiv.refl _) (size q) (width f)).symm v.2) ss rr) :
    PreparedCellRows (Bank := fun z => (c : Fin (cells z)) → Fin (size z c) → Bool) S J₀ prep B₀ i q v where
  layout := layout
  cells := ss
  order := order
  read rr cc := reportImage S prep cells owner base table size width ⟨i,q,v.1,cc,order.symm rr⟩ v.2 ss rr (observedRows rr cc)

end RoutingISA.Evaluator.PreparedOwned

end BorderVNP
end Computability
end OAI
