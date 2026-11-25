import OAI.Computability.BorderVNP.DiagonalExteriorPrefixBanks
import OAI.Computability.BorderVNP.DiagonalPositiveCoreReports

/-! # Installing the original native prefix and private bits in the report and claim checks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction ProcessorSlots CellMacro.Generator BorderVNP.Cube DiagonalTallyCellReports
open scoped Classical

variable {R n w dim width axes b h K s : ℕ} {id : TableEntry axes b h K s → ℕ} {gen : Fragment IO}
    {X Raw Hist : Type} {Route : Hist → Type} {Bank : Hist → Type} {Report : (i : Raw) → (q : Hist) → Route q → Type}
    (S : X → Fin (R+1) → PositiveTeam id gen n w)
    (J : ∀ x (p : (u : Fin (R+1)) → (S x u).Prefix),
      JoinedCells (fun u => (S x u).pub) (fun u => (S x u).postMemory) (fun u => (S x u).generated) p)
local notation "Claim" => (Fin ((R+1)*dim*width) → Bool)
variable (prep : JointBeforeCells S ≃ PreparedFields Raw Hist (Fin ((R+1)*dim*width) → Bool) Route Report)
    (banks : ∀ f : PreparedFields Raw Hist (Fin ((R+1)*dim*width) → Bool) Route Report,
      (J (prep.symm f).1 (prep.symm f).2).Private ≃ Bank f.2.1)
    (i : Raw) (q : Hist) (v : Route q × Bank q) {layout : Fin (R+1) → ReportLayout}
    (assigned : ∀ u,List (AssignedCell (layout u))) (rmap : Report i q v.1 ≃ NativeReports assigned)

local notation3 (prettyPrint := false) "fields(" rr "," cc ")" =>
  (⟨i,q,v.1,cc,rmap.symm rr⟩ : PreparedFields Raw Hist (Fin ((R+1)*dim*width) → Bool) Route Report)
local notation3 (prettyPrint := false) "prefix(" rr "," cc ")" => prep.symm fields(rr,cc)

/-- At every report and shared subtotal proposal, the genuine call row reads
the corresponding registered bits from the restored native private bank. -/
abbrev PreparedReportImage :=
  ∀ (rr : NativeReports assigned) (cc : Fin ((R+1)*dim*width) → Bool),
    (J (prefix(rr,cc)).1 (prefix(rr,cc)).2).ReportImage ((banks fields(rr,cc)).symm v.2) assigned rr

/-- The unchecked candidate uses the actual shared exterior, each physical
team's original full return, and that prefix's addressed private core. -/
noncomputable def preparedUnchecked (image : PreparedReportImage S J prep banks i q v assigned rmap) :
    UncheckedCandidate id gen n w (R+1) dim width where
  layout := layout
  assigned := assigned
  team rr cc := S (prefix(rr,cc)).1
  joined rr cc := J (prefix(rr,cc)).1
  candidate rr cc := sourceCandidate S J prep banks i q v (rmap.symm rr) cc
  image := image

/-- The renaming of true owned report rows preserves the complete original
positive predicate on each proposal. No returning finish or report values
are assumed in this transport. -/
noncomputable def preparedReportsEquiv (image : PreparedReportImage S J prep banks i q v assigned rmap) :
    let A := preparedUnchecked S J prep banks i q v assigned rmap image
    (Σ r : Report i q v.1, {c : Claim // sourcePass S J prep banks i q v r c}) ≃
      Σ rr : NativeReports assigned, {c : Claim // positivePass (A.team rr c) (A.joined rr c) (A.candidate rr c)} :=
  Equiv.sigmaCongrLeft' (β:=fun r => {c : Claim // sourcePass S J prep banks i q v r c}) rmap

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
