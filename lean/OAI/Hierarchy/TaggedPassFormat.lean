import OAI.Hierarchy.TaggedPassFormatCore
import OAI.Hierarchy.CorrectionFrame
import OAI.Hierarchy.CatalystSubstitutionHost
import OAI.Hierarchy.TaggedData

namespace OAI
/-! # Three exposed oracle banks in a stable radix pass -/
noncomputable section
namespace Hierarchy.Tagged.Radix
open Catalyst CatalystSubstitution CorrectionFrame

structure PassFormat.Calls (g : PassFormat) (F : Type*) [Field F] (k : ℕ) where
  first : Approximation F k (g.copies*pins g.first g.firstW)
  second : Approximation F k (g.copies*pins g.second g.secondW)
  wide : Approximation F k (pins g.wide g.wideW)

variable {F : Type*} [Field F] {k : ℕ} {g : PassFormat}

def PassFormat.Calls.occurrences (Y : g.Calls F k) : List (Occurrence F k) :=
  [⟨_,dataProduct g.copies (coeff F g.first g.firstW),Y.first⟩,
   ⟨_,dataProduct g.copies (coeff F g.second g.secondW),Y.second⟩,
   ⟨_,coeff F g.wide g.wideW,Y.wide⟩]

structure PassFormat.Calls.Paid (Y : g.Calls F k) (localBill wideBill G : ℝ) : Prop where
  firstCost : (Y.first.size:ℝ) ≤ localBill
  secondCost : (Y.second.size:ℝ) ≤ localBill
  wideCost : (Y.wide.size:ℝ) ≤ wideBill
  firstGap : Y.first.Gap (dataProduct g.copies (coeff F g.first g.firstW)) G
  secondGap : Y.second.Gap (dataProduct g.copies (coeff F g.second g.secondW)) G
  wideGap : Y.wide.Gap (coeff F g.wide g.wideW) G

theorem PassFormat.Calls.Paid.gaps {Y : g.Calls F k} {L W G : ℝ} (p : Y.Paid L W G) :
    ∀ o ∈ Y.occurrences, o.replacement.Gap o.target G := by
  intro o ho
  rcases List.mem_cons.mp ho with rfl|ho
  · exact p.firstGap
  rcases List.mem_cons.mp ho with rfl|ho
  · exact p.secondGap
  rcases List.mem_singleton.mp ho with rfl
  exact p.wideGap

theorem PassFormat.Calls.Paid.total {Y : g.Calls F k} {L W G : ℝ} (p : Y.Paid L W G) :
    (((Y.occurrences.map (·.replacement.size)).sum:ℕ):ℝ) ≤ 2*L+W := by
  simp only [PassFormat.Calls.occurrences,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Nat.cast_add]
  linarith only [p.firstCost,p.secondCost,p.wideCost]

end Hierarchy.Tagged.Radix

end
end OAI
