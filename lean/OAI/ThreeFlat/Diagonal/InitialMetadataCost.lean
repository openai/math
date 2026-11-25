import OAI.ThreeFlat.Diagonal.InitialMetadataScan

namespace OAI
/-! # Exact degree-dependent instruction coefficient of the cursor directory -/
namespace ThreeFlat.Diagonal.NavigationPass.Archive
open RAM RAM.PhysicalPinsExpr CompressorPacking.Native.ShrinkStage.Halves
variable (A : Archive)
set_option maxRecDepth 4096

private theorem work_sum {I : Type*} {n : ℕ} (g : I→Formula n) (k : ℕ)
    (uniform : ∀i,(g i).work=k) (xs : List I) :
    (MotifRows.totals (xs.map g)).work=1+xs.length*(k+1) := by
  induction xs with
  | nil => simp [MotifRows.totals,Formula.work]
  | cons i xs ih =>
    change (g i).work+(MotifRows.totals (xs.map g)).work+1=1+(xs.length+1)*(k+1)
    rw [uniform,ih];ring

theorem initialKernel_work : A.initialKernel.work=128 := rfl
theorem initialHalfHeader_work : A.initialHalfHeader.work=41 := rfl

theorem initialHalf_work : A.initialHalf.work=732+548*A.initialDegree := by
  let d:=A.initialDegree
  let pos:=A.initialOffset 11
  let row:=Formula.op .div pos (.lit 4)
  let site:=Formula.op .div row (.lit (2*d))
  let h:=Formula.op .mod row (.lit (2*d))
  let slots:=Formula.op .mul (A.initialField 4) (A.initialField 5)
  let q : HalfColumns:=⟨A.initialField 6,A.initialField 0,slots,A.initialField 2⟩
  let g (i : Fin (2*d)) : Formula 1:= .select .lt (.lit i.val) h
    (half q d site (.lit i.val)).width (.lit 0)
  have cost : ∀i,(g i).work=273 := fun _=>rfl
  have prefixWord : (CompressorPacking.Native.ShrinkStage.Halves.prefix q d site h).work=1+2*d*274 := by
    change (MotifRows.totals ((List.finRange (2*d)).map g)).work=_
    simpa only [List.length_finRange] using work_sum g 273 cost (List.finRange (2*d))
  change 15+1+326+(15+1+21+(15+1+333+(CompressorPacking.Native.ShrinkStage.Halves.prefix q d site h).work+1)+1)+1=732+548*d
  rw [prefixWord];ring

/-- Native steps per site, including the full outgoing-then-incoming prefix scan. -/
def metadataCoefficient (d : ℕ) := 1472+11744*d+8768*d^2

theorem metadataUnit_eq : A.metadataUnit=metadataCoefficient A.initialDegree := by
  rw [metadataUnit,initialKernel_work,initialHalfHeader_work,initialHalf_work]
  unfold metadataCoefficient
  ring

end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
