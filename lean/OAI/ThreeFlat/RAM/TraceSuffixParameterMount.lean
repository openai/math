import OAI.ThreeFlat.RAM.TraceSuffixMount

namespace OAI
/-! # A table slice within the evaluator's own fixed tick parameter pins -/

namespace ThreeFlat.RAM.TraceSuffixOracle

open Computability.VPVNP.BurstRAM PhysicalPrelude Diagonal.ApproximateImage
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [Field F] {W w nt ns n : ℕ} (I : Image F w)

def withTable (offset : ℕ) (initial : Fin I.parameters → Bool) (i : Fin I.parameters) :=
  if h : offset≤ i.val ∧ i.val-offset<w*FixedTraceImage.count I.G then
    FixedTraceImage.parameter I.G I.field I.keys ⟨_,h.2⟩ else initial i

theorem withTable_at (offset : ℕ) (initial : Fin I.parameters → Bool)
    (fits : offset+w*FixedTraceImage.count I.G≤I.parameters) (i : Fin (w*FixedTraceImage.count I.G)) :
    withTable I offset initial ⟨offset+i.val,by have := i.isLt;omega⟩ =
      FixedTraceImage.parameter I.G I.field I.keys i := by simp [withTable,i.isLt]

theorem withTable_outside (offset : ℕ) (initial : Fin I.parameters → Bool)
    (i : Fin I.parameters) (outside : i.val<offset ∨ offset+w*FixedTraceImage.count I.G≤ i.val) :
    withTable I offset initial i = initial i := by
  simp [withTable,show ¬(offset≤ i.val ∧ i.val-offset<w*FixedTraceImage.count I.G) by omega]

/-- The actual H parameters occupy the single original parameter bank.
Storing the fixed metadata there does not require a second copy of those parameters. -/
theorem table_mount (D : Fin I.advice → Bool) (team : Fin nt → Bool) (step : Fin ns → Bool)
    (initial : Fin I.parameters → Bool) (oa na oc nc : Fin n → Bool)
    (offset codeBase textStart textLength : ℕ) (hW : 0<W)
    (fits : offset+w*FixedTraceImage.count I.G≤I.parameters) :
    let par := withTable I offset initial
    let pins := fields D team step par oa na oc nc
    let base := 2+I.advice+nt+ns
    Mounted I ⟨2,base,base+offset,codeBase,textStart,textLength⟩
      (fun j => (TickMountedPins.memory (w:=W) pins j).val) D par := by
  dsimp only
  simpa only [Nat.add_zero] using mounted_tick I D team step (withTable I offset initial) oa na oc nc
    (withTable I offset initial) 0 offset codeBase textStart textLength hW (by omega) fits
    (fun i => by simp) (withTable_at I offset initial fits)
    (TickMountedPins.memory (fields D team step (withTable I offset initial) oa na oc nc))
    (TickMountedPins.memory_at _)


end ThreeFlat.RAM.TraceSuffixOracle

end OAI
