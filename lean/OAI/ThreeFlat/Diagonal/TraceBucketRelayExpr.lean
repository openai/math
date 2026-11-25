import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Fixed native code for the four metadata words of an initial relay row -/

namespace ThreeFlat.Diagonal.TraceBucketRelay

open RAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

/-- Bit of the zero, singleton, or low-mask displacement at heap position `q`. -/
def chooseSlot (d o q : ℕ) : ℕ :=
  if o=0 then 0 else if o<d+1 then if o=q+1 then 1 else 0 else if q<o-d then 1 else 0

def slotFormula {n : ℕ} (d o q : Formula n) : Formula n :=
  eqz o (L 0) (L 0) (lt o (add d (L 1)) (eqz o (add q (L 1)) (L 1) (L 0))
    (lt q (sub o d) (L 1) (L 0)))

theorem natural_branch {α : Sort*} (q : Prop) [Decidable q] (a b : α) :
    (if decide q = true then a else b) = (if q then a else b) := by
  by_cases h : q <;> simp [h]

private theorem slot_branches (d o q : ℕ) :
    (if decide (o=0) then 0 else if decide (o<d+1) then
      if decide (o=q+1) then 1 else 0 else if decide (q<o-d) then 1 else 0) = chooseSlot d o q := by
  by_cases z : o=0
  · simp [z,chooseSlot]
  · by_cases h : o<d+1
    · by_cases e : o=q+1 <;> simp [chooseSlot,z,h,e]
    · by_cases e : q<o-d <;> simp [chooseSlot,z,h,e]

theorem slot_natural {w n : ℕ} (d o q : Formula n) (data : Param → ℕ) (m : ℕ → ℕ) (v : Fin n → ℕ) :
    (slotFormula d o q).natural w data m v =
      chooseSlot (d.natural w data m v) (o.natural w data m v) (q.natural w data m v) := by
  exact slot_branches _ _ _

theorem slot_le (d o q : ℕ) : chooseSlot d o q ≤ 1 := by unfold chooseSlot; split_ifs <;> decide

/-- Arguments are the row, field, arc count, tag count, tags per offset,
row bit count, low bit count, current cursor position, preceding pin count,
and the tag of the equality scalar. -/
def arguments (arcs tags perOffset d low stage extra equality row field : ℕ) : Fin 10 → ℕ :=
  ![row,field,arcs,tags,perOffset,d,low,stage,extra,equality]

def values (v : Fin 10 → ℕ) : ℕ :=
  let row := v 0
  let col := v 1
  let bank := v 2*v 3
  let tag := row%v 3
  let offset := tag/v 4
  let cur := chooseSlot (v 5) offset (v 6+v 7)
  let prev := chooseSlot (v 5) offset (v 6+(v 7-1))
  let base := 2+v 8
  let out := base+(tag+v 3*cur)
  if col=3 then v 9 else if col=2 then 0 else if row<bank then
    if col=0 then base+row else if row/v 3=cur then base+row else 0
  else if col=0 then out else if v 7=0 then out else base+(bank+(tag+v 3*prev))

def formula : Formula 10 :=
  let row : Formula 10 := .reg 0
  let col : Formula 10 := .reg 1
  let tags : Formula 10 := .reg 3
  let bank := mul (.reg 2) tags
  let tag := rem row tags
  let off := div tag (.reg 4)
  let cur := slotFormula (.reg 5) off (add (.reg 6) (.reg 7))
  let prev := slotFormula (.reg 5) off (add (.reg 6) (sub (.reg 7) (L 1)))
  let base := add (L 2) (.reg 8)
  let out := add base (add tag (mul tags cur))
  eqz col (L 3) (.reg 9) (eqz col (L 2) (L 0) (lt row bank
    (eqz col (L 0) (add base row) (eqz (div row tags) cur (add base row) (L 0)))
    (eqz col (L 0) out (eqz (.reg 7) (L 0) out (add base (add bank (add tag (mul tags prev))))))))

theorem formula_natural (w : ℕ) (data : Param → ℕ) (m : ℕ → ℕ) (v : Fin 10 → ℕ) :
    formula.natural w data m v = values v := by
  simp only [formula,values,slot_natural,Formula.natural,natTest,natOp,natural_branch]; split_ifs <;> simp_all []

def program (w K : ℕ) (p : Param → Fin K) : Term w K 10 := formula.compile p

theorem program_binds {w K : ℕ} (p : Param → Fin K) : (program w K p).binds = formula.work :=
  Formula.binds_compile _ _

theorem program_work : formula.work = 168 := by decide

theorem program_binds_eq {w K : ℕ} (p : Param → Fin K) : (program w K p).binds = 168 :=
  (program_binds p).trans program_work

end ThreeFlat.Diagonal.TraceBucketRelay

end OAI
