import OAI.Hierarchy.ProtocolRAMCalendarInstalled

namespace OAI
/-! # Whole-mesh resource bounds for the installed procedure -/

namespace Hierarchy.ProtocolRAM.Calendar
open ProbeStage ProbeStage.Native PurchaseStage
open scoped Classical
noncomputable section
variable {z d k letters goods : ℕ}

section
variable (mesh : Mesh) (finish : ℝ) (price : PhasePrice)
    (layout : Attempt→Format z d k letters goods) (feeds : Boundary→List CommodityColumn)

local notation "C" => installed mesh finish price layout feeds
local notation "W" => wordBits z d copies

def slotFactor (r : ℕ) : Event→ℕ
  | .feed b => 4+((feedPasses C b).map (passFactor r)).sum
  | .attempt a =>
    let p := layout a
    let v := p.atTime mesh finish price a
    let s := StockCommit.fresh p.area p.stockSource
    let B := repair C a
    attemptFactor v s B r (guard C a)+(4+18*r)

def withinExtents (r : ℕ) : Event→Prop
  | .feed b => ∀p∈feedPasses C b,p.rows≤2^z*r
  | .attempt a =>
    let p := layout a
    let v := p.atTime mesh finish price a
    Extents v (StockCommit.fresh p.area p.stockSource) (repair C a) r

theorem installed_slot_bill (r : ℕ) (pos : 0<r) (evt : Event)
    (h : withinExtents mesh finish price layout feeds r evt) :
    ticks C evt≤2^z*slotFactor mesh finish price layout feeds r evt := by
  cases evt with
  | feed b => exact columns_bill (Nat.two_pow_pos z) _ h
  | attempt a =>
    let p := layout a
    let v := p.atTime mesh finish price a
    let s := StockCommit.fresh p.area p.stockSource
    let B := repair C a
    have guardRows : (guard C a).rows≤2^z*r := Nat.mul_pos (Nat.two_pow_pos _) pos
    have main := attempt_bill v s B r (guard C a) h guardRows
    have g := Nat.mul_le_mul_left 18 h.commodities
    change 18*p.area.goods≤18*(2^z*r) at g
    rw [show 18*(2^z*r)=2^z*(18*r) by ring] at g
    have small : 4≤2^z*4 := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    change (guard C a).clock+(v.prefix.ticks+(postTicks v.layout B+
      (StockCommit.freshSegment p.area p.stockSource W (enabledBatch v.layout B)).ticks))≤_
    rw [StockCommit.freshSegment_ticks]
    change (guard C a).clock+(v.prefix.ticks+(postTicks v.layout B+
      (4+18*p.area.goods+(s.native W v.rows (enabledBatch v.layout B)).ticks))) ≤
      2^z*(attemptFactor v s B r (guard C a)+(4+18*r))
    rw [Nat.mul_add,Nat.mul_add]
    omega

theorem installed_clock (r : ℕ) (pos : 0<r)
    (dimensions : ∀e∈events mesh,withinExtents mesh finish price layout feeds r e) :
    cost C (events mesh)≤4+2^z*((events mesh).map (slotFactor mesh finish price layout feeds r)).sum := by
  have summ (es : List Event) (h : ∀e∈es,withinExtents mesh finish price layout feeds r e) :
      (es.map (ticks C)).sum≤2^z*(es.map (slotFactor mesh finish price layout feeds r)).sum := by
    induction es with
    | nil => simp
    | cons e es ih =>
      simp only [List.map_cons,List.sum_cons,Nat.mul_add]
      exact Nat.add_le_add (installed_slot_bill mesh finish price layout feeds r pos e (h e (by simp)))
        (ih (fun x hx=>h x (by simp [hx])))
  simpa [cost,Nat.add_comm 4] using Nat.add_le_add_right (summ _ dimensions) 4

def slotText : Event→ℕ
  | .feed b => listText (feedPasses C b)
  | .attempt a =>
    let p := layout a
    let v := p.atTime mesh finish price a
    let B := repair C a
    rowText (guard C a).term + (rowText v.failures.test + PurchaseFrozen.Shelf.hardware d v.sampler.degree v.depth k)
      +postText v.layout B+39+commitText (StockCommit.fresh p.area p.stockSource) v.rows (enabledBatch v.layout B)

theorem installed_slot_text (evt : Event) : eventText C evt≤ slotText mesh finish price layout feeds evt := by
  cases evt with
  | feed b => exact le_rfl
  | attempt a =>
    let p := layout a
    let v := p.atTime mesh finish price a
    let B := repair C a
    let b := enabledBatch v.layout B
    obtain ⟨labels,regs,slots⟩ := StockCommit.freshSegment_size p.area p.stockSource W b
    have extra : text (StockCommit.freshSegment p.area p.stockSource W b).native=
        39+text ((StockCommit.fresh p.area p.stockSource).native W v.rows b).native := by
      change text (StockCommit.freshSegment p.area p.stockSource W b).native =
        39+text ((StockCommit.fresh p.area p.stockSource).native W p.area.rows b).native
      simp only [text,labels,regs,slots]
      omega
    have frozen := text_market v
    simp only [eventText,slotText]
    change rowText _+text v.prefix.native+postText v.layout B+
      text (StockCommit.freshSegment p.area p.stockSource W b).native ≤
      rowText (guard C a).term+(rowText v.failures.test+
        PurchaseFrozen.Shelf.hardware d v.sampler.degree v.depth k)+postText v.layout B+39+
        commitText (StockCommit.fresh p.area p.stockSource) v.rows b
    rw [extra,text_stock]
    omega

theorem installed_text : text (code C (events mesh))≤
    15+((events mesh).map (slotText mesh finish price layout feeds)).sum := by
  rw [text_run]
  apply Nat.add_le_add_left
  induction events mesh with
  | nil => rfl
  | cons e es ih =>
    exact Nat.add_le_add (installed_slot_text mesh finish price layout feeds e) ih

end
/-- The physical trace can use its actual word width (including an odd additive
constant) while its comparison-sort height retains a fixed additive offset. -/
def controlHeight (z d : ℕ) := z+(2*(rounds d+1)+3+rounds d*stride d copies)

theorem trace_word (z d : ℕ) :
    1≤wordBits z d copies ∧ wordBits z d copies≤2*(controlHeight z d+1) ∧
    z≤controlHeight z d := by
  rw [wordBits_linear]
  unfold controlHeight
  omega

/-- At the original height, the actual CT/controller word fits the 28-field
history verifier and its native sort record. -/
theorem trace_word_at_height {z d m : ℕ} (large : controlHeight 0 d+1≤z) (pad : z ≤ m) :
    3≤wordBits z d copies+1 ∧ wordBits z d copies+1≤4*(z+1) ∧ wordBits z d copies+1≤4*m := by
  rw [wordBits_linear]
  unfold controlHeight at large
  omega

theorem controlHeight_bill (z d : ℕ) :
    controlHeight z d+1≤(controlHeight 0 d+1)*(z+1) := by
  have bound (c : ℕ) : z+c+1 ≤ (c+1)*(z+1) := by
    calc
      z+c+1 ≤ c*z+(z+c+1) := Nat.le_add_left _ _
      _ = _ := by ring
  simpa only [controlHeight,Nat.zero_add] using
    bound (2*(rounds d+1)+3+rounds d*stride d copies)

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
