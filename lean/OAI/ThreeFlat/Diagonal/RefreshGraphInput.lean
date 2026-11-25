import OAI.ThreeFlat.Diagonal.RefreshGraphWriter
import OAI.ThreeFlat.Diagonal.SlotImageViews
import OAI.ThreeFlat.Diagonal.RefreshStageNav
import OAI.ThreeFlat.RAM.HeaderPipeline

namespace OAI
/-! # Native refresh graph reads from its true packed predecessor image -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.DescriptorExpr RAM.PhysicalPinsExpr
open CompressorPacking.Native
open scoped Fin.CommRing

variable {W a t v : ℕ}

theorem closed_field (current : Word W) (off : ℕ) (pub : Fin 0 → Word W)
    (mem : Memory W) (vs : Fin 1 → Word W) :
    (closed (field current off)).eval pub mem vs=headerWord mem current off := by
  rw [eval_closed]
  simp [field,RAM.MotifRows.plus,Formula.value,headerWord,BinaryOp.eval,Fin.cast_val_eq_self]

private theorem closure (current : Word W) (src size i : ℕ) (pub : Fin 0 → Word W)
    (mem : Memory W) (vs : Fin 1 → Word W) (s n : ℕ)
    (hs : headerWord mem current src=(s:Word W)) (hn : headerWord mem current size=(n:Word W)) :
    (closed (RAM.MotifRows.plus (field current src) (.op .mul (field current size) (.lit i)))).eval pub mem vs =
      ((s+n*i:ℕ):Word W) := by
  have x := closed_field current src pub mem vs
  have y := closed_field current size pub mem vs
  rw [eval_closed] at x y ⊢
  change (Formula.value (fun _=>0) mem vs (field current src))+
    (Formula.value (fun _=>0) mem vs (field current size))*(i:Word W)=_
  rw [x,y,hs,hn,Nat.cast_add,Nat.cast_mul]

def graphOld (current : Word W) (back : Bool) : Refresh.OldColumns (Term W 0 1) :=
  ⟨closed (oldColumn current (if back then 3 else 0)),closed (oldColumn current (if back then 4 else 1)),
    closed (splitColumn current (if back then 1 else 0))⟩

private theorem memoryRead (mem : Memory W) {start i value : ℕ}
    (base : Word W) (hb : base=(start:Word W)) (bound : start+i<2^W) (h : (mem (start+i)).val=value) :
    mem (base+(i:Word W)).val=(value:Word W) := by
  rw [hb,←Nat.cast_add,Fin.val_cast_of_lt bound,←h,Fin.cast_val_eq_self]

theorem nativeGraphInput (current : Word W) (G : LiftedSlots (Fin v) (2^a) (BitWord a × BitWord t))
    (C : SlotImage.Columns) (split : ℕ) (pub : Fin 0 → Word W) (mem : Memory W) (vs : Fin 1 → Word W)
    {width : SlotImage.RefreshInput v a t → ℕ}
    (image : SlotImage.Stored G (Equiv.refl _) (SlotImage.pairLane (tagOrdinal a) (tagOrdinal t))
      C (fun i=>(mem i).val) width)
    (shifts : SlotImage.SplitColumns C split (fun i=>(mem i).val) v a)
    (src : headerWord mem current 10=(C.graph:Word W)) (row : headerWord mem current 11=(C.rows:Word W))
    (spl : headerWord mem current 12=(split:Word W)) (gCap : C.graph+6*C.rows<2^W)
    (sCap : split+3*C.rows<2^W) :
    Refresh.GraphInput G (tagOrdinal t) (graphOld current) pub mem vs where
  neighbor p back := by
    have h := image.neighbor p back
    have inside := (SlotImage.cell_range image p back 0).2.trans gCap
    cases back <;> refine memoryRead mem _ (closure current 10 11 _ pub mem vs _ _ src row) ?_ ?_
    all_goals first | exact inside | exact h
  mate p back := by
    have h := image.mate p back
    have inside := (SlotImage.cell_range image p back 1).2.trans gCap
    cases back <;> refine memoryRead mem _ (closure current 10 11 _ pub mem vs _ _ src row) ?_ ?_
    all_goals first | exact inside | exact h
  remaining p back := by
    have lt : SlotImage.ordinal (Equiv.refl _) p<C.rows := by rw [image.rowCount]; exact SlotImage.ordinal_lt _ p
    have shift (b : Bool) :
        (mem (SlotImage.cell C (Equiv.refl _) p b 2)).val/2^a =
          (tagOrdinal t (SlotImage.shift G b p).2).val := by
      rw [image.displacement p b,SlotImage.pairLane_val,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (tagOrdinal a _).isLt,Nat.zero_add]
    cases back with
    | false =>
      apply memoryRead mem _ (closure current 12 11 0 pub mem vs _ _ spl row)
      · omega
      · simpa [Refresh.step,SlotImage.shift] using (shifts.forward p).trans (shift false)
    | true =>
      apply memoryRead mem _ (closure current 12 11 1 pub mem vs _ _ spl row)
      · omega
      · simpa [Refresh.step,SlotImage.shift] using (shifts.reverse p).trans (shift true)

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
