import OAI.Computability.BorderVNP.CubeISALengthScan

/-! # Reading every public column sum without modular overflow

A checked column starts with the supplied total as its residual. Each row
deducts its actual declared word, rejecting an underflow before subtraction.
At the end the residual must be zero. This checks even adversarial declarations
whose mathematical column sums exceed the representable word range.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeLengths

open VPVNP.BurstRAM Finset

/-- Load the declared-row base and derive the number of rows from the table shape. -/
def columnSetup : Code := .block [field 58 1, field 59 2, field 57 4,
  .binary .div 59 59 57, .constant 56 0]

/-- Initialize the current row and read the claimed total for this column. -/
def columnStart : Code := .block [field 62 3, .binary .add 62 62 56, .load 61 62,
  .constant 60 0, .constant 63 1]

/-- Deduct a row word from the residual only after checking underflow. -/
def debit : Code := .ifLt 61 62 (.seq (.constant 61 0) .reject) (.binary .sub 61 61 62)

/-- Load a row-major entry and decrement the residual. -/
def columnEntry : Code := .block [.binary .mul 62 60 57, .binary .add 62 62 56,
  .binary .add 62 58 62, .load 62 62, debit, .binary .add 60 60 63]

/-- Require the final residual to vanish, then proceed to the next column. -/
def columnEnd : Code := .block [.constant 62 0, requireEq 61 62, .binary .add 56 56 63]

/-- Check one column from the public declaration. -/
def columnBody : Code := .seq columnStart (.seq (.whileLt 60 59 columnEntry) columnEnd)

/-- Check the public totals against all the declared row entries. -/
def columns : Code := .seq columnSetup (.whileLt 56 57 columnBody)

/-- Sum of the first rows in one column of a physical row-major array. -/
def columnPrefix (l : Layout) (mem : ℕ → ℕ) (j k : ℕ) : ℕ :=
  ∑ r ∈ range k, mem (l.claimed + (r*l.coordinates+j))

/-- Each supplied total is the ordinary natural sum of the declared column. -/
def ColumnsAgree (l : Layout) (mem : ℕ → ℕ) (R : ℕ) : Prop :=
  ∀ j < l.coordinates, mem (l.totals+j) = columnPrefix l mem j R

/-- Register values retained while checking successive columns. -/
structure ColumnState (regs : Reg → ℕ) (mem : ℕ → ℕ) (l : Layout) (R j : ℕ) (z : NatState) : Prop where
  /-- Input memory and caller registers survive. -/
  kept : Kept regs mem z
  /-- Column counter. -/
  column : z.reg 56 = j
  /-- Number of columns. -/
  dim : z.reg 57 = l.coordinates
  /-- Beginning of the declared row array. -/
  base : z.reg 58 = l.claimed
  /-- Number of rows. -/
  rows : z.reg 59 = R

private structure Residual (regs : Reg → ℕ) (mem : ℕ → ℕ) (l : Layout) (R j k : ℕ) (z : NatState) : Prop where
  state : ColumnState regs mem l R j z
  row : z.reg 60 = k
  remaining : z.reg 61 = mem (l.totals+j) - columnPrefix l mem j k
  one : z.reg 63 = 1

private theorem debit_eval (p : Arg → ℕ) (mem : ℕ → ℕ) (reg : Reg → ℕ) :
    debit.evalNat p mem reg = Function.update reg 61 (reg 61-reg 62) := by
  by_cases h : reg 61 < reg 62
  · simp [debit,Code.evalNat,h,Nat.sub_eq_zero_of_le h.le]
  · simp [debit,Code.evalNat,addressOp,h]

private theorem debit_safe {w : ℕ} (p : Arg → ℕ) (mem : ℕ → ℕ) (reg : Reg → ℕ) :
    debit.safeReadOnly w p mem reg ↔ reg 62 ≤ reg 61 := by
  by_cases h : reg 61 < reg 62 <;> simp [debit,Code.safeReadOnly,addressOpFits,h]

private theorem debit_fit {w : ℕ} (p : Arg → ℕ) (mem : ℕ → ℕ) (reg : Reg → ℕ) :
    debit.relaxReject.safeReadOnly w p mem reg := by
  by_cases h : reg 61 < reg 62 <;> simp [debit,Code.relaxReject,Code.safeReadOnly,addressOpFits,h]
  omega

private theorem columnPrefix_succ (l : Layout) (mem : ℕ → ℕ) (j k : ℕ) :
    columnPrefix l mem j (k+1) = columnPrefix l mem j k + mem (l.claimed+(k*l.coordinates+j)) :=
  sum_range_succ ..

private theorem residual_exact (l : Layout) (mem : ℕ → ℕ) (j R : ℕ) :
    ((∀ k < R, mem (l.claimed+(k*l.coordinates+j)) ≤ mem (l.totals+j)-columnPrefix l mem j k) ∧
     mem (l.totals+j)-columnPrefix l mem j R = 0) ↔
    mem (l.totals+j) = columnPrefix l mem j R := by
  have mono {k r : ℕ} (h : k ≤ r) : columnPrefix l mem j k ≤ columnPrefix l mem j r :=
    Finset.sum_le_sum_of_subset (range_mono h)
  constructor
  · rintro ⟨ok,zero⟩
    have bound (k : ℕ) (hk : k ≤ R) : columnPrefix l mem j k ≤ mem (l.totals+j) := by
      induction k with
      | zero => simp [columnPrefix]
      | succ k ih =>
        have b := ih (by omega)
        have e := ok k (by omega)
        rw [columnPrefix_succ]
        omega
    have := bound R le_rfl
    omega
  · intro eq
    refine ⟨fun k hk => ?_, by omega⟩
    have b := mono (show k+1 ≤ R from hk)
    rw [columnPrefix_succ] at b
    omega

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem column_entry_test (regs : Reg → ℕ) (mem : ℕ → ℕ) (l : Layout) (R j k : ℕ)
    (t : Bank w) (mt : Memory w) (hs : Residual regs mem l R j k (.ofWords t mt))
    (hj : j < l.coordinates) (hk : k < R) (area : l.claimed+R*l.coordinates ≤ 2^w) :
    TestRun pub mac columnEntry t mt columnEntry.slots
      (mem (l.claimed+(k*l.coordinates+j)) ≤ mem (l.totals+j)-columnPrefix l mem j k)
      (Residual regs mem l R j (k+1)) := by
  have indexLt : k*l.coordinates+j < R*l.coordinates := by
    calc _ < (k+1)*l.coordinates := by rw [Nat.add_mul]; omega
         _ ≤ _ := Nat.mul_le_mul_right _ hk
  have ptr : l.claimed+(k*l.coordinates+j) < 2^w := by omega
  have key : k*l.coordinates+j < 2^w := by omega
  have mul : k*l.coordinates < 2^w := by omega
  have h56 : readings t 56 = j := hs.state.column
  have h57 : readings t 57 = l.coordinates := hs.state.dim
  have h58 : readings t 58 = l.claimed := hs.state.base
  have h59 : readings t 59 = R := hs.state.rows
  have h60 : readings t 60 = k := hs.row
  have h61 : readings t 61 = mem (l.totals+j)-columnPrefix l mem j k := hs.remaining
  have h63 : readings t 63 = 1 := hs.one
  have hm : readings mt = mem := hs.state.kept.1
  have inc : k+1 < 2^w := lt_of_le_of_lt hk (by rw [← h59]; exact (t 59).isLt)
  apply readTest _ t mt _ _ (by decide)
  · change (Code.block [.binary .mul 62 60 57, .binary .add 62 62 56, .binary .add 62 58 62,
      .load 62 62, debit.relaxReject, .binary .add 60 60 63]).safeReadOnly _ _ _ _
    simp (config := {decide := true}) [Code.block,Code.safeReadOnly,Code.evalNat_relaxReject,debit_fit,
      debit_eval,Code.evalNat,addressOp,addressOpFits,h56,h57,h58,h60,h63,ptr,key,mul,inc]
  · simp (config := {decide := true}) [columnEntry,Code.block,Code.safeReadOnly,debit_safe,debit_eval,
      Code.evalNat,addressOp,addressOpFits,h56,h57,h58,h60,h61,h63,hm,ptr,key,mul,inc]
  · refine ⟨⟨keptEval _ _ (by decide) hs.state.kept,?_,?_,?_,?_⟩,?_,?_,?_⟩ <;>
      simp (config := {decide := true}) [columnEntry,Code.block,debit_eval,Code.evalNat,addressOp,
        h56,h57,h58,h59,h60,h61,h63,hm,columnPrefix_succ,Nat.sub_sub]

/-- Physical ticks allowed for the setup, entry loop and final comparison of one column. -/
def columnCost (R : ℕ) := columnStart.slots + (R*(columnEntry.slots+1)+1) + columnEnd.slots

private theorem column_test (regs : Reg → ℕ) (mem : ℕ → ℕ) (l : Layout) (R j : ℕ)
    (t : Bank w) (mt : Memory w) (hs : ColumnState regs mem l R j (.ofWords t mt))
    (hf : Fits w (readings pub) mem) (layoutEq : l = layout (readings pub) mem)
    (shape : l.entries = R*l.coordinates) (hj : j < l.coordinates) :
    TestRun pub mac columnBody t mt (columnCost R)
      (mem (l.totals+j) = columnPrefix l mem j R) (ColumnState regs mem l R (j+1)) := by
  let I := Residual regs mem l R j
  let good k := mem (l.claimed+(k*l.coordinates+j)) ≤ mem (l.totals+j)-columnPrefix l mem j k
  have hm : readings mt = mem := hs.kept.1
  have h56 : readings t 56 = j := hs.column
  have h57 : readings t 57 = l.coordinates := hs.dim
  have h58 : readings t 58 = l.claimed := hs.base
  have h59 : readings t 59 = R := hs.rows
  have fw := hf.primary
  have hw : 1 < 2^w := by omega
  have fitTotal := hf.totals
  rw [← layoutEq] at fitTotal
  have addr : l.totals+j < 2^w := by omega
  have ptr : mem (frameField (readings pub) mem 63+3) = l.totals := by rw [layoutEq]; rfl
  have read (z : Reg → ℕ) := fieldSafe 62 (3 : Word 8) (readings pub) mem z hf.primary
    (by change frameField (readings pub) mem 63+3 < 2^w; have := hf.header; omega)
  have start : TestRun pub mac columnStart t mt columnStart.slots True (I 0) := by
    apply readTest _ t mt _ _ (by decide)
    · change columnStart.safeReadOnly _ _ _ _
      simp (config := {decide := true}) [columnStart,Code.block,Code.safeReadOnly,fieldValue,
        hm,read,addressOpFits,ptr,h56,addr,hw]
    · simp (config := {decide := true}) [columnStart,Code.block,Code.safeReadOnly,fieldValue,
        hm,read,addressOpFits,ptr,h56,addr,hw]
    · refine ⟨⟨keptEval _ _ (by decide) hs.kept,?_,?_,?_,?_⟩,?_,?_,?_⟩ <;>
        simp (config := {decide := true}) [columnStart,Code.block,Code.evalNat,fieldValue,hm,ptr,addressOp,
          h56,h57,h58,h59,columnPrefix]
  have area := hf.claimed
  rw [← layoutEq,shape] at area
  have loop (u : Bank w) (mu : Memory w) (hi : I 0 (.ofWords u mu)) :
      TestRun pub mac (.whileLt 60 59 columnEntry) u mu (R*(columnEntry.slots+1)+1)
        (∀ k < R, good k) (I R) := by
    apply (test_counted_loop 60 59 columnEntry R (fun _ => columnEntry.slots) good I
      (fun _ _ hz => ⟨hz.row,hz.state.rows⟩)
      (fun k hk u mu h => column_entry_test regs mem l R j k u mu h hj hk area) 0 (Nat.zero_le _)
      u mu hi).mono (by simp) (by simp) (fun _ hz => hz)
  have finish (u : Bank w) (mu : Memory w) (hi : I R (.ofWords u mu)) :
      TestRun pub mac columnEnd u mu columnEnd.slots (mem (l.totals+j)-columnPrefix l mem j R = 0)
        (ColumnState regs mem l R (j+1)) := by
    have q56 : readings u 56 = j := hi.state.column
    have q61 : readings u 61 = mem (l.totals+j)-columnPrefix l mem j R := hi.remaining
    have q63 : readings u 63 = 1 := hi.one
    have inc : j+1 < 2^w := lt_of_le_of_lt hj (by rw [← h57]; exact (t 57).isLt)
    have ev (z : Reg → ℕ) : (requireEq 61 62).evalNat (readings pub) (readings mu) z = z := by
      simp [requireEq,Code.evalNat]
    have req (z : Reg → ℕ) :
        (requireEq 61 62).safeReadOnly w (readings pub) (readings mu) z ↔ z 61 = z 62 := by
      simp [requireEq,Code.safeReadOnly]
    have relax (z : Reg → ℕ) : (requireEq 61 62).relaxReject.safeReadOnly w (readings pub) (readings mu) z := by
      simp [requireEq,Code.relaxReject,Code.safeReadOnly]
    apply readTest _ u mu _ _ (by decide)
    · change (Code.block [.constant 62 0, (requireEq 61 62).relaxReject, .binary .add 56 56 63]).safeReadOnly _ _ _ _
      simp (config := {decide := true}) [Code.block,Code.safeReadOnly,relax,Code.evalNat_relaxReject,ev,
        Code.evalNat,addressOpFits,q56,q63,inc]
    · simp (config := {decide := true}) [columnEnd,Code.block,Code.safeReadOnly,req,ev,Code.evalNat,
        addressOpFits,q56,q61,q63,inc]
    · refine ⟨keptEval _ _ (by decide) hi.state.kept,?_,?_,?_,?_⟩ <;>
        simp (config := {decide := true}) [columnEnd,Code.block,ev,Code.evalNat,addressOp,q56,q63] <;>
          first | exact hi.state.dim | exact hi.state.base | exact hi.state.rows
  apply (start.seq fun u mu hi => (loop u mu hi).seq finish).mono
  · simp [columnCost,Nat.add_assoc]
  · simpa only [true_and] using residual_exact l mem j R
  · exact fun _ hp => hp

/-- The actual nested native loop recomputes and verifies every declared column
total. The address and shape hypotheses concern public lengths only. No fit bound
is assumed on the natural sum of adversarial row words. -/
theorem columns_run (s : Bank w) (m : Memory w) (fit : Fits w (readings pub) (readings m)) (R : ℕ)
    (shape : (layout (readings pub) (readings m)).entries = R*(layout (readings pub) (readings m)).coordinates)
    (positive : 0 < (layout (readings pub) (readings m)).coordinates) :
    let l := layout (readings pub) (readings m)
    TestRun pub mac columns s m (columnSetup.slots+l.coordinates*(columnCost R+1)+1)
      (ColumnsAgree l (readings m) R) (Kept (readings s) (readings m)) := by
  let p := readings pub
  let mem := readings m
  let l := layout p mem
  let I := ColumnState (readings s) mem l R
  let ok j := mem (l.totals+j) = columnPrefix l mem j R
  have fieldOk (d : Reg) (f : Word 8) (hf : f.val ≤ 5) (z : Reg → ℕ) :=
    fieldSafe d f p mem z fit.primary (by have := fit.header; change frameField p mem 63+5 < _ at this; omega)
  have f1 := fieldOk 58 1 (by decide)
  have f2 := fieldOk 59 2 (by decide)
  have f4 := fieldOk 57 4 (by decide)
  have p1 : mem (frameField p mem 63+1) = l.claimed := rfl
  have p2 : mem (frameField p mem 63+2) = l.entries := rfl
  have p4 : mem (frameField p mem 63+4) = l.coordinates := rfl
  have pos : 0 < l.coordinates := positive
  have div : l.entries/l.coordinates = R := by rw [shape]; exact Nat.mul_div_left _ pos
  have keep : Kept (readings s) mem (.ofWords s m) := ⟨rfl,fun _ _ => rfl⟩
  have setup : TestRun pub mac columnSetup s m columnSetup.slots True (I 0) := by
    apply readTest _ s m _ _ (by decide)
    · change columnSetup.safeReadOnly w p mem (readings s)
      simp (config := {decide := true}) [columnSetup,Code.block,Code.safeReadOnly,f1,f2,f4,fieldValue,p4,
        addressOpFits,pos]
    · change columnSetup.safeReadOnly w p mem (readings s) ↔ True
      simp (config := {decide := true}) [columnSetup,Code.block,Code.safeReadOnly,f1,f2,f4,fieldValue,p4,
        addressOpFits,pos]
    · change I 0 ⟨columnSetup.evalNat p mem (readings s), mem⟩
      refine ⟨keptEval _ _ (by decide) keep,?_,?_,?_,?_⟩ <;>
        simp (config := {decide := true}) [columnSetup,Code.block,Code.evalNat,fieldValue,p1,p2,p4,addressOp,div]
  apply (setup.seq fun t mt hi => test_counted_loop 56 57 columnBody l.coordinates (fun _ => columnCost R)
    ok I (fun _ _ h => ⟨h.column,h.dim⟩)
    (fun j hj t mt h => column_test (readings s) mem l R j t mt h fit rfl shape hj)
    0 (Nat.zero_le _) t mt hi).mono
  · simp [l,p,mem,Nat.add_assoc]
  · simp [ColumnsAgree,l,p,mem,ok]
  · exact fun _ hz => hz.kept

/-- Public global checks used independently of a team's local row comparisons. -/
def publicMinimum : Code := .seq columns minimum

/-- Both loops run on arbitrary declaration words, checking exact natural totals
and the least minimizing coordinate without trusting any supplied total. -/
theorem publicMinimum_run (s : Bank w) (m : Memory w) (fit : Fits w (readings pub) (readings m)) (R : ℕ)
    (shape : (layout (readings pub) (readings m)).entries = R*(layout (readings pub) (readings m)).coordinates)
    (positive : 0 < (layout (readings pub) (readings m)).coordinates) :
    let l := layout (readings pub) (readings m)
    TestRun pub mac publicMinimum s m
      (columnSetup.slots+l.coordinates*(columnCost R+1)+1 +
       (minSetup.slots+pivot.slots+l.coordinates*(minBody.slots+1)+2))
      (ColumnsAgree l (readings m) R ∧ Least l (readings m)) (Kept (readings s) (readings m)) := by
  apply (columns_run s m fit R shape positive).seq
  intro t mt kept
  have hm : readings mt = readings m := kept.1
  apply (minimum_run (mac := mac) t mt (hm ▸ fit)).mono (by rw [hm]) (by rw [hm]) ?_
  intro z hz
  exact ⟨hz.1.trans hm,fun j hj => (hz.2 j hj).trans (kept.2 j hj)⟩

end RoutingISA.CubeLengths

end BorderVNP
end Computability
end OAI
