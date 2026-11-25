import OAI.Hierarchy.ProtocolRAMHistogram
import OAI.Hierarchy.ProtocolRAMSchedule
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # A physical batch of selected local replacements -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Fin.CommRing Classical

variable {w q d : ℕ}

/-- The row code for one candidate ball in the fixed conflict class. The selected
packet is read from the price lookup. Each resource obtains its current stock at
the indexed global commodity cell. Zero denotes an inactive menu choice. -/
structure Batch (q d : ℕ) where
  copies : ℕ
  radix : ℕ
  maxWidth : ℕ
  quotes : List Expr
  menu : Bank
  termCount : Bank
  enabled : Bank
  owner : Expr
  field : Fin q → Expr
  stock : Fin d → Expr
  perCopy : Fin d → Expr

def Batch.packet (b : Batch q d) : Expr := menuLookup b.menu b.radix b.quotes

def Batch.need (b : Batch q d) (i : Fin d) := boundedMul b.maxWidth (.lit b.copies) (b.perCopy i)

def Batch.ifSelected (b : Batch q d) (yes no : Expr) : Expr :=
  .branch .eq (.lookup b.enabled b.owner) (.lit 0) no
    (.branch .eq b.packet (.lit 0) no (ifEnough d b.need b.stock yes no))

def Batch.selected (b : Batch q d) (m : Memory w) (r : Word w) : Prop :=
  b.enabled.read m (b.owner.eval m r) ≠ 0 ∧ b.packet.eval m r ≠ 0 ∧
    ∀ i, (b.need i |>.eval m r).val ≤ (b.stock i |>.eval m r).val

theorem Batch.eval_ifSelected (b : Batch q d) (m : Memory w) (r : Word w) (yes no : Expr) :
    (b.ifSelected yes no).eval m r =
      if b.selected m r then yes.eval m r else no.eval m r := by
  classical
  simp only [ifSelected,Expr.eval,Comparison.test,beq_iff_eq,Nat.cast_zero,eval_ifEnough,selected]
  split_ifs <;> simp_all

/-- The fixed-width board accommodates every finite catalogue packet. Selector lanes
past the chosen packet's actual alphabet must all be zero. -/
def Batch.ifPacket (b : Batch q d) (yes no : Expr) : Expr :=
  let alphabet := Expr.lookup b.termCount b.packet
  ifEnough q b.field (fun i =>
    .branch .lt (.lit i.val) alphabet (.lit b.copies) (.lit 0))
    (ifHistogram q b.copies b.field yes no) no

def Batch.withinPacket (b : Batch q d) (m : Memory w) (r : Word w) : Prop :=
  ∀ i, ((b.field i).eval m r).val ≤
    (if i.val < (b.termCount.read m (b.packet.eval m r)).val then b.copies else 0)

private theorem nest_conditions {α : Type*} {A B : Prop}
    {da : Decidable A} {db : Decidable B} {dc : Decidable (A ∧ B)} (x y : α) :
    @ite α A da (@ite α B db x y) y=@ite α (A ∧ B) dc x y := by
  cases da with
  | isFalse ha =>
    cases dc with
    | isFalse => rfl
    | isTrue both => exact (ha both.1).elim
  | isTrue ha =>
    cases db with
    | isFalse hb =>
      cases dc with
      | isFalse => rfl
      | isTrue both => exact (hb both.2).elim
    | isTrue hb =>
      cases dc with
      | isTrue => rfl
      | isFalse hn => exact (hn ⟨ha,hb⟩).elim

theorem Batch.eval_ifPacket (b : Batch q d) (m : Memory w) (r : Word w) (yes no : Expr)
    (qFit : q ≤ 2^w) (copiesFit : b.copies < 2^w) (sumFit : q*b.copies < 2^w) :
    (b.ifPacket yes no).eval m r =
      if b.withinPacket m r ∧ (∑ i, ((b.field i).eval m r).val) = b.copies
      then yes.eval m r else no.eval m r := by
  classical
  rw [ifPacket,eval_ifEnough,eval_ifHistogram _ _ _ _ _ _ _ copiesFit sumFit]
  have bound (i : Fin q) := i.isLt.trans_le qFit
  have branch (i : Fin q) :
      ((Expr.branch .lt (.lit i.val) (.lookup b.termCount b.packet) (.lit b.copies) (.lit 0)).eval m r).val =
      (if i.val < (b.termCount.read m (b.packet.eval m r)).val then b.copies else 0) := by
    simp only [Expr.eval,Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt (bound i)]
    split <;> simp_all [Fin.val_cast_of_lt copiesFit]
  simp only [branch,withinPacket]
  exact nest_conditions _ _

def Batch.ifAdmitted (b : Batch q d) (yes no : Expr) : Expr :=
  b.ifSelected (b.ifPacket yes no) (ifHistogram q 0 b.field yes no)

theorem Batch.eval_ifAdmitted (b : Batch q d) (m : Memory w) (r : Word w) (yes no : Expr)
    (qFit : q ≤ 2^w) (copiesFit : b.copies < 2^w) (sumFit : q*b.copies < 2^w) :
    (b.ifAdmitted yes no).eval m r =
      if (if b.selected m r then b.withinPacket m r ∧ (∑ i, ((b.field i).eval m r).val) = b.copies
          else ∀ i, (b.field i).eval m r = 0)
      then yes.eval m r else no.eval m r := by
  classical
  rw [ifAdmitted,eval_ifSelected]
  by_cases select : b.selected m r
  · simp only [ite_eq_left select,eval_ifPacket _ _ _ _ _ qFit copiesFit sumFit]
  · simp only [ite_eq_right select,unused_fields]

/-- The controller emits zero width on an unselected or malformed candidate. -/
def Batch.wire (b : Batch q d) (tab : Fin q → Expr) : Expr :=
  b.ifSelected (b.ifPacket (installed q b.maxWidth b.field tab) (.lit 0)) (.lit 0)

theorem Batch.wire_selected {E : Type*} (b : Batch q d) (m : Memory w) (r : Word w)
    (e : E) (tab : Fin q → Expr) (counts : Fin q → E → ℕ)
    (h : Histogram (Fin q) b.copies) (active : b.selected m r)
    (alphabet : b.withinPacket m r) (qFit : q ≤ 2^w) (copiesFit : b.copies < 2^w) (sumFit : q*b.copies < 2^w)
    (fields : ∀ i, ((b.field i).eval m r).val = (h.val i).val)
    (terms : ∀ i, (tab i).eval m r = (counts i e : Word w))
    (maxBound : ∀ i, counts i e ≤ b.maxWidth) (fits : b.maxWidth < 2^w) :
    (b.wire tab).eval m r = (histWidth counts h e : Word w) := by
  rw [wire,eval_ifSelected,ite_eq_left active,eval_ifPacket _ _ _ _ _ qFit copiesFit sumFit]
  have code : (∑ i, ((b.field i).eval m r).val) = b.copies := by simpa only [fields] using h.2
  rw [ite_eq_left (And.intro alphabet code)]
  exact installed_histWidth m r e b.maxWidth b.field tab counts h (fun i => by rw [← fields]; simp) terms maxBound fits

theorem Batch.wire_skipped (b : Batch q d) (m : Memory w) (r : Word w) (tab : Fin q → Expr)
    (skip : ¬ b.selected m r) : (b.wire tab).eval m r = 0 := by
  simp [wire,eval_ifSelected,skip,Expr.eval]

/-- Every actual physical link width fits the fixed per-row capacity, even for
arbitrary untrusted selectors and table data. A wrong histogram emits zero. -/
theorem Batch.wire_bound (b : Batch q d) (m : Memory w) (r : Word w) (tab : Fin q → Expr)
    (qFit : q≤2^w) (copiesFit : b.copies<2^w) (sumFit : q*b.copies<2^w) :
    ((b.wire tab).eval m r).val ≤ b.maxWidth*b.copies := by
  rw [wire,eval_ifSelected]
  by_cases sel : b.selected m r
  · rw [ite_eq_left sel,eval_ifPacket _ _ _ _ _ qFit copiesFit sumFit]
    split
    · rename_i h
      simpa only [h.2] using installed_le m r q b.maxWidth b.field tab
    · exact Nat.zero_le _
  · rw [ite_eq_right sel]
    exact Nat.zero_le _

/-- Named columns published for one row per fixed link occurrence. The ordinal link ID
is retained at both ends, even when the next occurrence has the same pair of sites. -/
structure Link where
  group : Expr
  endpoint : Expr
  opposite : Expr
  idBase : ℕ
  lengthCode : Expr

def Link.fields (link : Link) (b : Batch q d) (widthTable : Fin q → Expr) : Fin 7 → Expr :=
  ![link.group,link.endpoint,link.opposite,.op .add (.lit link.idBase) .row,
    b.wire widthTable,link.lengthCode,b.ifSelected (b.ifPacket b.packet (.lit 0)) (.lit 0)]

/-- A separate pass reads the same indexed banks when updating the outstanding stocks.
Rejected and stock-deficient replacements leave the complete previous value intact. -/
def Batch.nextStock (b : Batch q d) (i : Fin d) (credit : Expr) : Expr :=
  b.ifSelected (b.ifPacket
    (.op .add (.op .sub (b.stock i) (b.need i)) credit) (b.stock i)) (b.stock i)

theorem Batch.need_bits (b : Batch q d) (m : Memory w) (r : Word w) (i : Fin d)
    (coefficient : ((b.perCopy i).eval m r).val ≤ b.maxWidth) (cap : b.maxWidth<2^w)
    (product : b.copies*((b.perCopy i).eval m r).val < 2^w) :
    (b.need i |>.eval m r).val = b.copies*((b.perCopy i).eval m r).val := by
  rw [need,eval_boundedMul _ _ _ _ _ coefficient cap,Expr.eval]
  rw [← Fin.cast_val_eq_self ((b.perCopy i).eval m r),←Nat.cast_mul,Fin.val_cast_of_lt product]
  simp

theorem Batch.nextStock_selected (b : Batch q d) (m : Memory w) (r : Word w) (i : Fin d)
    (credit : Expr) (selected : b.selected m r) (alphabet : b.withinPacket m r)
    (hist : (∑ j, ((b.field j).eval m r).val)=b.copies) (qFit : q≤2^w)
    (copiesFit : b.copies<2^w) (sumFit : q*b.copies < 2^w)
    (limit : ((b.stock i).eval m r).val-((b.need i).eval m r).val+(credit.eval m r).val < 2^w) :
    (b.nextStock i credit |>.eval m r).val =
      ((b.stock i).eval m r).val-((b.need i).eval m r).val+(credit.eval m r).val := by
  rw [nextStock,eval_ifSelected,ite_eq_left selected,eval_ifPacket _ _ _ _ _ qFit copiesFit sumFit,
    ite_eq_left (And.intro alphabet hist)]
  simp only [Expr.eval,RowOp.opcode,BinaryOp.eval]
  have eqn : (↑(((b.stock i).eval m r).val - ((b.need i).eval m r).val + (credit.eval m r).val) : Word w) =
      (b.stock i).eval m r - (b.need i).eval m r + credit.eval m r := by
    simp [Nat.cast_sub (R:=Word w) (selected.2.2 i)]
  rw [←eqn,Fin.val_cast_of_lt limit]

end Hierarchy.ProtocolRAM

end OAI
