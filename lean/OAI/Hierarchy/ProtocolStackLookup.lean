import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Shared word lookup for packed stack slices

The control word is the menu column of an emitted gate triple. One lookup
combines that column with a packed payload word and writes the shared table
entry to the current output position.
-/

namespace Hierarchy.ProtocolStackLookup

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

private def source (w base stride dst : ℕ) : Term w 0 1 :=
  .load (.binary .add (.literal base) (.binary .mul (.literal stride)
    (.binary .sub (.result 0) (.literal dst))))

def lookup (w gates payload table radix dst : ℕ) : Term w 0 1 :=
  .load (.binary .add (.binary .add (.literal table)
    (.binary .mul (source w (gates+2) 3 dst) (.literal radix)))
    (source w payload 1 dst))

theorem lookup_binds (w gates payload table radix dst : ℕ) :
    (lookup w gates payload table radix dst).binds = 20 := by
  simp only [lookup,source,Term.binary,Term.load,Term.binds_letThen,Term.binds_rename,Term.literal,Term.binds]

def batch (w gates payload table radix dst n : ℕ) : Procedure w :=
  PhysicalInputPhases.writing (lookup w gates payload table radix dst) Fin.elim0 dst n

variable {w n menus radix : ℕ}

def Inputs (gates payload table : ℕ) (control : Fin n → Fin menus) (chunk : Fin n → Fin radix)
    (entry : Fin menus → Fin radix → Word w) (m : Memory w) : Prop :=
  (∀ i : Fin n, m (gates+3*i.val+2) = ((control i).val : Word w)) ∧
  (∀ i : Fin n, m (payload+i.val) = ((chunk i).val : Word w)) ∧
  ∀ (a : Fin menus) (b : Fin radix), m (table+a.val*radix+b.val) = entry a b

def outputWord (dst : ℕ) (control : Fin n → Fin menus) (chunk : Fin n → Fin radix)
    (entry : Fin menus → Fin radix → Word w) (a : ℕ) : Word w :=
  if h : a-dst<n then entry (control ⟨_,h⟩) (chunk ⟨_,h⟩) else 0

private theorem source_eval (base stride dst : ℕ) (m : Memory w) (a : Word w)
    (lo : dst ≤ a.val) (fit : base+stride*(a.val-dst)<2^w) :
    (source w base stride dst).eval Fin.elim0 m (fun _=>a) = m (base+stride*(a.val-dst)) := by
  have hd : dst<2^w := lo.trans_lt a.isLt
  have sub : a - (dst : Word w) = ((a.val-dst : ℕ) : Word w) := by
    apply Fin.ext
    rw [Fin.sub_val_of_le (by change (dst : Word w).val≤_; rwa [Fin.val_cast_of_lt hd]),
        Fin.val_cast_of_lt hd, Fin.val_cast_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) a.isLt)]
  simp only [source,Term.eval_load,Term.eval_binary,Term.eval_literal,Term.eval,BinaryOp.eval]
  rw [sub, ←Nat.cast_mul, ←Nat.cast_add, Fin.val_cast_of_lt fit]

theorem batch_spec (gates payload table dst : ℕ)
    (control : Fin n → Fin menus) (chunk : Fin n → Fin radix)
    (entry : Fin menus → Fin radix → Word w)
    (gateSpace : gates+3*n≤dst) (payloadSpace : payload+n≤dst)
    (tableSpace : table+menus*radix≤dst) (stop : dst+n<2^w) :
    (batch w gates payload table radix dst n).Spec (Inputs gates payload table control chunk entry)
      (fun m o => o=fillSegment dst n (outputWord dst control chunk entry) m) (4+44*n) := by
  have cost : 4+n*(2*(lookup w gates payload table radix dst).binds+4)=4+44*n := by
    rw [lookup_binds]; omega
  rw [←cost]
  apply PhysicalInputPhases.writing_spec _ _ _ _ stop
  intro input data a m lo hi frame
  let i : Fin n := ⟨a.val-dst,by omega⟩
  have step : i.val=a.val-dst := rfl
  have gi : gates+2+3*i.val<dst := by have := i.isLt; omega
  have pi : payload+i.val<dst := by have := i.isLt; omega
  have menuRead : (source w (gates+2) 3 dst).eval Fin.elim0 m (fun _=>a)=((control i).val : Word w) := by
    rw [source_eval _ _ _ _ _ lo (by omega),←step,frame _ (.inl gi)]
    simpa only [show gates+2+3*i.val=gates+3*i.val+2 by omega] using data.1 i
  have chunkRead : (source w payload 1 dst).eval Fin.elim0 m (fun _=>a)=((chunk i).val : Word w) := by
    rw [source_eval _ _ _ _ _ lo (by simpa only [one_mul,←step] using lt_trans pi (by omega : dst<2^w)),
      one_mul,←step,frame _ (.inl pi)]
    exact data.2.1 i
  have cap := Nat.mul_le_mul_right radix (control i).isLt
  rw [Nat.succ_mul] at cap
  have address : table+(control i).val*radix+(chunk i).val<dst := by have := (chunk i).isLt; omega
  simp only [lookup,Term.eval_load,Term.eval_binary,Term.eval_literal,menuRead,chunkRead,BinaryOp.eval]
  rw [←Nat.cast_mul,←Nat.cast_add,←Nat.cast_add,Fin.val_cast_of_lt (address.trans_le (by omega)),
    frame _ (.inl address),data.2.2]
  simp [outputWord,i,show a.val-dst<n from i.isLt]

theorem batch_size (w gates payload table radix dst n : ℕ) :
    (batch w gates payload table radix dst n).labels=67 ∧
    (batch w gates payload table radix dst n).registers=24 ∧
    (batch w gates payload table radix dst n).slots=0 := by
  simp [batch, PhysicalInputPhases.writing, Term.labels_eq, lookup_binds]

end Hierarchy.ProtocolStackLookup

end OAI
