import OAI.Hierarchy.DescentGLPermutationRAM
import OAI.Hierarchy.DescentGLRowRAM

namespace OAI
/-! # Extending the physical span bitmap after one selected row -/

namespace Hierarchy.DescentGL.SpanRAM

open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing

noncomputable section
variable {w k h : ℕ}

def bitmap (base : ℕ) (rows : Fin h→Row k) (m : Memory w) : Prop :=
  ∀ i : Fin (2^k), m (base+i.val) =
    if (rowIndex k).symm i ∈ Submodule.span (ZMod 2) (Set.range rows) then 1 else 0

/-- This public sum table is independent of the chosen rows and the input instance.
Both operands are actual physical row indices in the canonical binary directory. -/
def shifted (x r : Fin (2^k)) : Fin (2^k) :=
  rowIndex k ((rowIndex k).symm x+(rowIndex k).symm r)

def nextIndex (k ptr : ℕ) : Expr :=
  chooseField (2^k) 0 (fun r=>chooseField (2^k) 0
    (fun x=>.lit (shifted x r).val) .row) (.lookup ⟨ptr,0⟩ (.lit 0))

def next (k base ptr : ℕ) : Expr :=
  let b : Bank := ⟨base,k⟩
  .branch .eq (.lookup b .row) (.lit 0) (.lookup b (nextIndex k ptr)) (.lit 1)

def zero (k : ℕ) : Expr := .branch .eq .row (.lit (rowIndex k 0).val) (.lit 1) (.lit 0)

private theorem snoc_span (rows : Fin h→Row k) (x a : Row k) :
    x∈Submodule.span (ZMod 2) (Set.range (Fin.snoc rows a)) ↔
      x∈Submodule.span (ZMod 2) (Set.range rows) ∨ x+a∈Submodule.span (ZMod 2) (Set.range rows) := by
  rw [Fin.range_snoc,Submodule.mem_span_insert']
  constructor
  · rintro ⟨b,hb⟩
    have two : ∀ t : ZMod 2,t=0 ∨ t=1 := by decide
    rcases two b with rfl|rfl
    · left; simpa using hb
    · right; simpa using hb
  · rintro (ha|ha)
    · exact ⟨0,by simpa using ha⟩
    · exact ⟨1,by simpa using ha⟩

theorem zero_bitmap (base : ℕ) (m : Memory w) (room : 2^k≤2^w) :
    bitmap base (Fin.elim0 : Fin 0→Row k) (ProtocolRAM.image base (2^k) (zero k) m) := by
  intro i
  rw [ProtocolRAMGeneratedWrite.read_image]
  have compare : (i.val:Word w)=((rowIndex k 0).val:Word w) ↔ (rowIndex k).symm i=0 := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt (i.isLt.trans_le room),
      Fin.val_cast_of_lt ((rowIndex k 0).isLt.trans_le room),←Fin.ext_iff]
    constructor
    · rintro rfl; exact (rowIndex k).symm_apply_apply _
    · intro h; rw [←h,Equiv.apply_symm_apply]
  simp [zero,Expr.eval,Comparison.test,compare]

theorem zero_exec (base : ℕ) (m : Memory w) (room : base+2^k<2^w) :
    (scan w base (2^k) (zero k)).Exec m (ProtocolRAM.image base (2^k) (zero k) m) (4+2^k*16) := by
  exact scan_exec base (2^k) (zero k) m ⟨trivial,trivial,trivial,trivial⟩ room

private theorem nextIndex_eval (m : Memory w) (ptr : ℕ) (i j : Fin (2^k))
    (actual : m ptr=(j.val:Word w)) (room : 2^k≤2^w) :
    (nextIndex k ptr).eval m (i.val:Word w) = ((shifted i j).val:Word w) := by
  have read : ((Expr.lookup ⟨ptr,0⟩ (.lit 0)).eval m (i.val:Word w)).val=0+j.val := by
    change (m (ptr+((0:Word w).val%2^0))).val=_
    simp [actual,Fin.val_cast_of_lt (j.isLt.trans_le room)]
  unfold nextIndex
  rw [eval_chooseField _ _ _ _ _ _ j (by omega) read]
  rw [eval_chooseField _ _ _ _ _ _ i (by omega) (by
    change (i.val:Word w).val=0+i.val
    simp [Fin.val_cast_of_lt (i.isLt.trans_le room)])]
  rfl

private theorem bank_read (base : ℕ) (m : Memory w) (i : Fin (2^k)) (room : 2^k≤2^w) :
    (Bank.mk base k).read m (i.val:Word w) = m (base+i.val) := by
  simp [Bank.read,Bank.size,Fin.val_cast_of_lt (i.isLt.trans_le room),Nat.mod_eq_of_lt i.isLt]

theorem extend (base ptr out : ℕ) (m : Memory w) (rows : Fin h→Row k) (a : Row k)
    (old : bitmap base rows m) (stored : m ptr=((rowIndex k a).val:Word w))
    (room : 2^k≤2^w) (wide : 1<2^w) :
    bitmap out (Fin.snoc rows a) (ProtocolRAM.image out (2^k) (next k base ptr) m) := by
  intro i
  rw [ProtocolRAMGeneratedWrite.read_image]
  let j := rowIndex k a
  have one : (1:Word w)≠0 := by
    intro h
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt wide] at this
  have shifted_eq : (rowIndex k).symm (shifted i j)=(rowIndex k).symm i+a := by
    simp [shifted,j]
  simp only [next,Expr.eval,nextIndex_eval m ptr i j stored room,bank_read _ _ _ room,
    old i,old (shifted i j),snoc_span,shifted_eq,Comparison.test,beq_iff_eq,Nat.cast_zero,Nat.cast_one]
  split_ifs <;> simp_all

theorem next_fits (base ptr out : ℕ) (old : (Bank.mk base k).Fits w out)
    (before : ptr<out) (wide : 1<2^w) : (next k base ptr).Fits w out := by
  refine ⟨⟨old,trivial⟩,trivial,⟨old,?_⟩,trivial⟩
  apply DescentGLPermutationRAM.fits_choose
  · exact ⟨⟨Nat.zero_lt_one,wide,Nat.succ_le_of_lt before⟩,trivial⟩
  · intro _
    exact DescentGLPermutationRAM.fits_choose _ _ _ _ trivial (fun _=>trivial)

theorem next_work (base ptr : ℕ) :
    (next k base ptr).work=16+2^k*(9+5*2^k) := by
  have index : (nextIndex k ptr).work=1+2^k*(9+5*2^k) := by
    unfold nextIndex
    rw [DescentGLPermutationRAM.work_choose _ _ _ _ (1+5*2^k) (fun r=>by
      rw [DescentGLPermutationRAM.work_choose _ _ _ _ 1 (fun _=>rfl)]
      simp [Expr.work,Nat.mul_comm])]
    simp [Expr.work]
   ; ring
  simp [next,Expr.work,index]
 ; ring

theorem extend_exec (base ptr out : ℕ) (m : Memory w) (old : (Bank.mk base k).Fits w out)
    (before : ptr<out) (room : out+2^k<2^w) :
    (scan w out (2^k) (next k base ptr)).Exec m (ProtocolRAM.image out (2^k) (next k base ptr) m)
      (4+2^k*(2*(16+2^k*(9+5*2^k))+4)) := by
  have wide : 1<2^w := by have := Nat.two_pow_pos k; omega
  intro P R K M pc reg pub exit installed data cfg mem entry initial
  have run := scan_exec out (2^k) (next k base ptr) m (next_fits base ptr out old before wide) room
    M pc reg pub exit installed data cfg mem entry initial
  simpa only [next_work] using run

theorem legal {base : Layout k} (hk : h<k) (addr : ℕ) (m : Memory w)
    (present : bitmap addr (fun a : Fin h=>rowFunctional base (a.castLE hk.le)) m)
    (room : 2^k≤2^w) (wide : 1<2^w) (i : Fin (2^k)) :
    ¬ RowRAM.excluded (Bank.mk addr k) m i ↔ i∈legalMenu hk base := by
  have one : (1:Word w)≠0 := by
    intro eqn
    have := congrArg Fin.val eqn
    simp [Nat.mod_eq_of_lt wide] at this
  simp only [RowRAM.excluded,not_ne_iff,bank_read addr m i room,present i,legalMenu,
    Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp_all

theorem frame (out n : ℕ) (term : Expr) (m : Memory w) (x : ℕ) (outside : x<out ∨ out+n≤x) :
    ProtocolRAM.image out n term m x=m x := by
  simp only [ProtocolRAM.image,fillSegment,ite_eq_right (show ¬(out≤x ∧ x<out+n) by omega)]

end
end Hierarchy.DescentGL.SpanRAM

end OAI
