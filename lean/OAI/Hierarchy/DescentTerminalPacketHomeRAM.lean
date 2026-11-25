import OAI.Hierarchy.ProtocolRAMCheapCode
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Expanding frozen ancestry homes into the input column of the stable cohort sort -/
namespace Hierarchy.DescentTerminalPacketHomeRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w n K H : ℕ}

structure Layout where
  index : Bank
  frozen : Bank
  dest : Bank

/-- The global frozen ordinal is a function of the public dimensions alone. -/
def calendar (E j rest kept : ℕ) (i : Fin (E*2^(j+rest))) : ℕ :=
  let row : Fin E×Fin (2^(j+rest)):=finProdFinEquiv.symm i
  row.2.val/2^(kept-j)+2^(j+(j+rest)-kept)*row.1.val

def calendarIndex (E j rest kept : ℕ) (lower : j ≤ kept) (upper : kept ≤ j+(j+rest))
    (i : Fin (E*2^(j+rest))) : Fin (E*2^(j+(j+rest)-kept)) :=
  let row : Fin E×Fin (2^(j+rest)):=finProdFinEquiv.symm i
  let frozen : Fin (2^(j+(j+rest)-kept)):=⟨row.2.val/2^(kept-j),by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [←pow_add,show j+(j+rest)-kept+(kept-j)=j+rest by omega]
    exact row.2.isLt⟩
  finProdFinEquiv (row.1,frozen)

theorem calendarIndex_val (E j rest kept : ℕ) (lower : j ≤ kept) (upper : kept ≤ j+(j+rest))
    (i : Fin (E*2^(j+rest))) :
    (calendarIndex E j rest kept lower upper i).val=calendar E j rest kept i := rfl

def field (L : Layout) : Expr:=.lookup L.frozen (.lookup L.index .row)
def program (L : Layout) (w n : ℕ):=scan w L.dest.base n (field L)
def after (L : Layout) (n : ℕ) (m : Memory w):=image L.dest.base n (field L) m

structure Room (L : Layout) (w n K : ℕ) : Prop where
  index : L.index.Fits w L.dest.base
  frozen : L.frozen.Fits w L.dest.base
  indexRows : n ≤ L.index.size
  frozenRows : K ≤ L.frozen.size
  destRows : n ≤ L.dest.size
  end_ : L.dest.base+n < 2^w

/-- The direct immutable ordinal depends only on the common tensor dimensions. -/
def literal (number : Fin n→Fin K) (a : ℕ) : ℕ:=if h:a < n then (number ⟨a,h⟩).val else 0

def mounted (L : Layout) (number : Fin n→Fin K) (old : Memory w) : Memory w :=
  fillSegment L.index.base n (fun a=>(literal number (a-L.index.base):Word w)) old

theorem literal_at (L : Layout) (number : Fin n→Fin K) (old : Memory w) (i : Fin n) :
    mounted L number old (L.index.base+i.val)=((number i).val:Word w) := by
  have hi:=i.isLt
  simp [mounted,fillSegment,literal,show L.index.base+i.val < L.index.base+n by omega,hi]

theorem calendar_literal (L : Layout) (E j rest kept : ℕ)
    (lower : j ≤ kept) (upper : kept ≤ j+(j+rest)) (old : Memory w) (i : Fin (E*2^(j+rest))) :
    mounted L (calendarIndex E j rest kept lower upper) old (L.index.base+i.val)=(calendar E j rest kept i:Word w) :=
  literal_at L (calendarIndex E j rest kept lower upper) old i

theorem literal_frame (L : Layout) (number : Fin n→Fin K) (old : Memory w) (a : ℕ)
    (away : a < L.index.base ∨ L.index.base+n ≤ a) : mounted L number old a=old a := by
  simp [mounted,fillSegment,show ¬(L.index.base ≤ a ∧ a < L.index.base+n) by omega]

theorem run (L : Layout) (R : Room L w n K) (m : Memory w) :
    (program L w n).Exec m (after L n m) (4+28*n) ∧ CheapCode (program L w n) := by
  have fee : 4+n*(2*(field L).work+4)=4+28*n:=by change 4+n*28=_;omega
  constructor
  · rw [←fee]
    exact scan_exec L.dest.base n (field L) m ⟨R.frozen,R.index,trivial⟩ R.end_
  · exact scan_cheap w L.dest.base n (field L)

theorem frame (L : Layout) (m : Memory w) {a : ℕ} (away : a < L.dest.base ∨ L.dest.base+n ≤ a) :
    after L n m a=m a := by simp [after,image,fillSegment,show ¬(L.dest.base ≤ a ∧ a < L.dest.base+n) by omega]

theorem honest (L : Layout) (R : Room L w n K) (number : Fin n→Fin K) (home : Fin K→Fin H)
    (m : Memory w) (idx : ∀i : Fin n,m (L.index.base+i.val)=((number i).val:Word w))
    (frozen : ∀k : Fin K,m (L.frozen.base+k.val)=((home k).val:Word w)) (i : Fin n) :
    after L n m (L.dest.base+i.val)=((home (number i)).val:Word w) := by
  have a:=i.isLt.trans_le R.indexRows;have b:=(number i).isLt.trans_le R.frozenRows
  have e1 : L.index.read m (i.val:Word w)=((number i).val:Word w) := by
    simpa only [Bank.read,Fin.val_cast_of_lt (a.trans R.index.2.1),Nat.mod_eq_of_lt a] using idx i
  have e2 : L.frozen.read m ((number i).val:Word w)=((home (number i)).val:Word w) := by
    simpa only [Bank.read,Fin.val_cast_of_lt (b.trans R.frozen.2.1),Nat.mod_eq_of_lt b] using frozen (number i)
  have at_ : after L n m (L.dest.base+i.val)=(field L).eval m (i.val:Word w) := by
    have hi:=i.isLt
    simp [after,image,fillSegment,show L.dest.base+i.val < L.dest.base+n by omega,Nat.cast_add]
  rw [at_]
  simpa only [field,Expr.eval,e1] using e2

theorem source (L : Layout) (R : Room L w n K) (number : Fin n→Fin K) (home : Fin K→Fin H)
    (m : Memory w) (idx : ∀i : Fin n,m (L.index.base+i.val)=((number i).val:Word w))
    (frozen : ∀k : Fin K,m (L.frozen.base+k.val)=((home k).val:Word w)) (i : Fin n) :
    L.dest.read (after L n m) (i.val:Word w)=((home (number i)).val:Word w) := by
  have hi:=i.isLt;have small:=i.isLt.trans_le R.destRows;have end_:=R.end_
  simp only [Bank.read,Fin.val_cast_of_lt (by omega : i.val < 2^w),Nat.mod_eq_of_lt small]
  exact honest L R number home m idx frozen i

end
end Hierarchy.DescentTerminalPacketHomeRAM

end OAI
