import OAI.ThreeFlat.Diagonal.ConstantKernelLUT
import OAI.ThreeFlat.RAM.HistoryCompiledRows
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Read-only packed descriptor pages for the finitely many base LUTs

Each record is shared by all copies at all sites and all ages. Its first
two words hold the true hidden count and row count; the next words are the
actual three physical source addresses and universal table ID per row.
-/
namespace ThreeFlat.RAM.HistoryStaticArchive

open Diagonal Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing Classical
noncomputable section

variable {F : Type*} [CommRing F] [Fintype F] {w k n bmax : ℕ}

structure Catalog (F : Type*) (n bmax : ℕ) where
  arity : Fin n → ℕ
  fits : ∀ i, arity i ≤ bmax
  coeff : ∀ i, (Fin (arity i) → Bool) → F

variable (L : Catalog F n bmax)

def stride (b : ℕ) := 2+4*(2^b*(b+1))
def size (n b : ℕ) := n*stride b

namespace Catalog

def rows (i : Fin n) := ConstantKernelLUT.network (L.coeff i)

omit [Fintype F] in
theorem rows_fit (i : Fin n) : 2+4*(L.rows i).cells ≤ stride bmax := by
  have eq := ConstantKernelLUT.network_cells (L.coeff i)
  have cap : 2^(L.arity i)*(L.arity i+1) ≤ 2^bmax*(bmax+1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (L.fits i)) (Nat.succ_le_succ (L.fits i))
  simpa only [stride,rows,eq] using Nat.add_le_add_left (Nat.mul_le_mul_left 4 cap) 2

def page (i : Fin n) (j : ℕ) : ℕ :=
  if j=0 then (L.rows i).internal else if j=1 then (L.rows i).cells else
    let q := j-2
    if h : q/4 < (L.rows i).cells then HistoryCompiledRows.metadata (fun t => (Fintype.equivFin _ t).val) (L.rows i)
      ⟨q/4,h⟩ ⟨q%4,Nat.mod_lt _ (by decide)⟩ else 0

/-- This is the literal static advice segment copied to S38 after the
multiscale compactor pages. -/
def data (q : Fin (size n bmax)) : Word w :=
  if h : q.val/stride bmax<n then (L.page ⟨q.val/stride bmax,h⟩ (q.val%stride bmax) : Word w) else 0

def Stores (base : ℕ) (mem : Memory w) := ∀ q : Fin (size n bmax), mem (base+q.val) = L.data q

theorem read (i : Fin n) (j : Fin (stride bmax)) (base : ℕ) (mem : Memory w) (hm : L.Stores base mem) :
    mem (base+(i.val*stride bmax+j.val)) = (L.page i j.val : Word w) := by
  let q := finProdFinEquiv (i,j)
  have ix : q.val = j.val+stride bmax*i.val := rfl
  have div : q.val/stride bmax = i.val := by rw [ix,Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt j.isLt),Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  have rem : q.val%stride bmax = j.val := by rw [ix,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt]
  have word : L.data (w:=w) q = (L.page i j.val : Word w) := by
    simp only [data,div,rem,dite_eq_left i.isLt]
  have offset : i.val*stride bmax+j.val=q.val := by rw [ix]; ac_rfl
  rw [offset]
  exact (hm q).trans word

theorem page_row (i : Fin n) (a : Fin (L.rows i).cells) (b : Fin 4) :
    L.page i (2+(4*a.val+b.val)) = HistoryCompiledRows.metadata (fun t => (Fintype.equivFin _ t).val) (L.rows i) a b := by
  have hb := b.isLt
  have div : (4*a.val+b.val)/4 = a.val := by omega
  have mod : (4*a.val+b.val)%4 = b.val := by omega
  have pastHeader : 2+(4*a.val+b.val)≠1 := by omega
  simp [page,pastHeader,div,mod,a.isLt]

end Catalog

/-- Address of one word in an arbitrarily selected template. The four
registers contain the archive base, common page stride, page, word. -/
def program (w k : ℕ) : Term w k 4 := (Term.binary .add (.result 0)
  (Term.binary .add (Term.binary .mul (.result 1) (.result 2)) (.result 3))).load

theorem program_binds : (program w k).binds=4 := by rfl

theorem Catalog.program_read (i : Fin n) (j : Fin (stride bmax)) (base : ℕ) (mem : Memory w) (pub : Fin k → Word w)
    (hm : L.Stores base mem) (room : base+size n bmax≤2^w) :
    (program w k).eval pub mem ![(base:Word w),(stride bmax:Word w),(i.val:Word w),(j.val:Word w)] = (L.page i j.val : Word w) := by
  let q := finProdFinEquiv (i,j)
  have qbound : stride bmax*i.val+j.val < size n bmax := by
    simpa only [size,Nat.add_comm] using (show j.val+stride bmax*i.val<n*stride bmax from q.isLt)
  have fit : base+(stride bmax*i.val+j.val)<2^w := by omega
  have fitsRead : base+(i.val*stride bmax+j.val)<2^w := by simpa only [Nat.mul_comm] using fit
  simpa [program,Term.eval_load,Term.eval_binary,Term.eval,BinaryOp.eval,←Nat.cast_mul,←Nat.cast_add,
    Fin.val_cast_of_lt fit,Nat.mul_comm,Nat.mod_eq_of_lt fitsRead] using L.read i j base mem hm

end
end ThreeFlat.RAM.HistoryStaticArchive

end OAI
