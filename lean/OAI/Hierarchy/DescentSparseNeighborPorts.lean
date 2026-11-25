import OAI.Hierarchy.DescentSparseDirectoryRAM
import OAI.Hierarchy.DescentPackedExchange
import OAI.Hierarchy.DescentNativeNeighbors

namespace OAI
/-! # Reading the previous native adjacency and bounding the local aperture -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM.Rect
open Sparse ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open DescentPackedExchange (Banks)
open scoped Classical Fin.CommRing
variable {C : Type*} [Fintype C] [DecidableEq C] {H d w R : ℕ}

def ports (origin : Fin H) (next : DescentPackedExchange.Port H d→Option (Fin H)) : Fin (d+1)→Option (Fin H) :=
  Fin.cases (some origin) (fun j=>next (origin,j))

def source (adj : Bank) (origin : Expr) : Fin (d+1)→Expr :=
  Fin.cases origin (fun j=>.lookup adj (.op .add (scale d origin) (.lit j.val)))

theorem source_eval (adj : Bank) (home : Fin H) (next : DescentPackedExchange.Port H d→Option (Fin H))
    (origin : Expr) (m : Memory w) (r : Word w) (pos : origin.eval m r=(home.val:Word w))
    (capacity : H*d≤adj.size) (width : adj.size<2^w)
    (values : ∀a,m (adj.base+(DescentPackedExchange.slot H d a).val)=(DescentPackedExchange.target (next a):Word w))
    (i : Fin (d+1)) :
    (source adj origin i).eval m r=(portWord (ports home next) i:Word w) := by
  cases i using Fin.cases with
  | zero => exact pos
  | succ j =>
    let ix := DescentPackedExchange.slot H d (home,j)
    have idx : ix.val=home.val*d+j.val := by change _+_*_=_;ac_rfl
    have lo := ix.isLt.trans_le capacity
    have a : (Expr.op .add (scale d origin) (.lit j.val)).eval m r=(ix.val:Word w) := by
      rw [idx]
      simp [Expr.eval,scale_eval,pos,RowOp.opcode,BinaryOp.eval,mul_comm]
    change adj.read m _=_
    rw [a]
    have got := values (home,j)
    change m (adj.base+ix.val)=(DescentPackedExchange.target (next (home,j)):Word w) at got
    simpa [Bank.read,Fin.val_cast_of_lt (lo.trans width),Nat.mod_eq_of_lt lo,portWord,ports,
      DescentPackedExchange.target,show ∀x : Option (Fin H),Option.elim x H Fin.val=(x.map Fin.val).getD H by intro x;cases x <;> rfl] using got

theorem source_work (adj : Bank) (origin : Expr) (i : Fin (d+1)) :
    (source adj origin i).work≤8+(d+1)*(origin.work+1) := by
  cases i using Fin.cases with
  | zero =>
    change origin.work≤_
    rw [Nat.succ_mul]
    omega
  | succ q =>
    change (Expr.lookup adj (.op .add (scale d origin) (.lit q.val))).work≤_
    simp [Expr.work,scale_work,Nat.succ_mul];omega

theorem source_fits (adj : Bank) (origin : Expr) (cut : ℕ) (hf : adj.Fits w cut) (originFit : origin.Fits w cut)
    (i : Fin (d+1)) : (source adj origin i).Fits w cut := by
  cases i using Fin.cases with
  | zero => exact originFit
  | succ j => exact ⟨hf,scale_fits _ _ originFit,trivial⟩

/-- Heap index of a valid dyadic interval. The local scan enumerates these
numeric indices once. Its final padding index has no occupied old header. -/
def heapCode (d q : ℕ) := 2^d-1+q

theorem heap_before {d e q t : ℕ} (h : d<e) (fit : q<2^d) : heapCode d q<heapCode e t := by
  have m := Nat.pow_le_pow_right (by decide : 0<2) (show d+1≤e from h)
  have p := Nat.two_pow_pos d
  have s := Nat.two_pow_pos e
  rw [Nat.pow_succ] at m
  unfold heapCode
  omega

theorem heap_injective {d e q t : ℕ} (a : q<2^d) (b : t<2^e) (h : heapCode d q=heapCode e t) :
    (d,q)=(e,t) := by
  rcases lt_trichotomy d e with lo|eqn|hi
  · exact ((heap_before (t:=t) lo a).ne h).elim
  · subst e
    exact congrArg (Prod.mk d) (Nat.add_left_cancel h)
  · exact ((heap_before (t:=q) hi b).ne h.symm).elim

theorem heap_range {k d q : ℕ} (depth : d≤k) (valid : q<2^d) : heapCode d q<2^(k+1) := by
  have lim := Nat.pow_le_pow_right (by decide : 0<2) depth
  have live := Nat.two_pow_pos d
  rw [Nat.pow_succ]
  unfold heapCode
  omega

def dyadicCell (col : C↪Fin H×(ℕ×ℕ)) (k : ℕ) (depth : ∀c,(col c).2.1≤k)
    (valid : ∀c,(col c).2.2<2^(col c).2.1) : C↪Fin H×Fin (2^(k+1)) where
  toFun c := ((col c).1,⟨heapCode (col c).2.1 (col c).2.2,heap_range (depth c) (valid c)⟩)
  inj' := by
    intro u v eqn
    apply col.injective
    exact Prod.ext (congrArg (fun a : Fin H×Fin (2^(k+1))=>a.1) eqn)
      (heap_injective (valid u) (valid v) (congrArg (fun a : Fin H×Fin (2^(k+1))=>a.2.val) eqn))

theorem oneNeighbor_mem {C : Type} [Fintype C] [DecidableEq C] (near : Fin H→Finset (Fin H)) (D : ℕ) (col : C↪Fin H×(ℕ×ℕ))
    (cell : C↪Fin H×Fin R) (site : ∀v,(cell v).1=(col v).1)
    (next : DescentPackedExchange.Port H d→Option (Fin H))
    (complete : ∀v u,u∈near v→∃j,next (v,j)=some u)
    {c v : C} (ok : v∈DescentSixParty.StarKeys.oneNeighbor near D col c) :
    v∈nearby cell (ports (cell c).1 next) := by
  have loc := (Finset.mem_product.mp (Finset.mem_filter.mp ok).2).1
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  rcases Finset.mem_insert.mp loc with same|edge
  · exact ⟨0,by simp [ports,site,same]⟩
  · obtain ⟨j,h⟩ := complete _ _ edge
    exact ⟨j.succ,by simpa [ports,site] using h⟩

/-- Uniform row count per origin. Both the dyadic codes and the neighbor port
list are bounded independently of the total number of occupied host sites. -/
theorem rows_bound (Δ k : ℕ) : slots Δ (2^(k+1))=1+2*(Δ+1)*2^k := by
  simp [slots,Nat.pow_succ];ring

end Hierarchy.DescentPacking.SparseBinRAM.Rect

end
end OAI
