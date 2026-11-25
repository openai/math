import OAI.Hierarchy.TraceReceiverPreparation
import OAI.ThreeFlat.RAM.HistoryCommandTable

namespace OAI
/-! # Readback of all three selected prefixes and every task in the native receiver -/
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing BigOperators Classical

variable {W : ℕ}

/-- The numeric S13 amount read from the selected node, using its actual ordinal. -/
def cacheAmount (D : Layout) (m : Memory W) (j : Fin 3) (i : ℕ) :=
  (m (amountAddress D.selected D.first D.results j m (i:Word W)).val).val

private theorem afterColumn_away (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ)
    (z : Memory W) (j : Fin 3) (a : ℕ) (head : a<D.current ∨ D.current+7≤a)
    (scratch : a<width j ∨ width j+n≤a) (out : a<columnBase D j ∨ columnBase D j+(n+1)≤a) :
    afterColumn D count cap width n j z a=z a := by
  have h : ¬(D.current≤a ∧ a<D.current+7) := by omega
  have w : ¬(width j≤a ∧ a<width j+n) := by omega
  have p : ¬(columnBase D j≤a ∧ a<columnBase D j+(n+1)) := by omega
  simp only [afterColumn,columnImage,TerminalWireArchive.image,prefixLayout,amountImage,rangeImage,
    fillSegment,ite_eq_right p,ite_eq_right w,ite_eq_right h]

private theorem col_low (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ)
    (h : BeforeBounds D count cap width n W) (j : Fin 3) (m : Memory W)
    (a : ℕ) (low : a<D.current) : afterColumn D count cap width n j m a=m a :=
  afterColumn_away D count cap width n m j a (Or.inl low)
    (Or.inl (by have := h.widthHigh j;omega)) (Or.inl (by have := h.prefixHigh j;omega))

theorem beforeStart_low (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ)
    (room : BeforeBounds D count cap width n W) (m : Memory W) (a : ℕ) (low : a<D.current) :
    beforeStart D count cap width n m a=m a := by
  have outside : ¬(D.current≤a ∧ a<D.current+7) := by omega
  simp only [beforeStart,rangeImage,fillSegment,ite_eq_right outside,col_low D count cap width n room _ _ a low]

theorem before_low (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ)
    (room : BeforeBounds D count cap width n W) (m : Memory W) (a : ℕ) (low : a<D.current) :
    beforeImage D count cap width n m a=m a := by
  have outside : ¬(D.tasks≤a ∧ a<D.tasks+5*n) := by have := room.tasksHigh;omega
  simp only [beforeImage,output,fillSegment,ite_eq_right outside,beforeStart_low D count cap width n room m a low]

/-- Preserve a numeric word outside the actual temporary and destination intervals. -/
theorem before_away (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ) (m : Memory W)
    (a : ℕ) (head : a<D.current ∨ D.current+7≤a) (tasks : a<D.tasks ∨ D.tasks+5*n≤a)
    (raw : ∀ j,a<width j ∨ width j+n≤a)
    (pre : ∀ j,a<columnBase D j ∨ columnBase D j+(n+1)≤a) :
    beforeImage D count cap width n m a=m a := by
  have h : ¬(D.current≤a ∧ a<D.current+7) := by omega
  have t : ¬(D.tasks≤a ∧ a<D.tasks+5*n) := by omega
  simp only [beforeImage,output,fillSegment,ite_eq_right t,beforeStart,rangeImage,ite_eq_right h]
  rw [afterColumn_away D count cap width n _ 2 a head (raw 2) (pre 2),
    afterColumn_away D count cap width n _ 1 a head (raw 1) (pre 1),
    afterColumn_away D count cap width n m 0 a head (raw 0) (pre 0)]

/-- One physical prefix is exactly the sum of the original selected cache amounts. -/
private theorem one_prefix (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ)
    (room : BeforeBounds D count cap width n W) (m z : Memory W) (j : Fin 3)
    (agree : ∀ a,a<D.current → z a=m a)
    (cache : ∀ i : Fin n,(amountAddress D.selected D.first D.results j m (i.val:Word W)).val<D.current)
    (small : ∑ i : Fin n,cacheAmount D m j i.val ≤ cap) (i : Fin n) :
    (afterColumn D count cap width n j z (columnBase D j+i.val)).val=
      ∑ k : Fin i.val,cacheAmount D m j k.val := by
  let ini := rangeImage D.current count (width j) (columnBase D j) 1 z
  let x := prefixLayout D.current cap (width j) (columnBase D j) n
  have low (a : ℕ) (ha : a<D.current) : ini a=m a := by
    have outside : ¬(D.current≤a ∧ a<D.current+7) := by omega
    simpa only [ini,rangeImage,fillSegment,ite_eq_right outside] using agree a ha
  have fr : (D.first:Word W).val=D.first := Fin.val_cast_of_lt (by have := room.firstLow;have := room.head;omega)
  have same (k : ℕ) (hk : k<n) :
      (ini (amountAddress D.selected D.first D.results j ini (k:Word W)).val).val=cacheAmount D m j k := by
    have v := room.selectedLow
    have hf := room.head
    have sv : ((D.selected:Word W)+(k:Word W)).val=D.selected+k := by
      rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    have addr : amountAddress D.selected D.first D.results j ini (k:Word W)=
        amountAddress D.selected D.first D.results j m (k:Word W) := by
      have first := low (D.first:Word W).val (by rw [fr];exact room.firstLow)
      have chosen := low ((D.selected:Word W)+(k:Word W)).val (by rw [sv];omega)
      simp only [amountAddress,first,chosen]
    rw [addr,low _ (cache ⟨k,hk⟩)]
    rfl
  have eqn : (∑ k : Fin n,(ini (amountAddress D.selected D.first D.results j ini (k.val:Word W)).val).val)=
      ∑ k : Fin n,cacheAmount D m j k.val := Finset.sum_congr rfl (fun k _=>same k.val k.isLt)
  exact (amount_prefix x ini D.selected D.first D.results j (room.col j) (eqn.trans_le small) i.val i.isLt.le).trans
    (Finset.sum_congr rfl (fun k _=>same k.val (k.isLt.trans i.isLt)))

/-- Numeric separation of the three prefix outputs and their scratch inputs. -/
structure ColumnSeparation (D : Layout) (width : Fin 3 → ℕ) (n : ℕ) : Prop where
  widths : ∀ j k,columnBase D j+n ≤ width k
  distinct : ∀ j k,j≠k → columnBase D j+n ≤ columnBase D k ∨ columnBase D k+(n+1) ≤ columnBase D j

theorem beforeStart_prefix (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ)
    (room : BeforeBounds D count cap width n W) (apart : ColumnSeparation D width n)
    (m : Memory W)
    (cache : ∀ j (i : Fin n),(amountAddress D.selected D.first D.results j m (i.val:Word W)).val<D.current)
    (small : ∀ j, ∑ i : Fin n,cacheAmount D m j i.val ≤ cap) (j : Fin 3) (i : Fin n) :
    (beforeStart D count cap width n m (columnBase D j+i.val)).val=∑ k : Fin i.val,cacheAmount D m j k.val := by
  let next := afterColumn D count cap width n (W:=W)
  let z1 := next 0 m
  let z2 := next 1 z1
  have l1 (a : ℕ) (ha : a<D.current) : z1 a=m a := col_low D count cap width n room 0 m a ha
  have l2 (a : ℕ) (ha : a<D.current) : z2 a=m a := (col_low D count cap width n room 1 z1 a ha).trans (l1 a ha)
  have hi := i.isLt
  have keep (j k : Fin 3) (h : j≠k) (z : Memory W) :
      next k z (columnBase D j+i.val)=z (columnBase D j+i.val) := by
    have h1 := room.prefixHigh j
    have h2 := apart.widths j k
    have h3 := apart.distinct j k h
    exact afterColumn_away D count cap width n z k _ (Or.inr (by omega)) (Or.inl (by omega)) (by omega)
  have far : ¬(D.current≤columnBase D j+i.val ∧ columnBase D j+i.val<D.current+7) := by
    have := room.prefixHigh j;omega
  simp only [beforeStart,rangeImage,fillSegment,ite_eq_right far]
  change ((next 2 z2) (columnBase D j+i.val)).val=_
  fin_cases j
  · exact (congrArg Fin.val ((keep 0 2 (by decide) z2).trans (keep 0 1 (by decide) z1))).trans
      (one_prefix D count cap width n room m m 0 (fun _ _=>rfl) (cache 0) (small 0) i)
  · exact (congrArg Fin.val (keep 1 2 (by decide) z2)).trans
      (one_prefix D count cap width n room m z1 1 l1 (cache 1) (small 1) i)
  · exact one_prefix D count cap width n room m z2 2 l2 (cache 2) (small 2) i

/-- All five words of the selected native task, with the original physical
node ID, immutable parent and exact local prefix for each of its three arrays. -/
theorem prepared_task (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ)
    (room : BeforeBounds D count cap width n W) (apart : ColumnSeparation D width n)
    (m : Memory W)
    (cache : ∀ j (i : Fin n),(amountAddress D.selected D.first D.results j m (i.val:Word W)).val<D.current)
    (small : ∀ j, ∑ i : Fin n,cacheAmount D m j i.val ≤ cap) (i : Fin n) :
    let ps (j : Fin 3) := ((∑ k : Fin i.val,cacheAmount D m j k.val : ℕ):Word W)
    RAM.HistoryCommandTable.readTask (beforeImage D count cap width n m) ((D.tasks+5*i.val:ℕ):Word W)=
      ⟨(D.results:Word W)+8*(m D.first+m (D.selected+i.val)),D.parent,
        (D.maps:Word W)+ps 0,ps 1,ps 2⟩ := by
  intro ps
  let z := beforeStart D count cap width n m
  let out := beforeImage D count cap width n m
  let task := ((D.tasks+5*i.val:ℕ):Word W)
  have it := i.isLt
  have rh := room.head
  have rt := room.tasksFit
  have dose : 5<2^W := by omega
  have amount (j : Fin 3) :
      z ((columnBase D j:Word W)+(i.val:Word W)).val=ps j := by
    have v := (room.reads j).1
    change z ((columnBase D j:Word W)+(i.val:Word W)).val=_
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    have partialSum := beforeStart_prefix D count cap width n room apart m cache small j i
    exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun t : ℕ=>(t:Word W)) partialSum)
  have fr : z (D.first:Word W).val=m D.first := by
    rw [Fin.val_cast_of_lt (by have := room.firstLow;omega)]
    exact beforeStart_low D count cap width n room m _ room.firstLow
  have sr : z ((D.selected:Word W)+(i.val:Word W)).val=m (D.selected+i.val) := by
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by have := room.selectedLow;omega)]
    exact beforeStart_low D count cap width n room m _ (by have := room.selectedLow;omega)
  have cond (j k : Fin 5) :
      Comparison.test .eq (j.val:Word W) (k.val:Word W)=decide (j=k) := by
    by_cases eq : j=k
    · subst k;simp [Comparison.test]
    · have ne : (j.val:Word W)≠(k.val:Word W) := fun he=>eq (Fin.ext (by
        have h:=congrArg Fin.val he
        rwa [Fin.val_cast_of_lt (j.isLt.trans dose),Fin.val_cast_of_lt (k.isLt.trans dose)] at h))
      simp [Comparison.test,eq,ne]
  have c0 (j : Fin 5) : Comparison.test .eq (j.val:Word W) 0=decide (j=0) := cond j 0
  have c1 (j : Fin 5) : Comparison.test .eq (j.val:Word W) 1=decide (j=1) := cond j 1
  have c2 (j : Fin 5) : Comparison.test .eq (j.val:Word W) 2=decide (j=2) := cond j 2
  have c3 (j : Fin 5) : Comparison.test .eq (j.val:Word W) 3=decide (j=3) := cond j 3
  have row (j : Fin 5) : out (task+(j.val:Word W)).val =
      (![(D.results:Word W)+8*(m D.first+m (D.selected+i.val)),D.parent,(D.maps:Word W)+ps 0,
        ps 1,ps 2]:Fin 5→Word W) j := by
    change out ((((D.tasks+5*i.val:ℕ):Word W)+(j.val:Word W))).val=_
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by have := j.isLt;omega)]
    have r := at_root D n z rt i j
    refine r.trans ?_
    have p0 : z ((D.pins:Word W)+(i.val:Word W)).val=ps 0 := amount 0
    have p1 : z ((D.rows:Word W)+(i.val:Word W)).val=ps 1 := amount 1
    have p2 : z ((D.bits:Word W)+(i.val:Word W)).val=ps 2 := amount 2
    simp only [entry,c0,c1,c2,c3,fr,sr,p0,p1,p2]
    fin_cases j <;> rfl
  change HistoryCommandTable.Task.mk (out (task+0).val) (out (task+1).val) (out (task+2).val)
    (out (task+3).val) (out (task+4).val) = _
  congr 1
  · exact row 0
  · exact row 1
  · exact row 2
  · exact row 3
  · exact row 4

end Hierarchy.TraceReceiverTasks

end OAI
