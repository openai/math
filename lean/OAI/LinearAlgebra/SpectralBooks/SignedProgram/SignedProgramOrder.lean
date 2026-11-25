import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramHot

/-! # From the physical coordinates to the parser slot order -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram.Hot
open SignedMachine

def MoveCell.active {n : ℕ} (tapes : Fin (n+1)) : MoveCell n → Bool
  | .state | .inputMove => true
  | .write i | .direction i => decide (i.val < tapes.val)

def RowCell.active {n : ℕ} (tapes : Fin (n+1)) (kind : Fin 3) : RowCell n → Bool
  | .state | .input | .kind => true
  | .read j => decide (j.val < tapes.val)
  | .out => decide (kind = 0)
  | .move b c => (if b then decide (kind = 2) else decide (kind ≠ 0)) && c.active tapes

def Cell.active {n : ℕ} (t : Table n) : Cell n → Bool
  | .tapes | .rows => true
  | .row i c => decide (i.val < t.rows.val) && c.active t.tapes (t.row i).kind

private def copies {α : Type*} {n : ℕ} (f : Fin n → List α) : List α := (List.ofFn f).flatten

def moves (n : ℕ) : List (MoveCell n) :=
  [.state,.inputMove] ++ copies fun i ↦ [.write i,.direction i]

def rowCells (n : ℕ) : List (RowCell n) :=
  [.state,.input] ++ (List.ofFn .read) ++ [.kind,.out] ++
    (moves n).map (.move false) ++ (moves n).map (.move true)

def cells (n : ℕ) : List (Cell n) :=
  [.tapes,.rows] ++ copies fun i ↦ (rowCells n).map (.row i)

private theorem len_copies {α : Type*} {n l : ℕ} {f : Fin n → List α} (h : ∀ i, (f i).length = l) :
    (copies f).length = n*l := by
  simp [copies,List.length_flatten,List.map_ofFn,Function.comp_def,h,List.ofFn_const]

@[simp] theorem moves_length (n : ℕ) : (moves n).length = 2+2*n := by
  rw [moves, List.length_append, len_copies (l := 2) (fun _ ↦ rfl)]
  simp [Nat.mul_comm]

@[simp] theorem rowCells_length (n : ℕ) : (rowCells n).length = 8+5*n := by
  simp [rowCells]
  omega

@[simp] theorem cells_length (n : ℕ) : (cells n).length = 2+n*(8+5*n) := by
  rw [cells, List.length_append,len_copies (l := 8+5*n) (fun _ ↦ by simp)]
  rfl

theorem mem_moves {n : ℕ} (c : MoveCell n) : c ∈ moves n := by
  cases c <;> simp [moves,copies,List.mem_flatten,List.mem_ofFn]

theorem mem_rowCells {n : ℕ} (c : RowCell n) : c ∈ rowCells n := by
  cases c with
  | move b c => cases b <;> simp [rowCells,mem_moves]
  | _ => simp [rowCells,List.mem_ofFn]

theorem mem_cells {n : ℕ} (c : Cell n) : c ∈ cells n := by
  cases c with
  | row i r =>
    simp only [cells,List.cons_append,List.nil_append,List.mem_cons, reduceCtorEq,false_or,copies, List.mem_flatten,List.mem_ofFn]
    exact ⟨_, ⟨i,rfl⟩,List.mem_map.mpr ⟨r,mem_rowCells r,rfl⟩⟩
  | _ => simp [cells]

theorem cells_card_le (n : ℕ) : Fintype.card (Cell n) ≤ 2+n*(8+5*n) := by
  classical
  have he : (cells n).toFinset = Finset.univ := Finset.ext (by simp [mem_cells])
  simpa [he] using (cells n).toFinset_card_le

theorem decodeGuessWidth_le (n : ℕ) : decodeGuessWidth n ≤
    (2+n*(8+5*n))*(n+3)+(n+1)+(slotsCount n+1)*(n+1) := by
  unfold decodeGuessWidth GuessNames
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  have h := Nat.mul_le_mul_right (n+3) (cells_card_le n)
  omega

private theorem map_copies {α β : Type*} {n : ℕ} (g : α → β) (f : Fin n → List α) :
    (copies f).map g = copies fun i ↦ (f i).map g := by
  simp [copies,List.map_flatten,List.map_ofFn,Function.comp_def]

private def selectValue (b : Bool) (x : ℕ) := if b then some x else none

private theorem mask_map {α : Type*} (b : Bool) (ls : List α) (on : α → Bool) (v : α → ℕ) :
    mask b (ls.map (fun c ↦ selectValue (on c) (v c))) =
      ls.map (fun c ↦ selectValue (b && on c) (v c)) := by
  cases b <;> simp [mask,selectValue]

private theorem move_slots {n : ℕ} (k : Fin (n+1)) (m : Move n) :
    m.fields k = (moves n).map (fun c ↦ selectValue (c.active k) (c.value m)) := by
  simp only [moves,List.map_append,List.map_cons,List.map_nil,map_copies,Move.fields,MoveCell.active,
    MoveCell.value,selectValue,ite_true]
  congr 1
  unfold blocks copies
  congr 2
  funext i
  by_cases h : i.val < k.val <;> simp [h,mask]

private theorem row_slots {n : ℕ} (k : Fin (n+1)) (r : Row n) :
    r.fields k = (rowCells n).map (fun c ↦ selectValue (c.active k r.kind) (c.value r)) := by
  have hread : blocks k (fun i ↦ [some (symbolCode (r.reads i))]) =
      List.ofFn (fun i : Fin n ↦ selectValue (decide (i.val < k.val)) (symbolCode (r.reads i))) := by
    unfold blocks
    have h (i : Fin n) : mask (decide (i.val < k.val)) [some (symbolCode (r.reads i))] =
        [selectValue (decide (i.val < k.val)) (symbolCode (r.reads i))] := by
      by_cases hi : i.val < k.val <;> simp [mask,selectValue,hi]
    simp_rw [h]
    have H := List.map_ofFn (f := fun i : Fin n ↦ selectValue (decide (i.val < k.val)) (symbolCode (r.reads i))) (g := fun v : Option ℕ ↦ [v])
    simp only [Function.comp_def] at H
    rw [← H]
    generalize List.ofFn _ = ls
    induction ls <;> simp [*]
  simp only [rowCells, Row.fields, hread,List.map_append,List.map_ofFn,List.map_map,Function.comp_def,
    List.map_cons,List.map_nil,RowCell.value,RowCell.active, Bool.false_eq_true, ite_false,ite_true,
    move_slots, mask_map]
  generalize r.kind = z
  fin_cases z <;> simp [selectValue,mask]

theorem body_slots {n : ℕ} (t : Table n) :
    t.bodyFields = (cells n).map (fun c ↦ selectValue (c.active t) (c.value t)) := by
  simp only [Table.bodyFields, cells,List.map_append, List.map_cons,List.map_nil,map_copies,List.map_map,
    Function.comp_def, Cell.value,Cell.active,blocks,row_slots,mask_map]
  rfl

theorem fits_iff {n : ℕ} (t : Table n) (f : Fin (n+1)) :
    t.Fits f ↔ ∀ c : Cell n, c.active t = true → c.value t ≤ n := by
  constructor
  · intro h c hc
    apply h
    rw [Table.fields,body_slots]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, mem_cells c, by simp [selectValue,hc]⟩)
  · intro h v hv
    rw [Table.fields,body_slots,List.mem_cons] at hv
    rcases hv with he | hm
    · exact Option.some.inj he ▸ Nat.le_of_lt_succ f.isLt
    · obtain ⟨c,_,hc⟩ := List.mem_map.mp hm
      by_cases ha : c.active t = true
      · have he : c.value t = v := by simpa [selectValue,ha] using hc
        exact he ▸ h c ha
      · simp [selectValue,ha] at hc

def cellAt (n : ℕ) (i : Fin (slotsCount n - 1)) : Cell n :=
  (cells n)[i.val]'(by rw [cells_length]; have := i.isLt; unfold slotsCount at this; omega)

def slotAt {n : ℕ} (t : Table n) (f : Fin (n+1)) (i : Fin (slotsCount n)) : Unary.Slot n :=
  if hi : i.val = 0 then some f else
    let c := cellAt n ⟨i.val-1,by have := i.isLt; omega⟩
    if c.active t then some (bounded n (c.value t)) else none

theorem slotAt_eq {n : ℕ} (t : Table n) (f : Fin (n+1)) (i : Fin (slotsCount n)) :
    slotAt t f i = t.slot f i := by
  unfold slotAt Table.slot
  split
  next hi =>
    have he : i = ⟨0,by simp [slotsCount]⟩ := Fin.ext hi
    subst i
    simp [Table.fields]
  next hi =>
    rcases i with ⟨j,hj⟩
    cases j with
    | zero => contradiction
    | succ j =>
      simp [Table.fields, body_slots, cellAt, selectValue]

end SignedProgram.Hot

end SpectralBooks
end LinearAlgebra
end OAI
