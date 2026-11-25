import OAI.Computability.MultitapeWeakETH.PhysicalEpoch

/-! # Loading the first operand from its external block terminals -/

namespace OAI.Computability.MultitapeWeakETH.PhysicalBlocks

open IntegerMultiplication
open scoped Classical
noncomputable section

def leftTape (M : Machine) := M.layout.elim M.input InputLayout.leftTape
def leftStart (M : Machine) (n : ℕ) := M.layout.elim 0 (fun layout => layout.leftStart n)

/-- Identify the external input bit at a physical cell, if there is one. -/
def inputIndex (M : Machine) (n : ℕ) (tape : M.Tapes) (z : ℤ) : Option (Fin n) :=
  let d := z-leftStart M n
  if h : tape = leftTape M ∧ 0 ≤ d ∧ d.toNat < n then some ⟨d.toNat,h.2.2⟩ else none

theorem inputIndex_some {M : Machine} {n : ℕ} {i : Fin n} {tape : M.Tapes} {z : ℤ}
    (h : inputIndex M n tape z = some i) : tape = leftTape M ∧ z = leftStart M n + i.val := by
  simp only [inputIndex] at h
  split at h
  · rename_i active
    cases h
    exact ⟨active.1,by dsimp; omega⟩
  · contradiction

/-- The control and all absolute head positions are independent of both operands. -/
theorem initial_controller (M : Machine) {n : ℕ} (x y x' y' : Word n) :
    (initial M x y).pc = (initial M x' y').pc ∧
    ∀ tape, ((initial M x y).tape tape).pos = ((initial M x' y').tape tape).pos := by
  cases h : M.layout <;> simp [initial,h,InputLayout.load,NearSquareRoot.initialConfig,TM.Tape.loaded]

/-- Outside the designated first-operand interval the initialized tape may
depend on the column. Inside it the symbol comes from exactly one row bit. -/
theorem initial_cell (M : Machine) {n : ℕ} (x x' y : Word n) (tape : M.Tapes) (z : ℤ) :
    ((initial M x y).tape tape).absolute z = (inputIndex M n tape z).elim
      (((initial M x' y).tape tape).absolute z) (fun i => M.bit (x i)) := by
  cases h : M.layout with
  | some layout =>
    simp only [initial,h,inputIndex,leftTape,leftStart,Option.elim_some,InputLayout.load,
      TM.Tape.absolute,add_sub_cancel]
    split <;> simp_all
  | none =>
    simp only [initial,h,NearSquareRoot.initialConfig,inputIndex,leftTape,leftStart,
      Option.elim_none,sub_zero,TM.Tape.loaded,TM.Tape.absolute]
    by_cases ht : tape = M.input
    · subst tape
      cases z with
      | negSucc a => simp
      | ofNat k =>
        by_cases hk : k < n
        · simp [hk,List.append_assoc,List.getElem?_append_left
            (show k < (List.ofFn (M.bit ∘ x)).length by simpa)]
        · simp [hk,List.append_assoc,List.getElem?_append_right
            (show (List.ofFn (M.bit ∘ x)).length ≤ k by simpa using Nat.le_of_not_gt hk),
            List.getElem?_append_right
            (show (List.ofFn (M.bit ∘ x')).length ≤ k by simpa using Nat.le_of_not_gt hk)]
    · simp [ht]

variable {M : Machine} {n b : ℕ}

/-- The operand loaded after the first j external block vertices. -/
def loadedPrefix (x : Word n) (b j : ℕ) : Word n := fun i => if block b i < j then x i else false

@[simp] theorem prefix_zero (x : Word n) (b : ℕ) : loadedPrefix x b 0 = fun _ => false := by
  funext i
  simp [loadedPrefix]

theorem prefix_all (hb : 0 < b) (x : Word n) : loadedPrefix x b (n ⌈/⌉ b) = x := by
  funext i
  have small : n-1-i.val < b*(n ⌈/⌉ b) :=
    lt_of_lt_of_le (by omega : n-1-i.val < n) ((ceilDiv_le_iff_le_mul hb).mp le_rfl)
  have lt : block b i < n ⌈/⌉ b := (Nat.div_lt_iff_lt_mul hb).mpr (by simpa [mul_comm] using small)
  simp [loadedPrefix,lt]

/-- Updating a single external block leaves every other register unchanged.
Within its two possible physical blocks it overwrites exactly the new bits. -/
def insertBits (_hb : 0 < b) (j : ℕ) (x : Word n) (i : Key M) (old : Value M b i) :
    Value M b i :=
  match i with
  | none => old
  | some (tape,blockId) => fun r =>
    match inputIndex M n tape (blockId*b+r.val) with
    | none => old r
    | some k => if block b k = j then M.bit (x k) else old r

theorem prefix_succ (hb : 0 < b) (j : ℕ) (x y : Word n) (key : Key M) :
    store hb (.running (initial M (loadedPrefix x b (j+1)) y)) key =
      insertBits hb j x key (store hb (.running (initial M (loadedPrefix x b j) y)) key) := by
  cases key with
  | none =>
    have ctrl := initial_controller M (loadedPrefix x b (j+1)) y (loadedPrefix x b j) y
    simp only [store,insertBits,config,stopped,ctrl.1,ctrl.2]
    rfl
  | some p =>
    obtain ⟨tape,id⟩ := p
    funext r
    change ((initial M (loadedPrefix x b (j+1)) y).tape tape).absolute (id*b+r.val) = _
    rw [initial_cell M _ (loadedPrefix x b j)]
    cases h : inputIndex M n tape (id*b+r.val) with
    | none => simp [insertBits,h,store,config]
    | some k =>
      by_cases equal : block b k = j
      · simp [insertBits,h,loadedPrefix,equal]
      · have old := initial_cell M (loadedPrefix x b j) (loadedPrefix x b j) y tape (id*b+r.val)
        simp only [h,Option.elim_some] at old
        simp only [h,Option.elim_some,insertBits,equal,ite_false,store,config,old,loadedPrefix]
        have eq : block b k < j+1 ↔ block b k < j := by omega
        simp only [eq]

theorem insertBits_outside (hb : 0 < b) (j : ℕ) (x : Word n) (key : Key M)
    (outside : key ∉ ioKeys M (leftTape M) (leftStart M n) n b j) (old : Value M b key) :
    insertBits hb j x key old = old := by
  cases key with
  | none => rfl
  | some p =>
    obtain ⟨tape,id⟩ := p
    funext r
    simp only [insertBits]
    split
    · rfl
    · rename_i k present
      split
      · rename_i eq
        obtain ⟨rfl,cell⟩ := inputIndex_some present
        have hk := mem_ioKeys M hb k (leftStart M n) (leftTape M)
        rw [← cell,eq] at hk
        have blockEq : (id*b+r.val)/(b:ℤ) = id := by
          rw [add_comm,Int.add_mul_ediv_right _ _ (by omega),Int.ediv_eq_zero_of_lt (by omega) (by omega),zero_add]
        exact (outside (blockEq ▸ hk)).elim
      · rfl


theorem insertBits_congr (hb : 0 < b) {j : ℕ} {x x' : Word n}
    (agree : ∀ i, block b i = j → x i = x' i) (key : Key M) (old : Value M b key) :
    insertBits hb j x key old = insertBits hb j x' key old := by
  cases key with
  | none => rfl
  | some p =>
    obtain ⟨tape,id⟩ := p
    funext r
    simp only [insertBits]
    split
    · rfl
    · split
      · exact congrArg M.bit (agree _ ‹_›)
      · rfl

end
end OAI.Computability.MultitapeWeakETH.PhysicalBlocks
