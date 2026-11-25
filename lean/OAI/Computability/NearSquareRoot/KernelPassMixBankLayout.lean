import OAI.Computability.IntegerMultiplication.Match
import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Transposing a fixed bank of streams

The row count is compiled into the program. Each step of the gather zips
one more row onto the address records. In the other direction each step
splits off the first component. The address ruler also determines the
number of empty input tuples when the bank has zero rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace MixBankLayout

open IntegerMultiplication.Code

variable {X α : Type}

/-- The input bank consists of complete rows in address order. -/
def bank {i : ℕ} (l : List α) (x : α → Fin i → X) : List (List X) :=
  List.ofFn fun j => l.map fun c => x c j

def align : (i : ℕ) → X → Tally × List (List X) → List (List X)
  | 0, _, p => p.1.map fun _ => []
  | i+1, d, p =>
    (zipFair d [] (p.2.headD [], align i d (p.1, p.2.tail))).map
      fun z => z.1 :: z.2

def scatter : (i : ℕ) → X → List (List X) → List (List X)
  | 0, _, _ => []
  | i+1, d, l => (l.map fun t => t.headD d) :: scatter i d (l.map List.tail)

private theorem tail_easy {Y : Type} [Codec Y] : Easy (@List.tail Y) := by
  have h := Easy.listCase ([] : List Y) (Easy.snd : Easy (fun p : Y × List Y => p.2))
  change Easy (fun l : List Y => l.tail)
  convert h using 1
  funext l
  cases l <;> rfl

/-- P192 stack program for gathering the entries from all rows. -/
theorem easy_align [Codec X] (i : ℕ) (d : X) : Easy (align i d) := by
  induction i with
  | zero => exact Easy.fst.compose (Easy.const ([] : List X)).mapping
  | succ i ih =>
    have ht : Easy (fun p : Tally × List (List X) => (p.1, p.2.tail)) :=
      Easy.fst.pair (Easy.snd.compose tail_easy)
    have hh : Easy (fun p : Tally × List (List X) => p.2.headD []) :=
      Easy.snd.compose (Iter.leader [])
    exact ((hh.pair (ht.compose ih)).compose (easy_zip d ([] : List X))).compose
      Easy.cons.mapping

/-- P192 stack program for the inverse change of layout. -/
theorem easy_scatter [Codec X] (i : ℕ) (d : X) : Easy (scatter i d) := by
  induction i with
  | zero => exact Easy.const _
  | succ i ih =>
    exact ((Iter.leader d).mapping.pair (tail_easy.mapping.compose ih)).compose Easy.cons

theorem align_bank {i : ℕ} (d : X) (l : List α) (x : α → Fin i → X) :
    align i d (tally l.length, bank l x) = l.map fun c => List.ofFn (x c) := by
  induction i with
  | zero => simp [align, tally]
  | succ i ih =>
    let tail (c : α) (j : Fin i) := x c j.succ
    have eq : bank l x = (l.map fun c => x c 0) :: bank l tail := List.ofFn_succ
    rw [align, eq]
    simp only [List.headD_cons, List.tail_cons, ih, fair, List.map_map]
    apply List.map_congr_left
    intro c _
    exact List.ofFn_succ.symm

theorem scatter_columns {i : ℕ} (d : X) (l : List α) (x : α → Fin i → X) :
    scatter i d (l.map fun c => List.ofFn (x c)) = bank l x := by
  induction i with
  | zero => simp [scatter, bank]
  | succ i ih =>
    let tail (c : α) (j : Fin i) := x c j.succ
    have eq : bank l x = (l.map fun c => x c 0) :: bank l tail := List.ofFn_succ
    rw [scatter, eq]
    simp only [List.map_map]
    have t (c : α) : (List.ofFn (x c)).tail = List.ofFn (tail c) := by
      rw [List.ofFn_succ]
      rfl
    have h (c : α) : (List.ofFn (x c)).headD d = x c 0 := by rw [List.ofFn_succ]; rfl
    simpa only [Function.comp_def, t, h] using congrArg (List.cons (l.map fun c => x c 0)) (ih tail)

private theorem row_size [Codec X] (l : List α) (x : α → X) (b : ℕ)
    (h : ∀ a ∈ l, size (x a) ≤ b) :
    size (l.map x) ≤ l.length * (b + 1) + 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih (fun z hz => h z (List.mem_cons_of_mem a hz))
    simp only [List.map_cons, size_cons, List.length_cons, Nat.succ_mul]
    omega

/-- The budget of the gather includes all delimiter symbols and every input record. -/
theorem size_bank_le [Codec X] {i : ℕ} (l : List α) (x : α → Fin i → X) (b : ℕ)
    (h : ∀ a ∈ l, ∀ j, size (x a j) ≤ b) :
    size (bank l x) ≤ i * (l.length * (b + 1) + 2) + 1 := by
  induction i with
  | zero => simp [bank]
  | succ i ih =>
    let tail (a : α) (j : Fin i) := x a j.succ
    have e : bank l x = (l.map fun c => x c 0) :: bank l tail := List.ofFn_succ
    have hh := row_size l (fun c => x c 0) b (fun c hc => h c hc 0)
    have ht := ih tail (fun c hc j => h c hc j.succ)
    rw [e, size_cons, Nat.succ_mul]
    omega

end MixBankLayout

end NearSquareRoot
end Computability
end OAI
