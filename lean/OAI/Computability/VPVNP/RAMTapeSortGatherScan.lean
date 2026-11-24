import OAI.Computability.VPVNP.RAMTapeSortGatherWord

/-! # Scanning to a unary record offset

Five invocations of the word mover remove a physical record. An offset loop
repeats this fixed subprogram for the records preceding the selected one.
All skipped bits accumulate in reverse order for restoration.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortGather

open Routine

private def words (b : Buffer) : ℕ → FiniteRoutine Port
  | 0 => .ret
  | n+1 => (word b).followedBy (words b n)

private theorem words_runs (b : Buffer) (w n : ℕ) (s : Stacks Port) (data tail : List Bool)
    (hlen : data.length = n*w) (hb : s .block = data ++ tail)
    (hw : s .width = List.replicate w true) (ht : s .widthBack = []) :
    (words b n).Runs (n*(6*w+2)+1) s
      (Function.update (Function.update s .block tail) b.dest (data.reverse ++ s b.dest)) := by
  induction n generalizing s data with
  | zero =>
    have hd : data = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst data
    simp only [List.nil_append] at hb
    simp only [words, Nat.zero_mul, Nat.zero_add, List.reverse_nil, List.nil_append, ← hb,
      Function.update_eq_self]
    exact runs_ret s
  | succ n ih =>
    let x := data.take w
    let xs := data.drop w
    have hs : x ++ xs = data := List.take_append_drop ..
    have hle : w ≤ data.length := by rw [hlen, Nat.succ_mul]; omega
    have hx : x.length = w := by simp [x, hle]
    have hxs : xs.length = n*w := by simp [xs, hlen, Nat.succ_mul]
    let mid := Function.update (Function.update s Port.block (xs ++ tail)) b.dest
      (x.reverse ++ s b.dest)
    have hm : s .block = x ++ (xs ++ tail) := by rw [← List.append_assoc, hs, hb]
    have first := word_runs b s x (xs++tail) hm (by rwa [hx]) ht
    have rest := ih mid xs hxs (by cases b <;> simp [mid, Buffer.dest])
      (by cases b <;> simp [mid, Buffer.dest, hw]) (by cases b <;> simp [mid, Buffer.dest, ht])
    have finish : Function.update (Function.update mid .block tail) b.dest (xs.reverse ++ mid b.dest) =
        Function.update (Function.update s .block tail) b.dest (data.reverse ++ s b.dest) := by
      rw [← hs, List.reverse_append, List.append_assoc]
      funext k
      cases b <;> cases k <;> simp [mid, Buffer.dest]
    rw [finish] at rest
    rw [hx] at first
    simpa only [words, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      FiniteRoutine.Runs.followedBy first rest

/-- Place the block, skipped prefix, selected record and output on their gather ports with
unary offset and width counters and empty width scratch. -/
def store (w i : ℕ) (block saved selected out : List Bool) : Stacks Port
  | .block => block
  | .offset => List.replicate i true
  | .width => List.replicate w true
  | .widthBack => []
  | .saved => saved
  | .recordBack => selected
  | .output => out

/-- The skipped prefix is saved bit-for-bit on a single reverse buffer. -/
def skip : FiniteRoutine Port := .ofRoutine
  (popLoop Port.offset (fun _ => true) (halt false) (words .skipped 5).body)

theorem skip_runs (w i : ℕ) (pre tail saved selected out : List Bool)
    (hlen : pre.length = i*(5*w)) :
    skip.Runs (i*(30*w+12)+1) (store w i (pre++tail) saved selected out)
      (store w 0 tail (pre.reverse++saved) selected out) := by
  induction i generalizing pre saved with
  | zero =>
    have h : pre = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst pre
    simp only [Nat.zero_mul, Nat.zero_add, List.nil_append, List.reverse_nil]
    exact Runs.popLoop_empty Port.offset (fun _ => true) (halt false) (words .skipped 5).body rfl
  | succ i ih =>
    let x := pre.take (5*w)
    let xs := pre.drop (5*w)
    have hs : x ++ xs = pre := List.take_append_drop ..
    have hle : 5*w ≤ pre.length := by rw [hlen, Nat.succ_mul i (5*w)]; omega
    have hx : x.length = 5*w := by simp [x, hle]
    have hxs : xs.length = i*(5*w) := by simp [xs, hlen, Nat.succ_mul]
    let start := store w (i+1) (pre++tail) saved selected out
    let one := store w i (pre++tail) saved selected out
    have head : start .offset = true :: List.replicate i true := List.replicate_succ
    have pop : Function.update start .offset (List.replicate i true) = one := by
      funext k
      cases k <;> rfl
    have hb := words_runs .skipped w 5 one x (xs++tail) hx
      (by change pre ++ tail = _; rw [← hs, List.append_assoc]) rfl rfl
    have hu : Function.update (Function.update one .block (xs++tail)) Buffer.skipped.dest
        (x.reverse ++ one Buffer.skipped.dest) = store w i (xs++tail) (x.reverse++saved) selected out := by
      funext k
      cases k <;> rfl
    rw [hu] at hb
    have rest := ih xs (x.reverse++saved) hxs
    have loop := Runs.popLoop_true_continue Port.offset (fun _ => true) (halt false)
      (words .skipped 5).body head rfl (by rw [pop]; exact hb) rest
    rw [show 1+(5*(6*w+2)+1)+(i*(30*w+12)+1) = (i+1)*(30*w+12)+1 by ring] at loop
    have hend : pre.reverse ++ saved = xs.reverse ++ (x.reverse ++ saved) := by
      rw [← hs, List.reverse_append, List.append_assoc]
    rw [hend]
    exact loop

/-- The selected record moves to its own reverse buffer, separate from the prefix. -/
def select : FiniteRoutine Port := words .selected 5

theorem select_runs (w i : ℕ) (data tail saved selected out : List Bool)
    (hlen : data.length = 5*w) :
    select.Runs (30*w+11) (store w i (data++tail) saved selected out)
      (store w i tail saved (data.reverse++selected) out) := by
  have h := words_runs .selected w 5 (store w i (data++tail) saved selected out) data tail hlen
    rfl rfl rfl
  have he : Function.update (Function.update (store w i (data++tail) saved selected out)
      .block tail) Buffer.selected.dest (data.reverse ++ selected) = store w i tail saved
      (data.reverse++selected) out := by
    funext k
    cases k <;> rfl
  change select.Runs _ _ (Function.update _ Buffer.selected.dest (data.reverse ++ selected)) at h
  rw [he, show 5*(6*w+2)+1 = 30*w+11 by ring] at h
  exact h

end RAMTape.SortGather

end VPVNP
end Computability
end OAI
