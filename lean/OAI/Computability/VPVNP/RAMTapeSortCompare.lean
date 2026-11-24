import OAI.Computability.VPVNP.RAMTapeSortRecordCode

/-! # Return values and exact costs of the physical sorting comparator -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Sorter

open RAMBoundary

private theorem discard_run (mode : Mode) (r : Route) (ok : Bool) (hd : r.dst = none)
    (s : Stacks Port) (xs : List Bool) :
    StackRuns (recordCode mode) (xs.length + 1) (.clean r ok) (Function.update s r.src xs)
      (r.after ok) (Function.update s r.src []) := by
  induction xs with
  | nil =>
    refine StackRuns.cons (.pop rfl) ?_
    simp only [Function.update_self, List.head?_nil, List.tail_nil, Option.elim_none, Function.update_idem]
    exact .nil ..
  | cons x xs ih =>
    refine StackRuns.cons (.pop rfl) ?_
    simp only [Function.update_self, List.head?_cons, List.tail_cons, Option.elim_some,
      Function.update_idem, hd, Option.isSome_none, Bool.false_eq_true, ite_false]
    exact ih

private def pair (s : Stacks Port) (src dst : Port) (x y : List Bool) : Stacks Port :=
  Function.update (Function.update s src x) dst y

private theorem move_run (mode : Mode) (r : Route) (ok : Bool) (dst : Port)
    (hd : r.dst = some dst) (hne : r.src ≠ dst) (s : Stacks Port) (xs ys : List Bool) :
    StackRuns (recordCode mode) (2*xs.length+1) (.clean r ok) (pair s r.src dst xs ys)
      (r.after ok) (pair s r.src dst [] (xs.reverse ++ ys)) := by
  have getSrc (a b : List Bool) : pair s r.src dst a b r.src = a := by simp [pair, hne]
  have getDst (a b : List Bool) : pair s r.src dst a b dst = b := by simp [pair]
  have setSrc (a b c : List Bool) : Function.update (pair s r.src dst a b) r.src c =
      pair s r.src dst c b := by simp only [pair]; rw [Function.update_comm hne.symm, Function.update_idem]
  have setDst (a b c : List Bool) : Function.update (pair s r.src dst a b) dst c =
      pair s r.src dst a c := by simp [pair]
  induction xs generalizing ys with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, List.reverse_nil, List.nil_append]
    refine StackRuns.cons (.pop rfl) ?_
    simp only [getSrc, List.head?_nil, List.tail_nil, Option.elim_none, setSrc]
    exact .nil ..
  | cons x xs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    refine StackRuns.cons (.pop rfl) ?_
    simp only [getSrc, List.head?_cons, List.tail_cons, Option.elim_some, setSrc,
      hd, Option.isSome_some, ite_true]
    refine StackRuns.cons (.push rfl) ?_
    simp only [hd, Option.getD_some, getDst, setDst]
    exact ih (x :: ys)

private theorem discard_bank (mode : Mode) (r : Route) (ok : Bool) (hd : r.dst = none) (s : Bank) :
    StackRuns (recordCode mode) ((s.stacks r.src).length+1) (.clean r ok) s.stacks
      (r.after ok) (s.update r.src []).stacks := by
  simpa only [Function.update_eq_self, Bank.update_stacks] using discard_run mode r ok hd s.stacks (s.stacks r.src)

private theorem move_bank (mode : Mode) (r : Route) (ok : Bool) (dst : Port)
    (hd : r.dst = some dst) (hne : r.src ≠ dst) (s : Bank) :
    StackRuns (recordCode mode) (2*(s.stacks r.src).length+1) (.clean r ok) s.stacks
      (r.after ok) ((s.update r.src []).update dst ((s.stacks r.src).reverse ++ s.stacks dst)).stacks := by
  simpa only [pair, Function.update_eq_self, Bank.update_stacks] using
    move_run mode r ok dst hd hne s.stacks (s.stacks r.src) (s.stacks dst)

private theorem emit_run (mode : Mode) (ok : Bool) (b : Bank) :
    StackRuns (recordCode mode) 1 (.emit ok) b.stacks .done {b with valid := ok :: b.valid}.stacks := by
  refine StackRuns.cons (.push rfl) ?_
  rw [Bank.update_stacks]; exact .nil ..

/-- Isolate two records, leaving the supplied tails and destination history
untouched until they are needed. -/
def ready {w : ℕ} (a b : RawSlot w) (s : Bank) : Bank :=
  {s with left := Boundary.recordBytes a ++ s.left, right := Boundary.recordBytes b ++ s.right,
          width := List.replicate w true, widthBack := [], savedLeft := [], savedRight := [], tmp := []}

/-- A clean return bank with the new validity bit. The caller may latch
this bit or reject as soon as it is false. -/
def returned (w : ℕ) (s : Bank) (ok : Bool) (bytes : List Bool) : Bank :=
  {s with width := List.replicate w true, widthBack := [], savedLeft := [], savedRight := [], tmp := [],
          next := bytes ++ s.next, valid := ok :: s.valid}

private def saved {w : ℕ} (a b : RawSlot w) (s : Bank) : Bank :=
  {s with width := List.replicate w true, widthBack := [], savedLeft := (Boundary.recordBytes a).reverse,
          savedRight := (Boundary.recordBytes b).reverse, tmp := []}

private theorem scan_saved (mode : Mode) {w : ℕ} (a b : RawSlot w) (s : Bank) :
    StackRuns (recordCode mode) (5*(8*w+3)) entry (ready a b s).stacks
      (cleanup mode (expected a b)) (saved a b s).stacks := by
  simpa only [ready,saved,List.append_nil] using
    record_run mode a b {s with savedLeft := [], savedRight := [], tmp := []}

private theorem returning (mode : Mode) (k : ℕ) (s t : Bank)
    (h : StackRuns (recordCode mode) k entry s.stacks .done t.stacks) :
    (routine mode).Runs k s.stacks t.stacks := by
  apply FiniteRoutine.runs_ofStackCode_framed (ports := id) Function.injective_id
    (normal := fun q ↦ decide (q = State.done)) (entry := entry) (exit := .done)
    (by rfl) (by rfl) (fun q hq ↦ by obtain rfl := of_decide_eq_true hq; rfl) h
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  exact fun j hj ↦ (hj j rfl).elim

/-- Verifying an outgoing slot compares all five raw words and rejects
noncanonical records through the returned bit. No input values affect its clock. -/
theorem verify_runs {w : ℕ} (a b : RawSlot w) (s : Bank) :
    verify.Runs (50*w+18) (ready a b s).stacks (returned w s (verifyOK a b) []).stacks := by
  let ok := verifyOK a b
  let start := saved a b s
  let x := start.update .savedLeft []
  let y := x.update .savedRight []
  have h₀ := scan_saved .verify a b s
  have h₁ := discard_bank .verify .verifyLeft ok rfl start
  have h₂ := discard_bank .verify .verifyRight ok rfl x
  have h₃ := emit_run .verify ok y
  have hh := h₀.trans (h₁.trans (h₂.trans h₃))
  simp only [Route.src, start, x, saved, Bank.update, Bank.stacks, List.length_reverse,
    Boundary.length_recordBytes] at hh
  apply returning
  convert hh using 1 <;> first | rfl | omega

private theorem select_left {w : ℕ} (keepMin ok : Bool) (a b : RawSlot w) (s : Bank) :
    StackRuns (recordCode (.select keepMin)) (25*w+4) (.clean (.discardOther true) ok) (saved a b s).stacks
      .done (returned w s ok (Boundary.recordBytes a).reverse).stacks := by
  let mode := Mode.select keepMin
  let start := saved a b s
  let x := start.update .savedRight []
  let y := (x.update .savedLeft []).update .tmp ((x.stacks .savedLeft).reverse ++ x.stacks .tmp)
  let z := (y.update .tmp []).update .next ((y.stacks .tmp).reverse ++ y.stacks .next)
  have hd := discard_bank mode (.discardOther true) ok rfl start
  have hm := move_bank mode (.saved true) ok .tmp rfl (by decide) x
  have hn := move_bank mode .staged ok .next rfl (by decide) y
  have he := emit_run mode ok z
  have hh := hd.trans (hm.trans (hn.trans he))
  simp only [start,x,y,z,saved,Bank.update,Bank.stacks,Route.src,ite_true,List.length_reverse,
    List.reverse_reverse,List.append_nil,Boundary.length_recordBytes] at hh
  convert hh using 1 <;> first | rfl | omega

private theorem select_right {w : ℕ} (keepMin ok : Bool) (a b : RawSlot w) (s : Bank) :
    StackRuns (recordCode (.select keepMin)) (25*w+4) (.clean (.discardOther false) ok) (saved a b s).stacks
      .done (returned w s ok (Boundary.recordBytes b).reverse).stacks := by
  let mode := Mode.select keepMin
  let start := saved a b s
  let x := start.update .savedLeft []
  let y := (x.update .savedRight []).update .tmp ((x.stacks .savedRight).reverse ++ x.stacks .tmp)
  let z := (y.update .tmp []).update .next ((y.stacks .tmp).reverse ++ y.stacks .next)
  have hd := discard_bank mode (.discardOther false) ok rfl start
  have hm := move_bank mode (.saved false) ok .tmp rfl (by decide) x
  have hn := move_bank mode .staged ok .next rfl (by decide) y
  have he := emit_run mode ok z
  have hh := hd.trans (hm.trans (hn.trans he))
  simp only [start,x,y,z,saved,Bank.update,Bank.stacks,Route.src,Bool.false_eq_true,ite_false,
    List.length_reverse,List.reverse_reverse,List.append_nil,Boundary.length_recordBytes] at hh
  convert hh using 1 <;> first | rfl | omega

/-- Select the comparator output and append its reversed five-word encoding
to the backward destination block. All scratch stacks are empty on return. -/
theorem select_runs {w : ℕ} (keepMin : Bool) (a b : RawSlot w) (s : Bank) :
    (select keepMin).Runs (65*w+19) (ready a b s).stacks
      (returned w s (selectOK a b) (Boundary.recordBytes (chosen keepMin a b)).reverse).stacks := by
  apply returning
  rw [show 65*w+19 = 5*(8*w+3)+(25*w+4) by omega]
  apply (scan_saved (.select keepMin) a b s).trans
  by_cases h : (leDecision (expected a b) == keepMin) = true
  · simpa [cleanup,h,chosen,selectOK] using select_left keepMin (selectOK a b) a b s
  · have hf := Bool.eq_false_iff.mpr h
    simpa [cleanup,hf,chosen,selectOK] using select_right keepMin (selectOK a b) a b s

end RAMTape.Sorter

end VPVNP
end Computability
end OAI
