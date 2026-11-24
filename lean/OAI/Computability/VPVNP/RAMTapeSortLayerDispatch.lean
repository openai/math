import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-! # Choosing the local or cross-site sorting layer

A layer with stride exponent `j` uses the incident stream precisely when
the site holds `2^h` rows and `h ≤ j`. The finite control compares the unary
exponents before any stream is split. It removes one mark from each exponent
per round and saves the number of rounds above a delimiter. It restores the
two exponents and consumes the delimiter before entering the selected branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortLayerDispatch

/-- Unary block-width and stride exponents together with the scratch stack used to compare and
restore them before layer dispatch. -/
inductive Port where
  | width | stride | tmp
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

private inductive Phase where
  | start | scanWidth | scanStride | save | undoWidth
  | restore (cross : Bool) | putWidth (cross : Bool) | putStride (cross : Bool)
  | report (cross : Bool) | done
  deriving DecidableEq, Fintype

private def code : StackCode Port Phase
  | .start => .push .tmp false .scanWidth
  | .scanWidth => .pop .width fun b => b.elim (.restore true) (fun _ => .scanStride)
  | .scanStride => .pop .stride fun b => b.elim .undoWidth (fun _ => .save)
  | .save => .push .tmp true .scanWidth
  | .undoWidth => .push .width true (.restore false)
  | .restore b => .pop .tmp fun mark => if mark = some true then .putWidth b else .report b
  | .putWidth b => .push .width true (.putStride b)
  | .putStride b => .push .stride true (.restore b)
  | .report b => .push .tmp b .done
  | .done => .halt true

private abbrev marks (n : ℕ) := List.replicate n true

private def bank (width stride tmp : List Bool) : Stacks Port
  | .width => width
  | .stride => stride
  | .tmp => tmp

private theorem set_bank (w j t v : List Bool) (p : Port) :
    Function.update (bank w j t) p v = match p with
      | .width => bank v j t
      | .stride => bank w v t
      | .tmp => bank w j v := by
  funext k
  cases p <;> cases k <;> rfl

local macro "dispatch_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [bank, set_bank, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, Bool.false_ne_true,
    Option.some.injEq, ↓reduceIte])

private theorem scan_pairs (n h j : ℕ) (tmp : List Bool) :
    StackRuns code (3*n) .scanWidth (bank (marks (h+n)) (marks (j+n)) tmp)
      .scanWidth (bank (marks h) (marks j) (marks n ++ tmp)) := by
  induction n generalizing tmp with
  | zero => exact .nil ..
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_succ, Nat.add_succ]
    change StackRuns _ _ _ (bank (true :: marks (h+n)) (true :: marks (j+n)) tmp) _ _
    dispatch_step
    dispatch_step
    dispatch_step
    simpa only [marks, List.replicate_succ', List.append_assoc, List.singleton_append]
      using ih (true :: tmp)

private theorem restore_pairs (b : Bool) (n h j : ℕ) (tmp : List Bool) :
    StackRuns code (3*n+2) (.restore b)
      (bank (marks h) (marks j) (marks n ++ false :: tmp))
      .done (bank (marks (h+n)) (marks (j+n)) (b :: tmp)) := by
  induction n generalizing h j with
  | zero =>
    change StackRuns _ 2 _ (bank _ _ (false :: tmp)) _ _
    dispatch_step
    dispatch_step
    exact .nil ..
  | succ n ih =>
    rw [Nat.mul_succ, show 3*n+3+2 = (3*n+2)+1+1+1 by omega]
    change StackRuns _ _ _ (bank _ _ (true :: (marks n ++ false :: tmp))) _ _
    dispatch_step
    dispatch_step
    dispatch_step
    simpa only [marks, List.replicate_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using ih (h+1) (j+1)

private theorem scan_cross (h d : ℕ) (tmp : List Bool) :
    StackRuns code (6*h+4) .start (bank (marks h) (marks (d+h)) tmp)
      .done (bank (marks h) (marks (d+h)) (true :: tmp)) := by
  have pairs := scan_pairs h 0 d (false :: tmp)
  have restore := restore_pairs true h 0 d tmp
  simp only [Nat.zero_add] at pairs restore
  have finish : StackRuns code ((3*h+2)+1) .scanWidth
      (bank [] (marks d) (marks h ++ false :: tmp)) .done
      (bank (marks h) (marks (d+h)) (true :: tmp)) := by
    dispatch_step
    exact restore
  rw [show 6*h+4 = (3*h + ((3*h+2)+1))+1 by omega]
  dispatch_step
  exact pairs.trans finish

private theorem scan_local (j d : ℕ) (tmp : List Bool) :
    StackRuns code (6*j+6) .start (bank (marks (d+1+j)) (marks j) tmp)
      .done (bank (marks (d+1+j)) (marks j) (false :: tmp)) := by
  have pairs := scan_pairs j (d+1) 0 (false :: tmp)
  have restore := restore_pairs false j (d+1) 0 tmp
  simp only [Nat.zero_add] at pairs restore
  have finish : StackRuns code ((3*j+2)+1+1+1) .scanWidth
      (bank (true :: marks d) [] (marks j ++ false :: tmp)) .done
      (bank (marks (d+1+j)) (marks j) (false :: tmp)) := by
    dispatch_step
    dispatch_step
    dispatch_step
    exact restore
  rw [show 6*j+6 = (3*j + ((3*j+2)+1+1+1))+1 by omega]
  dispatch_step
  exact pairs.trans finish

variable {K : Type}

private def test (ports : Port → K) : FiniteRoutine K :=
  FiniteRoutine.ofStackCode code ports .start (· == .done)

private def branch (tmp : K) (cross sameSite : FiniteRoutine K) : FiniteRoutine K :=
  .ofRoutine (Routine.popCase tmp (Routine.halt false) sameSite.body cross.body)

/-- The branch callback receives the full caller store, with both exponents
and the previous contents of the temporary stack restored. -/
def routine (ports : Port → K) (cross sameSite : FiniteRoutine K) : FiniteRoutine K :=
  (test ports).followedBy (branch (ports .tmp) cross sameSite)

variable [DecidableEq K]

private theorem test_runs (ports : Port → K) (hp : Function.Injective ports)
    {h j n : ℕ} {b : Bool} (s : Stacks K) (hh : s (ports .width) = marks h)
    (hj : s (ports .stride) = marks j)
    (run : StackRuns code n .start (bank (marks h) (marks j) (s (ports .tmp)))
      .done (bank (marks h) (marks j) (b :: s (ports .tmp)))) :
    (test ports).Runs n s (Function.update s (ports .tmp) (b :: s (ports .tmp))) := by
  apply FiniteRoutine.runs_ofStackCode_framed hp (normal := (· == .done)) rfl rfl
    (fun q e => by simp only [beq_iff_eq] at e; subst q; rfl) run
  · intro p
    cases p <;> first | assumption | rfl
  · intro p
    cases p <;> simp [hp.eq_iff, bank, hh, hj]
  · intro k hk
    exact Function.update_of_ne (hk .tmp).symm ..

/-- Cross-site stride, including the equality boundary. -/
theorem cross_runs (ports : Port → K) (hp : Function.Injective ports)
    (cross sameSite : FiniteRoutine K) {s out : Stacks K} {h j t : ℕ}
    (hh : s (ports .width) = List.replicate h true)
    (hj : s (ports .stride) = List.replicate j true) (hc : h ≤ j)
    (hr : cross.Runs t s out) :
    (routine ports cross sameSite).Runs (6*h+5+t) s out := by
  have scan := scan_cross h (j-h) (s (ports .tmp))
  rw [Nat.sub_add_cancel hc] at scan
  have first := test_runs ports hp s hh hj scan
  let mid := Function.update s (ports .tmp) (true :: s (ports .tmp))
  have pick : (branch (ports .tmp) cross sameSite).Runs (t+1) mid out := by
    apply Routine.runs_popCase_true (ports .tmp) (Routine.halt false) sameSite.body cross.body (s := mid)
      (Function.update_self ..)
    simpa only [mid, Function.update_idem, Function.update_eq_self] using hr
  rw [show 6*h+5+t = (6*h+4)+(t+1) by omega]
  exact first.followedBy pick

/-- Strides strictly below the site's row width use its materialized block. -/
theorem local_runs (ports : Port → K) (hp : Function.Injective ports)
    (cross sameSite : FiniteRoutine K) {s out : Stacks K} {h j t : ℕ}
    (hh : s (ports .width) = List.replicate h true)
    (hj : s (ports .stride) = List.replicate j true) (hl : j < h)
    (hr : sameSite.Runs t s out) :
    (routine ports cross sameSite).Runs (6*j+7+t) s out := by
  have scan := scan_local j (h-j-1) (s (ports .tmp))
  rw [show h-j-1+1+j = h by omega] at scan
  have first := test_runs ports hp s hh hj scan
  let mid := Function.update s (ports .tmp) (false :: s (ports .tmp))
  have pick : (branch (ports .tmp) cross sameSite).Runs (t+1) mid out := by
    apply Routine.runs_popCase_false (ports .tmp) (Routine.halt false) sameSite.body cross.body (s := mid)
      (Function.update_self ..)
    simpa only [mid, Function.update_idem, Function.update_eq_self] using hr
  rw [show 6*j+7+t = (6*j+6)+(t+1) by omega]
  exact first.followedBy pick

end RAMTape.SortLayerDispatch

end VPVNP
end Computability
end OAI
