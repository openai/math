import OAI.Computability.VPVNP.RankQueryStackBorrow
import OAI.Computability.VPVNP.RankQueryStackActivate
import OAI.Computability.VPVNP.SliceArithmeticCallClear

/-! # Preparing a child call or a completed Schur sum -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine.ScanCall

open RAMTape UniversalCountStack SliceArithmetic.CallClear

variable {K : Type} [DecidableEq K]

/-- Wire the decrement routine to the live remaining-count field, a scratch stack, and the
engine's condition port. -/
def borrowPorts (tmp : K) : Borrow.Port → Engine.Port K
  | .counter => .frame (.inl 7)
  | .scratch => .aux tmp
  | .flag => .condition

omit [DecidableEq K] in
private theorem borrowPorts_inj (tmp : K) : Function.Injective (borrowPorts tmp) := by
  intro i j h; cases i <;> cases j <;> simp_all [borrowPorts]

/-- Decrement the remaining count and signal whether the scan has exhausted its product terms. -/
def test (tmp : K) : FiniteRoutine (Engine.Port K) :=
  (FiniteRoutine.ofRoutine Borrow.body).onPorts (borrowPorts tmp)

private def livePorts : List (Engine.Port K) := (List.finRange 10).map (fun i => .frame (.inl i))

/-- Return the completed accumulator, clear the live frame fields, and signal completion of the
scan. -/
def finish (tmp : K) : FiniteRoutine (Engine.Port K) :=
  ((SuccessorFields.prependCopy (.frame (.inl 8)) .result (.aux tmp)).followedBy (cleanup livePorts)).followedBy
    (.ofRoutine (Routine.push .condition true))

private def field (k : Engine.Port K) (b : Bool) : FiniteRoutine (Engine.Port K) := .ofRoutine (Routine.push k b)

/-- Compute the left child's words, set the saved direction and select descent. -/
def descend (left : FiniteRoutine (Engine.Port K)) : FiniteRoutine (Engine.Port K) :=
  (left.followedBy (field (.frame (.inl 0)) false)).followedBy (field .condition false)

/-- Inspect the remaining count, then stage the next left child or return the completed Schur
sum. -/
def scan (tmp : K) (left : FiniteRoutine (Engine.Port K)) : FiniteRoutine (Engine.Port K) :=
  (test tmp).followedBy (.ofRoutine (Routine.popCase .condition (Routine.halt false) (descend left).body (finish tmp).body))

/-- Prepare the second child of a summand. Its suspended frame receives the
just-returned left operand before the result port is cleared. -/
def right (tmp : K) (child : FiniteRoutine (Engine.Port K)) : FiniteRoutine (Engine.Port K) :=
  ((child.followedBy (SuccessorFields.prependCopy .result (.frame (.inl 9)) (.aux tmp))).followedBy
    (clear .result)).followedBy (field (.frame (.inl 0)) true)

variable {n U Z p e w v : ℕ} {c : SliceArithmetic.Vector p e}

private def scanLive (q : Key n U Z) (counter : List Bool) (a : Scalar c) :=
  fields w [] q counter (scalar v a) []

private theorem test_general (tmp : K) (q : Key n U Z) (a : Scalar c) (fs : List (F n U Z c)) (aux : Stacks K)
    (ht : aux tmp = []) (x y : List Bool) (done : Bool) (t : ℕ)
    (h : Borrow.body.Runs t (Borrow.bank x [] []) (Borrow.bank y [] [done])) :
    (test tmp).Runs t (store (scanLive (w := w) (v := v) q x a) (history w v fs) [] [] aux)
      (store (scanLive (w := w) (v := v) q y a) (history w v fs) [done] [] aux) := by
  apply FiniteRoutine.runs_onPorts_framed _ (borrowPorts_inj tmp) h
  · intro j; cases j <;> first | rfl | exact ht
  · intro j; cases j <;> first | rfl | exact ht
  · intro j hj
    cases j with
    | frame k =>
      cases k with
      | inl i =>
        fin_cases i <;> first | rfl | exact (hj .counter rfl).elim
      | inr => rfl
    | condition => exact (hj .flag rfl).elim
    | result | aux => rfl

private theorem update_sig (l h : Data) (s r : List Bool) (aux : Stacks K) (b : List Bool) :
    Function.update (store l h s r aux) .condition b = store l h b r aux := by
  funext j; cases j with
  | frame k => cases k <;> rfl
  | _ => rfl

private theorem update_out (l h : Data) (s r : List Bool) (aux : Stacks K) (b : List Bool) :
    Function.update (store l h s r aux) .result b = store l h s b aux := by
  funext j; cases j with
  | frame k => cases k <;> rfl
  | _ => rfl

private theorem cleanup_live (l h : Data) (sig ret : List Bool) (aux : Stacks K) :
    erased livePorts (store l h sig ret aux) = store (fun _ => []) h sig ret aux := by
  funext j; cases j with
  | frame k => cases k <;> simp [erased, livePorts, store]
  | _ => simp [erased, livePorts, store]

private theorem finish_runs (tmp : K) (q : Key n U Z) (a : Scalar c) (fs : List (F n U Z c)) (aux : Stacks K)
    (ht : aux tmp = []) :
    ∃ t ≤ 5*(e*v)+10*(max 1 (max w (e*v))+1)+4,
      (finish tmp).Runs t (store (scanLive (w := w) (v := v) q [] a) (history w v fs) [] [] aux)
        (atControl w v (.returned a) fs aux [true]) := by
  let l := scanLive (w := w) (v := v) q [] a
  let h := history w v fs
  let s := store l h [] [] aux
  have copy := SuccessorFields.prependCopy_runs (Engine.Port.frame (.inl 8)) .result (.aux tmp)
    (by simp) (by simp) (by simp) s ht
  change (SuccessorFields.prependCopy _ _ _).Runs (5*(scalar v a).length+2) s
    (Function.update s .result (scalar v a ++ [])) at copy
  rw [List.append_nil, update_out, scalar_length] at copy
  obtain ⟨t, hb, erase⟩ := cleanup_runs livePorts (store l h [] (scalar v a) aux) (max 1 (max w (e*v))) (by
    intro j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    change (fields w [] q [] (scalar v a) [] i).length ≤ _
    refine Fin.cases (by simp [fields]) (fun j => ?_) i
    refine Fin.addCases (motive := fun j => (Fin.append (fun x => digits w (q.words x))
      ![[],scalar v a,[]] j).length ≤ _) (fun x : Fin 6 => ?_) (fun x : Fin 3 => ?_) j
    · simp
    · rw [Fin.append_right]; fin_cases x <;> simp)
  rw [cleanup_live] at erase
  have sig := Routine.runs_push (Engine.Port.condition : Engine.Port K) true
    (store (fun _ => []) h [] (scalar v a) aux)
  change (field .condition true).Runs 1 _ (Function.update _ .condition [true]) at sig
  rw [update_sig] at sig
  simp only [livePorts, List.length_map, List.length_finRange] at hb
  exact ⟨_, by omega, (copy.followedBy erase).followedBy sig⟩

theorem zero_runs (tmp : K) (left : FiniteRoutine (Engine.Port K)) (q : Key n U Z) (a : Scalar c)
    (fs : List (F n U Z c)) (aux : Stacks K) (ht : aux tmp = []) :
    ∃ t ≤ 3*w+5*(e*v)+10*(max 1 (max w (e*v))+1)+8,
      (scan tmp left).Runs t (atControl w v (.scan q 0 a) fs aux) (atControl w v (.returned a) fs aux [true]) := by
  have testRun := test_general (w := w) (v := v) tmp q a fs aux ht _ _ _ _ (Borrow.zero_runs w)
  obtain ⟨t, hticks, finishRun⟩ := finish_runs (w := w) (v := v) tmp q a fs aux ht
  let mid := store (scanLive (w := w) (v := v) q [] a) (history w v fs) [true] [] aux
  have branch := Routine.runs_popCase_true .condition (Routine.halt false) (descend left).body (finish tmp).body
    (s := mid) (tail := []) rfl (show (finish tmp).body.Runs t (Function.update mid .condition []) _ by
      rw [update_sig]; exact finishRun)
  exact ⟨_, by omega, FiniteRoutine.Runs.followedBy testRun (b := .ofRoutine _) branch⟩

private theorem setTag (q : Key n U Z) (tag k acc l xs : List Bool) (saved : Data)
    (sig r : List Bool) (aux : Stacks K) :
    Function.update (store (fields w tag q k acc l) saved sig r aux) (.frame (.inl 0)) xs =
      store (fields w xs q k acc l) saved sig r aux := by
  funext j
  cases j with
  | frame p => cases p with | inl i => fin_cases i <;> rfl | inr => rfl
  | _ => rfl

private theorem setLeft (q : Key n U Z) (tag k acc l xs : List Bool) (saved : Data)
    (sig r : List Bool) (aux : Stacks K) :
    Function.update (store (fields w tag q k acc l) saved sig r aux) (.frame (.inl 9)) xs =
      store (fields w tag q k acc xs) saved sig r aux := by
  funext j
  cases j with
  | frame p => cases p with | inl i => fin_cases i <;> rfl | inr => rfl
  | _ => rfl

/-- A positive loop counter prepares the left continuation and the pending child. -/
theorem succ_runs (tmp : K) (left : FiniteRoutine (Engine.Port K)) (q : Key n U Z) (k : ℕ) (a : Scalar c)
    (fs : List (F n U Z c)) (aux out : Stacks K) (ht : aux tmp = []) (hfit : k+1 < 2^w) {tc : ℕ}
    (child : left.Runs tc (store (fields w [] q (digits w k) (scalar v a) []) (history w v fs) [] [] aux)
      (store (fields w [] q (digits w k) (scalar v a) []) (history w v fs) [] [] out)) :
    ∃ t ≤ tc+4*w+7, (scan tmp left).Runs t (atControl w v (.scan q (k+1) a) fs aux)
      (store (nativeFrame w v (.left q k a)) (history w v fs) [false] [] out) := by
  obtain ⟨s,hs,dec⟩ := Borrow.succ_runs w k hfit
  have testRun := test_general (w := w) (v := v) tmp q a fs aux ht _ _ _ _ dec
  let l := fields w [] q (digits w k) (scalar v a) []
  let h := history w v fs
  have dir := Routine.runs_push (Engine.Port.frame (.inl 0) : Engine.Port K) false (store l h [] [] out)
  change (field (.frame (.inl 0)) false).Runs 1 _ (Function.update _ (.frame (.inl 0)) [false]) at dir
  rw [setTag] at dir
  have sig := Routine.runs_push (Engine.Port.condition : Engine.Port K) false
    (store (nativeFrame w v (.left q k a)) h [] [] out)
  change (field .condition false).Runs 1 _ (Function.update _ .condition [false]) at sig
  rw [update_sig] at sig
  have entry := (child.followedBy dir).followedBy sig
  let mid := store l h [false] [] aux
  have branch := Routine.runs_popCase_false .condition (Routine.halt false) (descend left).body (finish tmp).body
    (s := mid) (tail := []) rfl (show (descend left).body.Runs (tc+1+1) (Function.update mid .condition []) _ by
      rw [update_sig]; exact entry)
  exact ⟨_, by omega, FiniteRoutine.Runs.followedBy testRun (b := .ofRoutine _) branch⟩

/-- The left value changes ports while its parent's query and count are restored
for the right-child dispatcher. -/
theorem right_runs (tmp : K) (child : FiniteRoutine (Engine.Port K)) (q : Key n U Z) (k : ℕ) (acc l : Scalar c)
    (fs : List (F n U Z c)) (aux out : Stacks K) (ht : out tmp = []) {tc : ℕ}
    (dispatch : child.Runs tc (store (fields w [] q (digits w k) (scalar v acc) []) (history w v fs) [] (scalar v l) aux)
      (store (fields w [] q (digits w k) (scalar v acc) []) (history w v fs) [] (scalar v l) out)) :
    (right tmp child).Runs (tc+6*(e*v)+4)
      (store (popped w v (.left q k acc)) (history w v fs) [] (scalar v l) aux)
      (store (nativeFrame w v (.right q k acc l)) (history w v fs) [] [] out) := by
  have hp : popped w v (.left q k acc) = fields w [] q (digits w k) (scalar v acc) [] := by
    funext i; fin_cases i <;> rfl
  rw [hp]
  let h := history w v fs
  let start := store (fields w [] q (digits w k) (scalar v acc) []) h [] (scalar v l) out
  have copy := SuccessorFields.prependCopy_runs Engine.Port.result (.frame (.inl 9)) (.aux tmp)
    (by simp) (by simp) (by simp) start ht
  change (SuccessorFields.prependCopy _ _ _).Runs (5*(scalar v l).length+2) start
    (Function.update start (.frame (.inl 9)) (scalar v l ++ [])) at copy
  rw [List.append_nil, setLeft, scalar_length] at copy
  let mid := store (fields w [] q (digits w k) (scalar v acc) (scalar v l)) h [] (scalar v l) out
  have clearResult := clear_runs .result mid
  change (clear .result).Runs ((scalar v l).length+1) mid (Function.update mid .result []) at clearResult
  rw [update_out, scalar_length] at clearResult
  have tag := Routine.runs_push (Engine.Port.frame (.inl 0) : Engine.Port K) true
    (store (fields w [] q (digits w k) (scalar v acc) (scalar v l)) h [] [] out)
  change (field (.frame (.inl 0)) true).Runs 1 _ (Function.update _ (.frame (.inl 0)) [true]) at tag
  rw [setTag] at tag
  have both := ((dispatch.followedBy copy).followedBy clearResult).followedBy tag
  rw [show tc+6*(e*v)+4 = tc+(5*(e*v)+2)+(e*v+1)+1 by omega]
  exact both

end RankQuery.Stack.Engine.ScanCall

end VPVNP
end Computability
end OAI
