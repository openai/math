import OAI.Computability.VPVNP.RAMTapeWordSimple
import OAI.Computability.VPVNP.RAMTapeStackLift

/-!
# Comparing the successor cost with its cap

The cost and the cap arrive least-significant bit first. Subtracting the cap
with an initial borrow of one tests whether the cost is at most the cap.
Each pair of popped bits is saved and later returned to its original stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorCap

open TapeWord BurstRAM

/-- Control states for subtracting the cap with an initial borrow, restoring both operands, and
reporting whether the cost fits. -/
inductive State where
  | left (borrow : Bool)
  | right (borrow x : Bool)
  | saveLeft (borrow x y : Bool)
  | saveRight (borrow y : Bool)
  | restore (borrow : Bool)
  | takeRight (borrow x : Bool)
  | putLeft (borrow x y : Bool)
  | putRight (borrow y : Bool)
  | done (withinCap : Bool)
  | reject
  deriving DecidableEq, Fintype

/-- The scratch ports `.tmp` and `.out` save the left and right inputs. -/
def code : StackCode ScanPort State
  | .left c => .pop .left fun b => b.elim (.restore c) (.right c)
  | .right c x => .pop .right fun b => b.elim .reject fun y => .saveLeft (subBit c x y).2 x y
  | .saveLeft c x y => .push .tmp x (.saveRight c y)
  | .saveRight c y => .push .out y (.left c)
  | .restore c => .pop .tmp fun b => b.elim (.done c) (.takeRight c)
  | .takeRight c x => .pop .out fun b => b.elim .reject (.putLeft c x)
  | .putLeft c x y => .push .left x (.putRight c y)
  | .putRight c y => .push .right y (.restore c)
  | .done _ => .halt true
  | .reject => .halt false

private theorem update_stacks (x y t u word : List Bool) (k : ScanPort) :
    Function.update (scanStacks x y t u) k word = match k with
      | .left => scanStacks word y t u
      | .right => scanStacks x word t u
      | .tmp => scanStacks x y word u
      | .out => scanStacks x y t word := by
  funext j; cases k <;> cases j <;> simp [scanStacks]

local macro "cap_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [scanStacks, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, update_stacks])

private theorem save_run (c : Bool) (x y t u : List Bool) (hlen : x.length = y.length) :
    StackRuns code (4 * x.length + 1) (.left c) (scanStacks x y t u)
      (.restore (subScan c x y).2) (scanStacks [] [] (x.reverse ++ t) (y.reverse ++ u)) := by
  induction x generalizing c y t u with
  | nil =>
    have hy := List.length_eq_zero_iff.mp hlen.symm
    subst y
    cap_step
    exact .nil ..
  | cons x xs ih =>
    cases y with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
        List.singleton_append, subScan, scan]
      cap_step
      cap_step
      cap_step
      cap_step
      exact ih _ _ _ _ (Nat.succ.inj hlen)

private theorem restore_run (c : Bool) (x y t u : List Bool) (hlen : t.length = u.length) :
    StackRuns code (4 * t.length + 1) (.restore c) (scanStacks x y t u)
      (.done c) (scanStacks (t.reverse ++ x) (u.reverse ++ y) [] []) := by
  induction t generalizing x y u with
  | nil =>
    have hu := List.length_eq_zero_iff.mp hlen.symm
    subst u
    cap_step
    exact .nil ..
  | cons a t ih =>
    cases u with
    | nil => simp at hlen
    | cons b u =>
      simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      cap_step
      cap_step
      cap_step
      cap_step
      exact ih _ _ _ (Nat.succ.inj hlen)

/-- Exactly eight stack instructions per bit and two empty pops. The final
state holds the unsigned comparison and all four stacks have their entry values. -/
theorem run (x y : List Bool) (hlen : x.length = y.length) :
    StackRuns code (8 * x.length + 2) (.left true) (scanStacks x y [] [])
      (.done (decide (value x ≤ value y))) (scanStacks x y [] []) := by
  have hb : (subScan true x y).2 = decide (value x ≤ value y) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.toNat_true, Nat.lt_succ_iff, decide_eq_true_eq] using
      subScan_borrow (c := true) hlen
  have hf := save_run true x y [] [] hlen
  have hr := restore_run (subScan true x y).2 [] [] x.reverse y.reverse (by simpa)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse, hb] at hf hr
  convert hf.trans hr using 1
  omega

theorem word_run {w : ℕ} (cost cap : Word w) :
    StackRuns code (8 * w + 2) (.left true) (scanStacks (wordBits cost) (wordBits cap) [] [])
      (.done (decide (cost.val ≤ cap.val))) (scanStacks (wordBits cost) (wordBits cap) [] []) := by
  simpa only [length_wordBits, value_wordBits] using run (wordBits cost) (wordBits cap) (by simp)

/-- A caller can use any four distinct ports. The entire caller stack bank
is restored, and the caller can use the terminal flag to select its continuation. -/
theorem run_lift {K Q : Type*} [DecidableEq K] {target : StackCode K Q}
    (ports : ScanPort → K) (hp : Function.Injective ports) (labels : State → Q)
    (rows : ∀ q, (code q).returns = false → target (labels q) = (code q).rename ports labels)
    (s : Stacks K) (hlen : (s (ports .left)).length = (s (ports .right)).length)
    (ht : s (ports .tmp) = []) (hu : s (ports .out) = []) :
    StackRuns target (8 * (s (ports .left)).length + 2) (labels (.left true)) s
      (labels (.done (decide (value (s (ports .left)) ≤ value (s (ports .right)))))) s := by
  have he := installStacks_eq hp s (scanStacks (s (ports .left)) (s (ports .right)) [] [])
    (by intro k; cases k <;> first | rfl | exact ht | exact hu)
  simpa only [he] using (run _ _ hlen).lift ports hp labels s rows

end RAMTape.SuccessorCap

end VPVNP
end Computability
end OAI
