import OAI.Computability.NearSquareRoot.BoundedProductRight

/-!
# Space-bounded oracle calls on a packed pair

Both wrappers execute their supplied command in its original environment.
They can therefore surround an invocation of an ancestor command. The clock
and stack bounds of that invocation occur only once in the conclusion.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space

open IntegerMultiplication IntegerMultiplication.Code

def onFirst (cmd : Cmd) : Cmd :=
  splitRoot 0 (fun _ => .pass) (cmd.join (pack 0))

def onSecond (cmd : Cmd) : Cmd :=
  splitRoot 0 (fun _ => .pass)
    ((Code.move 0 1 2).join (cmd.join ((Code.move 1 0 2).join (pack 0))))

namespace BoundedFits

/-- Keep the second tree underneath the active input on its original stack. -/
theorem onFirst {cmd : Cmd} {env : Env} {x y z : Tree} {r : Deck} {t cap depth : ℕ}
    (h : BoundedFits env cmd (pile 0 x (pile 0 z r)) (pile 0 y (pile 0 z r)) t cap depth) :
    BoundedFits env (Space.onFirst cmd) (pile 0 (.fork x z) r) (pile 0 (.fork y z) r)
      (t+7) (cap+1) (depth+1) := by
  have start : DeckCap cap (pile 0 x (pile 0 z r)) := h.choose_spec.2.start
  have finish : DeckCap cap (pile 0 y (pile 0 z r)) := h.choose_spec.2.finish
  have body := h.mono le_rfl (Nat.le_succ cap) le_rfl
  have done_ := BoundedFits.pack y z r 0 env (depth := depth+1) finish.coverFork
  have outer := BoundedFits.pair (c := fun _ => .pass) (body.join done_ le_rfl)
    start.coverFork (Nat.succ_le_succ (Nat.zero_le _))
  exact outer.mono (by omega) le_rfl le_rfl

/-- Move the first tree to a work stack while the oracle runs on the second
tree. Each move traverses the spectator once. -/
theorem onSecond {cmd : Cmd} {env : Env} {x y z : Tree} {r : Deck} {t cap depth : ℕ}
    (h : BoundedFits env cmd (pile 0 x (pile 1 z r)) (pile 0 y (pile 1 z r)) t cap depth) :
    BoundedFits env (Space.onSecond cmd) (pile 0 (.fork z x) r) (pile 0 (.fork z y) r)
      (t + 84*z.count + 11) (cap + 43*z.count + 1) (max depth (42*z.count)+1) := by
  let peak := cap + 43*z.count + 1
  let ret := max depth (42*z.count)+1
  have start : DeckCap cap (pile 0 x (pile 1 z r)) := h.choose_spec.2.start
  have finish : DeckCap cap (pile 0 y (pile 1 z r)) := h.choose_spec.2.finish
  rw [pile_comm 0 _ r 1 _ (by decide)] at start finish
  have zstart := start.unpile.pile 0 z
  have zfinish := finish.unpile.pile 0 z
  have moveRet : 42*z.count+1 ≤ ret := Nat.succ_le_succ (le_max_right ..)
  have subRet : depth+1 ≤ ret := Nat.succ_le_succ (le_max_left ..)
  have park := BoundedFits.move (i:=0) (j:=1) (u:=2) (by decide) (by decide) z env
    (pile 0 x r) zstart (cap:=peak) (depth:=42*z.count) (by dsimp [peak]; omega) le_rfl
  have restore := BoundedFits.move (i:=1) (j:=0) (u:=2) (by decide) (by decide) z env
    (pile 0 y r) finish (cap:=peak) (depth:=42*z.count) (by dsimp [peak]; omega) le_rfl
  rw [pile_comm 1 _ r 0 _ (by decide)] at park restore
  have done_ := BoundedFits.pack z y r 0 env (cap:=peak) (depth:=ret) (zfinish.coverFork.mono (by dsimp [peak]; omega))
  have sub := h.mono le_rfl (show cap ≤ peak by dsimp [peak]; omega) le_rfl
  have body := park.join (sub.join (restore.join done_ moveRet) subRet) moveRet
  have outer := BoundedFits.pair (c := fun _ => .pass) body
    (zstart.coverFork.mono (by dsimp [peak]; omega)) (by omega)
  exact outer.mono (by omega) le_rfl le_rfl

end BoundedFits
end Space

end NearSquareRoot
end Computability
end OAI
