import OAI.Computability.NearSquareRoot.PhysicalWalshNode

/-! # Range guards at the actual recursive Walsh inputs

For a terminal piece, each quadruple in each pair of spectator positions has
to fit the four accumulators. At a recursive node the mix and scale guards
apply only at instructions actually reached by the template; the child guard
recurses on the particular lane resulting from all preceding instructions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code KernelPass PhysicalWalsh PhysicalWalshGrid

variable {a W : ℕ} (hW : 0 < W) (p : Plan (a+1) W W)

def baseGuard (s : Shape) (x : Data s) : Prop :=
  ∀ g : Fin s.pref, ∀ b : Fin s.suff, PhysicalWalshBase.FitsGroup
    (fun j => x ((g.val*4 + j.val)*s.suff + b.val))

def goodWith : ℕ → (s : Shape) → Data s → Prop
  | 0, s, x => baseGuard s x
  | j+1, s, x =>
    Ready (nodeOps hW p) (guards (coords a W) Shape.w (fun _ _ _ => True)
      (fun axis v => goodWith j (descend (a+1) W axis v))) p s (lane (a+1) W s x)

/-- The numeric feasibility condition for all arrays generated on one run. -/
def Good (s : Shape) (x : Data s) : Prop := goodWith hW p s.level s x

def nodeGuards : Guards (a+1) (layout (coords a W) Shape.w) := guards (coords a W) Shape.w (fun _ _ _ => True)
  (fun axis s => Good hW p (descend (a+1) W axis s))

private theorem guard_congr {U H R : Type} {l : Layout U H R} {A i o : ℕ}
    (f : Ops A l) (G G' : Guards A l) (u : U)
    (agree : ∀ {i o} (p : Plan A i o) (x : Rows l u i), isLeaf p = true → (G p u x ↔ G' p u x))
    (q : Plan A i o) (x : Rows l u i) : Ready f G q u x ↔ Ready f G' q u x := by
  induction q with
  | mix c => exact agree (.mix c) x rfl
  | xor g => exact agree (.xor g) x rfl
  | scale n t c => exact agree (.scale n t c) x rfl
  | child axis => exact agree (.child axis) x rfl
  | seq p q hp hq => exact and_congr (hq _) (hp _)
  | parallel p q hp hq => exact and_congr (hp _) (hq _)

theorem good_base {s : Shape} {x : Data s} (hs : s.level=0) (hg : Good hW p s x) : baseGuard s x := by
  simpa only [Good, hs, goodWith] using hg

theorem good_step {s : Shape} {x : Data s} (hs : 0 < s.level) (hg : Good hW p s x) :
    Ready (nodeOps hW p) (nodeGuards hW p) p s (lane (a+1) W s x) := by
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  simp only [Good, hj, goodWith] at hg
  apply (guard_congr _ _ _ s _ p _).mp hg
  intro i o t y leaf
  cases t with
  | mix _ | xor _ | scale _ _ _ => rfl
  | child axis => simp only [nodeGuards, guards, Good, descend, hj, Nat.succ_sub_one]
  | seq _ _ | parallel _ _ => cases leaf

theorem good_of_step {s : Shape} {x : Data s} (hs : 0 < s.level)
    (ready : Ready (nodeOps hW p) (nodeGuards hW p) p s (lane (a+1) W s x)) : Good hW p s x := by
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  simp only [Good, hj, goodWith]
  apply (guard_congr _ _ _ s _ p _).mp ready
  intro i o t y leaf
  cases t with
  | mix _ | xor _ | scale _ _ _ => rfl
  | child axis => simp only [nodeGuards, guards, Good, descend, hj, Nat.succ_sub_one]
  | seq _ _ | parallel _ _ => cases leaf

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
