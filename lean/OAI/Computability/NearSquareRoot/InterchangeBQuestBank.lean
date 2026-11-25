import OAI.Computability.NearSquareRoot.InterchangeBQuestPack

/-!
# Collecting bounded recursive calls into a finite bank

A collector copies its source, runs both branches, and retains the first
output while computing the second. The size of each retained tree is
accounted for by its `Alive` certificate. Recursive time charges add
across the branches.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom

namespace BHop

variable {I Y A B : Type} {job : Job Y} {r : Regime I} {N l : I → ℕ}
    {zone : I → Y → Prop} {p q v : I → Tree} {h k : ℤ}

private theorem exchange (hp : Alive r N l p) (hq : Alive r N l q) :
    Rip r N l (together p q) (together q p) :=
  let s := Rip.split (Rip.alivePair hp hq)
  s.2.twice s.1

/-- Run on the second subtree, accounting for the first subtree's space. -/
theorem right (a : BHop job r N l zone h p q)
    (v : I → Tree) (hv : Alive r N l v) (hp : Alive r N l p) (hq : Alive r N l q) :
    BHop job r N l zone h (together v p) (together v q) :=
  ((a.pack v hv).preceded (exchange hv hp)).afterTask (exchange hq hv)

/-- Compute two outputs from one input. The second branch retains the first
result on its parked deck. -/
theorem doubleg (a : BHop job r N l zone h p q) (b : BHop job r N l zone k p v)
    (hp : Alive r N l p) (hq : Alive r N l q) (hv : Alive r N l v) :
    BHop job r N l zone (h+k) p (together q v) :=
  ((a.pack p hp).seam (b.right q hq hp hv)).preceded (hp.twice hp)

/-- Collect independently computed rows, summing their recursive call limits.
The accumulating bank has bounded size at each branch. -/
theorem finite [Fintype B] (out : Series B) (cost : B → ℤ) (y : I → B → Tree)
    (row : ∀ b, BHop job r N l zone (cost b) p (fun i => y i b))
    (hp : Alive r N l p) (hy : ∀ b, Alive r N l (fun i => y i b)) :
    BHop job r N l zone (∑ b, cost b) p (stackRun (fun _ => out) y) := by
  classical
  have build : ∀ s : List B, s.Nodup →
      Alive r N l (fun i => Task.forest (y i) s) ∧
        BHop job r N l zone (s.toFinset.sum cost) p (fun i => Task.forest (y i) s) := by
    intro s hs
    induction s with
    | nil =>
      have empty : Rip r N l p (fun i => Task.forest (y i) []) := by
        obtain ⟨d, run⟩ := hp
        exact ⟨d, fixture run.out run.budget _⟩
      exact ⟨empty.idle, by simpa only [List.toFinset_nil, Finset.sum_empty] using
        (tarry empty : BHop job r N l zone 0 _ _)⟩
    | cons b s ih =>
      obtain ⟨hb, hn⟩ := List.nodup_cons.mp hs
      obtain ⟨alive, collected⟩ := ih hn
      refine ⟨Rip.alivePair (hy b) alive, ?_⟩
      simpa only [Task.forest_cons, together, List.toFinset_cons,
        Finset.sum_insert (show b ∉ s.toFinset by simpa using hb)] using
        (row b).doubleg collected hp (hy b) alive
  have all : out.explore.toFinset = Finset.univ := by ext; simp [out.complete]
  unfold stackRun
  simp_rw [stripe_simple]
  simpa only [all] using (build out.explore out.nodup).2

/-- Run two stages with the same header. Its copy is retained during the
first stage, then paired with the intermediate bank. -/
theorem sequence {s : I → Tree} (pos : ∀ i, 1 ≤ N i)
    (hp : Alive r N l p) (hq : Alive r N l q)
    (first : BHop job r N l zone h (together r.header p) q)
    (next : BHop job r N l zone k (together r.header q) s) :
    BHop job r N l zone (h+k) (together r.header p) s := by
  have hh := Drive.started (r:=r) (l:=l) pos
  have step := (tarry (Drive.fetch pos hp)).doubleg first (Rip.alivePair hh hp) hh hq
  simpa only [Int.zero_add] using step.seam next

/-- Select an arbitrary source row for each output. A selector may repeat
a row. The collection spends exactly the sum of the individual budgets. -/
theorem collect [Fintype B] (pos : ∀ i, 1 ≤ N i) (rows : Series A) (out : Series B)
    (x : I → A → Tree) (y : I → B → Tree) (sel : B → A) (cost : B → ℕ)
    (hx : ∀ a, Alive r N l (fun i => x i a)) (hy : ∀ b, Alive r N l (fun i => y i b))
    (row : ∀ b, BHop job r N l zone (cost b) (together r.header (fun i => x i (sel b)))
      (fun i => y i b)) :
    BHop job r N l zone (∑ b, (cost b : ℤ)) (together r.header (stackRun (fun _ => rows) x))
      (stackRun (fun _ => out) y) := by
  have ha := Fatigue.entire rows x pos hx
  have hh := Drive.started (r:=r) (l:=l) pos
  apply finite out _ _ _ (Rip.alivePair hh ha) hy
  intro b
  exact (row b).preceded ((Fatigue.drill rows x ha (sel b)).right hh)

end BHop
end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
