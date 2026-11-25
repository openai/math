import OAI.ThreeFlat.Routing.SpillLinks
import OAI.ThreeFlat.Concentrator.Greedy
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Local bits checking a deterministic greedy matching

Only the contenders for a public candidate can report that it is occupied.
There is a constant number of inspected bits per left slot for bounded degree.
-/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.Spill
open Concentrator

variable {L R F : Type*} [Fintype L] [LinearOrder L] [Fintype R] [LinearOrder R]

private abbrev Around (N : L → Finset R) (i : L) := Σ r : N i, Contenders N r.val
private abbrev GreedyPort (N : L → Finset R) (i : L) := Option (Around N i)

private def own {N : L → Finset R} {i : L} (r : N i) : Contenders N r.val := ⟨i,r.property⟩

private def greedyWire (N : L → Finset R) (i : L) :
    GreedyPort N i → L ⊕ Candidate N
  | none => .inl i
  | some ⟨r,j⟩ => .inr ⟨j.val,⟨r.val,j.property⟩⟩

private def greedyTest (N : L → Finset R) (i : L) (b : GreedyPort N i → Bool) : Prop :=
  let available := (N i).attach.filter fun r =>
    ∀ j : Contenders N r.val, j.val < i → b (some ⟨r,j⟩) = false
  let winner := if b none then if h : available.Nonempty then some (available.min' h) else none
    else none
  ∀ r : N i, b (some ⟨r, own r⟩) = decide (winner = some r)

/-- Choose the least free primary port, using only the selections of earlier
contenders on the same candidate ports. -/
def greedyNetwork [Zero F] [One F] (N : L → Finset R) : BitNetwork F (Fintype.card L) :=
  LocalChecks.network (GreedyPort N) (greedyWire N) (greedyTest N)

def greedyCheck [Zero F] [One F] (N : L → Finset R) : BitNetwork F (Fintype.card (L ⊕ Candidate N)) :=
  LocalChecks.exposed (GreedyPort N) (greedyWire N) (greedyTest N)

def available (N : L → Finset R) (h : Candidate N → Bool) (i : L) : Finset (N i) :=
  (N i).attach.filter fun r => ∀ j : Contenders N r.val, j.val < i →
    h ⟨j.val,⟨r.val,j.property⟩⟩ = false

def winner (N : L → Finset R) (x : L → Bool) (h : Candidate N → Bool) (i : L) :
    Option (N i) :=
  if x i then if ht : (available N h i).Nonempty then some ((available N h i).min' ht)
    else none else none

omit [Fintype R] in
theorem greedyTest_iff (N : L → Finset R) (x : L → Bool) (h : Candidate N → Bool) (i : L) :
    greedyTest N i (Sum.elim x h ∘ greedyWire N i) ↔
      ∀ r : N i, h ⟨i,r⟩ = decide (winner N x h i = some r) := by
  rfl

def PrimaryValid (N : L → Finset R) (x : L → Bool) (h : Candidate N → Bool) :=
  ∀ (i : L) (r : N i), h ⟨i,r⟩ = decide (winner N x h i = some r)

omit [Fintype R] in
theorem greedyCheck_eval [CommSemiring F] (N : L → Finset R) (x : L → Bool)
    (h : Candidate N → Bool) :
    TypedWiring.value (greedyCheck (F := F) N) (Sum.elim x h) =
      if PrimaryValid N x h then 1 else 0 := by
  rw [greedyCheck,LocalChecks.exposed_value]
  congr 1

omit [Fintype R] in
/-- The local certificate has a unique extension for every activity mask. -/
theorem existsUnique_greedy_bits [WellFoundedLT L] (N : L → Finset R) (x : L → Bool) :
    ∃! h : Candidate N → Bool, LocalChecks.Accepts (GreedyPort N) (greedyWire N) (greedyTest N) x h := by
  let body (i : L) (prev : ∀ j : L, j < i → N j → Bool) : N i → Bool := fun r =>
    let prior (z : Candidate N) := if hz : z.1 < i then prev z.1 hz z.2 else false
    decide (winner N x prior i = some r)
  let row : ∀ i : L, N i → Bool := wellFounded_lt.fix body
  let canon (z : Candidate N) := row z.1 z.2
  have agree (a b : Candidate N → Bool) (i : L) (hab : ∀ z : Candidate N, z.1 < i → a z = b z) :
      winner N x a i = winner N x b i := by
    have eqn : available N a i = available N b i := by
      ext r
      simp only [available,Finset.mem_filter,Finset.mem_attach,true_and]
      exact forall_congr' (fun j => forall_congr' (fun hj => congrArg (· = false)
        (hab ⟨j.val,⟨r.val,j.property⟩⟩ hj) |> Iff.of_eq))
    simp only [winner,eqn]
  have row_spec (i : L) (r : N i) : canon ⟨i,r⟩ = decide (winner N x canon i = some r) := by
    change wellFounded_lt.fix body i r = _
    rw [wellFounded_lt.fix_eq]
    dsimp only [body]
    apply congrArg (fun sel : Option (N i) => decide (sel = some r))
    apply agree
    intro j hj
    simp [hj,canon,row]
    rfl
  refine ⟨canon, fun i => (greedyTest_iff N x canon i).2 (row_spec i), ?_⟩
  intro h hh
  have H (i : L) : ∀ r : N i, h ⟨i,r⟩ = canon ⟨i,r⟩ := by
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro r
      rw [(greedyTest_iff N x h i).1 (hh i) r,row_spec,
        agree h canon i (fun z hz => ih z.1 hz z.2)]
  exact funext (fun z => H z.1 z.2)

omit [Fintype R] in
theorem existsUnique_primaryValid [WellFoundedLT L] (N : L → Finset R) (x : L → Bool) :
    ∃! h, PrimaryValid N x h := by
  have iff' (h : Candidate N → Bool) :
      LocalChecks.Accepts (GreedyPort N) (greedyWire N) (greedyTest N) x h ↔ PrimaryValid N x h :=
    forall_congr' (greedyTest_iff N x h)
  obtain ⟨h,ok,only⟩ := existsUnique_greedy_bits N x
  exact ⟨h,(iff' h).1 ok,fun g hg => only g ((iff' g).2 hg)⟩

omit [Fintype R] in
theorem greedyNetwork_cells [Zero F] [One F] (N : L → Finset R) (D : ℕ)
    (right : ∀ r, Fintype.card (Contenders N r) ≤ D) (left : ∀ i, (N i).card ≤ D) :
    (greedyNetwork (F := F) N).cells ≤ Fintype.card L *
      (2^(D*D+1)*(D*D+3)) := by
  have bound (i : L) : Fintype.card (Around N i) ≤ D*D := by
    calc
      _ = ∑ r : N i, Fintype.card (Contenders N r.val) := Fintype.card_sigma
      _ ≤ ∑ _ : N i, D := Finset.sum_le_sum (fun r _ => right r.val)
      _ ≤ _ := by simpa using Nat.mul_le_mul_right D (left i)
  apply LocalChecks.cells_le (F := F) (d := D*D+1) (GreedyPort N) (greedyWire N) (greedyTest N)
  intro i
  simpa [GreedyPort] using Nat.add_le_add_right (bound i) 1

end ThreeFlat.Routing.Spill

end
end OAI
