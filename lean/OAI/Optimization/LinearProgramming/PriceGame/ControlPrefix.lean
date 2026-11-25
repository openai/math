import OAI.Optimization.LinearProgramming.PriceGame.Computation
import OAI.Optimization.LinearProgramming.OracleSpec.PriceGame

/-! Stop a deterministic computation at its first unanswered query. The externally
persisted continuation contains the public input and a finite tape of reply bits. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

universe u v

variable {N : ℕ} {α : Type u} {β : Type v}

/-- Run along just the supplied branch, returning either the result and unconsumed
bits, or the next genuine price query. -/
def observe (p : Computation N α) (bits : List Bool) : Sum (α × List Bool) (Query N) :=
  match p with
  | .pure a => .inl (a, bits)
  | .ask q next => match bits with
    | [] => .inr q
    | b :: bs => observe (next b) bs

theorem observe_bind (p : Computation N α) (f : α → Computation N β) (bs : List Bool) :
    observe (p.bind f) bs = match observe p bs with
      | .inl (a, rest) => observe (f a) rest
      | .inr q => .inr q := by
  induction p generalizing bs with
  | pure => rfl
  | ask q next ih => cases bs with
    | nil => rfl
    | cons b bs => exact ih b bs

theorem observe_map (p : Computation N α) (f : α → β) (bs : List Bool) :
    observe (p.map f) bs = (observe p bs).map (fun v => (f v.1, v.2)) id := by
  rw [Computation.map, observe_bind]
  cases observe p bs <;> rfl

/-- Residual computations are used only in the refinement proof. None is saved in
the first-order reply tape. -/
def Pending (p : Computation N α) (bs : List Bool) (q : Query N)
    (next : Bool → Computation N α) : Prop :=
  ∀ more, observe p (bs ++ more) = observe (.ask q next) more

theorem pending_of_observe (p : Computation N α) (bs : List Bool) {q : Query N}
    (h : observe p bs = .inr q) :
    ∃ next : Bool → Computation N α, Pending p bs q next ∧
      max (next false).height (next true).height + bs.length + 1 ≤ p.height := by
  induction p generalizing bs q with
  | pure => contradiction
  | ask q₀ more ih =>
    cases bs with
    | nil =>
      have he : q₀ = q := Sum.inr.inj h
      subst q
      exact ⟨more, fun _ => rfl, by simp [Computation.height]⟩
    | cons b bs =>
      obtain ⟨k, hp, ht⟩ := ih b bs h
      refine ⟨k, (fun rest => hp rest), ?_⟩
      have hb : (more b).height ≤ max (more false).height (more true).height := by cases b <;> simp
      simp only [Computation.height, List.length_cons]
      omega

theorem observe_decides_after_height (p : Computation N α) (bs : List Bool) (hb : p.height ≤ bs.length) :
    ∃ a rest, observe p bs = .inl (a, rest) := by
  cases he : observe p bs with
  | inl v => exact ⟨v.1, v.2, rfl⟩
  | inr q =>
    obtain ⟨_,_,ht⟩ := pending_of_observe p bs he
    omega

/-- Number of decision nodes inspected in one replay, including the terminal observation. -/
def observedSteps (p : Computation N α) (bits : List Bool) : ℕ :=
  match p with
  | .pure _ => 1
  | .ask _ next => match bits with
    | [] => 1
    | b :: bs => 1 + observedSteps (next b) bs

theorem observedSteps_bound (p : Computation N α) (bs : List Bool) :
    observedSteps p bs ≤ min bs.length p.height + 1 := by
  induction p generalizing bs with
  | pure => simp [observedSteps, Computation.height]
  | ask q next ih =>
    cases bs with
    | nil => simp [observedSteps]
    | cons b bs =>
      have ht : (next b).height ≤ max (next false).height (next true).height := by cases b <;> simp
      have hs := ih b bs
      simp only [observedSteps, Computation.height, List.length_cons]
      omega

/-- The semantic input contains exactly the three public fields in the challenge. -/
structure PublicInput where
  goods : ℕ
  range : ℕ
  anchor : Fin goods
deriving DecidableEq

/-- Chronological replies are reconstructed by reversing the stored list before
each replay. A new answer is pushed in constant list time. -/
structure Tape where
  input : PublicInput
  reverseReplies : List Bool
deriving DecidableEq

abbrev PublicSolver := (i : PublicInput) → Computation i.goods Bool

def startTape : Sum PublicInput (Bool × Tape) → Tape
  | .inl i => ⟨i, []⟩
  | .inr (answer, prior) => ⟨prior.input, answer :: prior.reverseReplies⟩

def observeTape (solver : PublicSolver) (t : Tape) : Sum Bool (OracleSpec.Word × Tape) :=
  match observe (solver t.input) t.reverseReplies.reverse with
  | .inl (value, _) => .inl value
  | .inr q => .inr (OracleSpec.priceQuery q.index q.prices, t)

def dispatch (solver : PublicSolver) (event : Sum PublicInput (Bool × Tape)) :
    Sum Bool (OracleSpec.Word × Tape) := observeTape solver (startTape event)

/-- The only emitted words are precisely the price vectors at the first unanswered
node on the public prefix. No function or hidden state occurs in the saved tape. -/
theorem dispatch_query_iff (solver : PublicSolver) (event : Sum PublicInput (Bool × Tape))
    (packet : OracleSpec.Word) (carry : Tape) :
    dispatch solver event = .inr (packet, carry) ↔
      carry = startTape event ∧ ∃ q : Query carry.input.goods,
        observe (solver carry.input) carry.reverseReplies.reverse = .inr q ∧
        OracleSpec.priceQuery q.index q.prices = packet := by
  constructor
  · intro he
    unfold dispatch observeTape at he
    split at he
    · contradiction
    · rename_i q hq
      obtain ⟨hp,ht⟩ := Prod.mk.inj (Sum.inr.inj he)
      subst carry
      exact ⟨rfl, q, hq, hp⟩
  · rintro ⟨rfl,q,hq,rfl⟩
    simp [dispatch, observeTape, hq]

@[simp] theorem resume_tape_input (b : Bool) (t : Tape) :
    (startTape (.inr (b, t))).input = t.input := rfl

@[simp] theorem resume_tape_word (b : Bool) (t : Tape) :
    (startTape (.inr (b, t))).reverseReplies.reverse = t.reverseReplies.reverse ++ [b] := by
  simp [startTape]

/-- The quadratic bound counts every decision-node inspection in every replay,
including the call that returns the sign. Individual arithmetic is charged separately. -/
theorem replay_node_budget (p : Computation N α) (scripts : List (List Bool))
    (hcount : scripts.length ≤ p.height + 1) :
    (scripts.map (observedSteps p)).sum ≤ (p.height+1)^2 := by
  have each (s : List Bool) : observedSteps p s ≤ p.height+1 :=
    (observedSteps_bound p s).trans (Nat.add_le_add_right (min_le_right _ _) 1)
  have hsum : (scripts.map (observedSteps p)).sum ≤ scripts.length * (p.height+1) := by
    induction scripts with
    | nil => simp
    | cons s ss ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have ht := ih (by simpa using Nat.le_of_succ_le hcount)
      have hh := each s
      omega
  exact hsum.trans (by simpa [pow_two] using Nat.mul_le_mul_right (p.height + 1) hcount)

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
