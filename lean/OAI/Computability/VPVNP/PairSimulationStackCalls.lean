import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Data.Fintype.Card

/-!
# Exact branch streams of a bounded bit-stack call

A stack call consumes one supplied bit at each binary choice. A halting
instruction returns its status, stack bank, remaining instruction fuel and
unused suffix. Section 13 can therefore run the next local test on the same
stream. The complete accepted words form a finite set of cardinality exactly
the bounded accepting path count of the stack code.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.StackMachine

open RAMTape

variable {K Q : Type*} [DecidableEq K]

/-- State at a genuine halt. The final halt itself has spent one unit of fuel. -/
structure Exit (K Q : Type*) where
  /-- Boolean status of the halt reached by the bounded stack call. -/
  accept : Bool
  /-- Stack-code control state at which the halt instruction was executed. -/
  state : Q
  /-- Contents of each named bit stack when the call halted. -/
  bank : Stacks K
  /-- Suffix of the input choice stream left unconsumed at the halt. -/
  rest : List Bool
  /-- Instruction fuel remaining after charging the final halt instruction. -/
  unused : ℕ

/-- A binary choice reads one bit, including when its two successors coincide.
Running out of fuel or choices before a halt returns `none`. -/
def parse (code : StackCode K Q) : ℕ → Q → Stacks K → List Bool → Option (Exit K Q)
  | 0, _, _, _ => none
  | fuel + 1, q, s, bits =>
    match code q with
    | .push k b next => parse code fuel next (Function.update s k (b :: s k)) bits
    | .pop k next => parse code fuel (next (s k).head?) (Function.update s k (s k).tail) bits
    | .goto next => parse code fuel next s bits
    | .choose low high =>
      match bits with
      | [] => none
      | b :: more => parse code fuel (if b then high else low) s more
    | .halt b => some ⟨b, q, s, bits, fuel⟩

/-- Keep the suffix of a call which halted with the required status. -/
def haltPrefix (b : Bool) (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K)
    (bits : List Bool) : Option (List Bool) :=
  match parse code fuel q s bits with
  | none => none
  | some x => if x.accept = b then some x.rest else none

/-- Return the unused choice suffix when bounded stack execution reaches an accepting halt, and
return `none` otherwise. -/
abbrev acceptPrefix := @haltPrefix K Q _ true

private def tag (b : Bool) : List Bool ↪ List Bool :=
  ⟨List.cons b, fun _ _ h => (List.cons.inj h).2⟩

private theorem disjoint_tags (low high : Finset (List Bool)) :
    Disjoint (low.map (tag false)) (high.map (tag true)) := by
  refine Finset.disjoint_left.mpr fun word hl hh => ?_
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hl
  obtain ⟨b, _, e⟩ := Finset.mem_map.mp hh
  exact Bool.noConfusion (List.cons.inj e).1

/-- Complete streams halting with the selected status. A one-bit tag keeps
the two branch slots disjoint even when both continue at the same state. -/
def haltWords (status : Bool) (code : StackCode K Q) : ℕ → Q → Stacks K → Finset (List Bool)
  | 0, _, _ => ∅
  | fuel + 1, q, s =>
    match code q with
    | .push k b next => haltWords status code fuel next (Function.update s k (b :: s k))
    | .pop k next => haltWords status code fuel (next (s k).head?) (Function.update s k (s k).tail)
    | .goto next => haltWords status code fuel next s
    | .choose low high =>
      (haltWords status code fuel low s).map (tag false) ∪
        (haltWords status code fuel high s).map (tag true)
    | .halt b => if b = status then {[]} else ∅

/-- Finite set of exact choice words that lead from the supplied control state and stack bank
to an accepting halt within the fuel bound. -/
abbrev acceptedWords := @haltWords K Q _ true

theorem acceptedWords_card (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K) :
    (acceptedWords code fuel q s).card = stackPaths code fuel q s := by
  induction fuel generalizing q s with
  | zero => rfl
  | succ fuel ih =>
    cases hc : code q with
    | push | pop | goto => simpa only [acceptedWords, haltWords, stackPaths, hc] using ih _ _
    | choose low high =>
      simp only [acceptedWords, haltWords, stackPaths, hc, Finset.card_union_of_disjoint
        (disjoint_tags _ _), Finset.card_map]
      exact congrArg₂ (· + ·) (ih low s) (ih high s)
    | halt b => cases b <;> simp [acceptedWords, haltWords, stackPaths, hc]

private theorem tag_prefix {b : Bool} {words : Finset (List Bool)} {bits rest : List Bool} :
    (∃ pre ∈ words.map (tag b), bits = pre ++ rest) ↔
      ∃ pre ∈ words, bits = b :: (pre ++ rest) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨pre, hpre, rfl⟩ := Finset.mem_map.mp hw
    exact ⟨pre, hpre, rfl⟩
  · rintro ⟨pre, hpre, rfl⟩
    exact ⟨tag b pre, Finset.mem_map_of_mem _ hpre, rfl⟩

/-- Every accepting or rejecting halt reads exactly one complete word for
its status. The suffix can begin immediately with another stack call. -/
theorem haltPrefix_iff (status : Bool) (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K)
    (bits rest : List Bool) :
    haltPrefix status code fuel q s bits = some rest ↔
      ∃ pre ∈ haltWords status code fuel q s, bits = pre ++ rest := by
  induction fuel generalizing q s bits with
  | zero => simp [haltPrefix, parse, haltWords]
  | succ fuel ih =>
    cases hc : code q with
    | push | pop | goto => simpa only [haltPrefix, parse, haltWords, hc] using ih _ _ _
    | choose low high =>
      simp only [haltWords, hc, Finset.mem_union, or_and_right, exists_or, tag_prefix]
      cases bits with
      | nil => simp [haltPrefix, parse, hc]
      | cons b bits => cases b <;> simpa [haltPrefix, parse, hc] using ih _ s bits
    | halt b =>
      by_cases h : b = status <;> simp [haltPrefix, parse, haltWords, hc, h]

theorem acceptPrefix_iff (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K)
    (bits rest : List Bool) :
    acceptPrefix code fuel q s bits = some rest ↔
      ∃ pre ∈ acceptedWords code fuel q s, bits = pre ++ rest :=
  haltPrefix_iff true code fuel q s bits rest

/-- Distinct words accepted with an empty remaining suffix. -/
abbrev CompleteStreams (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K) :=
  {bs : List Bool // acceptPrefix code fuel q s bs = some []}

private def streamEquiv (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K) :
    CompleteStreams code fuel q s ≃ ↥(acceptedWords code fuel q s) :=
  Equiv.subtypeEquivRight fun bs => by simp [acceptPrefix_iff]

instance (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K) :
    Fintype (CompleteStreams code fuel q s) :=
  Fintype.ofEquiv _ (streamEquiv code fuel q s).symm

theorem completeStreams_card (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K) :
    Fintype.card (CompleteStreams code fuel q s) = stackPaths code fuel q s :=
  (Fintype.card_congr (streamEquiv code fuel q s)).trans <|
    (Fintype.card_coe _).trans (acceptedWords_card code fuel q s)

/-- An extension of a halted input changes only the unused suffix. In
particular, the stack bank and fuel handed to the next subroutine are the
ones obtained by running the complete consumed word in isolation. -/
theorem parse_append {code : StackCode K Q} {fuel : ℕ} {q : Q} {s : Stacks K}
    {bits : List Bool} {x : Exit K Q} (h : parse code fuel q s bits = some x)
    (more : List Bool) :
    parse code fuel q s (bits ++ more) = some {x with rest := x.rest ++ more} := by
  induction fuel generalizing q s bits with
  | zero => simp [parse] at h
  | succ fuel ih =>
    cases hc : code q with
    | push | pop | goto =>
      simpa only [parse, hc] using ih (by simpa only [parse, hc] using h)
    | choose low high =>
      cases bits with
      | nil => simp [parse, hc] at h
      | cons b bits =>
        simpa only [parse, hc, List.cons_append] using ih (by simpa only [parse, hc] using h)
    | halt status =>
      simp only [parse, hc, Option.some.injEq] at h ⊢
      subst x
      rfl

/-- Recover the complete consumed word and the exact exit configuration
from an arbitrary halted stream. -/
theorem parse_split {code : StackCode K Q} {fuel : ℕ} {q : Q} {s : Stacks K}
    {bits : List Bool} {x : Exit K Q} (h : parse code fuel q s bits = some x) :
    ∃ pre, bits = pre ++ x.rest ∧
      parse code fuel q s pre = some {x with rest := []} := by
  induction fuel generalizing q s bits with
  | zero => simp [parse] at h
  | succ fuel ih =>
    cases hc : code q with
    | push | pop | goto =>
      simpa only [parse, hc] using ih (by simpa only [parse, hc] using h)
    | choose low high =>
      cases bits with
      | nil => simp [parse, hc] at h
      | cons b bits =>
        obtain ⟨pre, e, done⟩ := ih (by simpa only [parse, hc] using h)
        exact ⟨b :: pre, congrArg (b :: ·) e, by simpa only [parse, hc] using done⟩
    | halt status =>
      simp only [parse, hc, Option.some.injEq] at h
      subst x
      exact ⟨[], rfl, by simp [parse, hc]⟩

/-- A deterministic stack segment leaves the branch stream untouched and
hands all remaining fuel to its successor. -/
theorem parse_runs {code : StackCode K Q} {n q s next out}
    (h : StackRuns code n q s next out) (fuel : ℕ) (bits : List Bool) :
    parse code (fuel + n) q s bits = parse code fuel next out bits := by
  induction h with
  | nil => rfl
  | cons hs _ ih => cases hs <;> simp_all [parse]

end PairSimulation.StackMachine

end VPVNP
end Computability
end OAI
