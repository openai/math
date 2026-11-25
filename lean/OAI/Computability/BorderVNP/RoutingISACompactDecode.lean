import OAI.Computability.BorderVNP.CellFieldDecoder
import OAI.Computability.BorderVNP.CellFragments

/-!
# Decoding a word-padded private bitstream

Each payload bit is preceded by a one tag. A zero tag terminates the payload,
after which every remaining bit must be zero. The decoder reverses the payload
onto one private stack while it reads, then restores the original order on the
destination. A truncated tag or a nonzero padding bit leads to a rejecting halt.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactFrame

open VPVNP.RAMTape CellMacro.Generator

/-- Tagged data bits with a mandatory zero terminator. -/
abbrev frameBits := CellMacro.FieldDecoder.frame

/-- A fixed set of parser and output labels. -/
inductive Phase where
  | tag | digit | save (b : Bool) | padding | restore | emit (b : Bool) | reject
  deriving DecidableEq, Fintype

variable {K : Type} [DecidableEq K]

private def routine (src dst : K) : Routine (K ⊕ Unit) Phase where
  entry := .tag
  code
    | .tag => .pop (.inl src) fun
      | none => some .reject
      | some true => some .digit
      | some false => some .padding
    | .digit => .pop (.inl src) fun b => some (b.elim .reject Phase.save)
    | .save b => .push (.inr ()) b (some .tag)
    | .padding => .pop (.inl src) fun
      | none => some .restore
      | some false => some .padding
      | some true => some .reject
    | .restore => .pop (.inr ()) fun b => b.map Phase.emit
    | .emit b => .push (.inl dst) b (some .restore)
    | .reject => .halt false

/-- A returning fixed-control decoder with one private bit stack. -/
def decode (src dst : K) : Fragment K where
  Scratch := Unit
  body := .ofRoutine (routine src dst)

private def bank (s : Stacks K) (src dst : K) (input output back : List Bool) : Stacks (K ⊕ Unit) :=
  Sum.elim (Function.update (Function.update s src input) dst output) (fun _ => back)

private theorem at_src (s : Stacks K) {src dst : K} (hd : src ≠ dst) (i o b : List Bool) :
    bank s src dst i o b (.inl src) = i := by simp [bank, hd]

private theorem at_dst (s : Stacks K) (src dst : K) (i o b : List Bool) :
    bank s src dst i o b (.inl dst) = o := by simp [bank, -Sum.elim_update_left]

private theorem at_back (s : Stacks K) (src dst : K) (i o b : List Bool) :
    bank s src dst i o b (.inr ()) = b := rfl

private theorem set_src (s : Stacks K) {src dst : K} (hd : src ≠ dst) (i o b x : List Bool) :
    Function.update (bank s src dst i o b) (.inl src) x = bank s src dst x o b := by
  funext p
  rcases p with k | u
  · by_cases h : k = src <;> by_cases j : k = dst <;> simp_all [bank, -Sum.elim_update_left]
  · simp [bank, -Sum.elim_update_left]

private theorem set_dst (s : Stacks K) (src dst : K) (i o b x : List Bool) :
    Function.update (bank s src dst i o b) (.inl dst) x = bank s src dst i x b := by
  funext p
  rcases p with k | u
  · by_cases h : k = dst <;> simp [bank, h, -Sum.elim_update_left]
  · simp [bank, -Sum.elim_update_left]

private theorem set_back (s : Stacks K) (src dst : K) (i o b x : List Bool) :
    Function.update (bank s src dst i o b) (.inr ()) x = bank s src dst i o x := by
  funext p
  rcases p with k | ⟨⟩ <;> simp [bank, -Sum.elim_update_left]

section

variable (s : Stacks K) {src dst : K} (hd : src ≠ dst)

local notation "M" => Routine.standalone (routine src dst)
local notation "B" => bank s src dst

local macro "decode_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp (disch := assumption) only [at_src, at_dst, at_back, set_src, set_dst, set_back,
    List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
    Option.elim_none, Option.elim_some, Option.map_none, Option.map_some])

include hd in
private theorem scan (payload suffix out back : List Bool) :
    StackRuns M (3*payload.length) (some .tag) (B (frameBits payload ++ suffix) out back)
      (some .tag) (B (false :: suffix) out (payload.reverse ++ back)) := by
  induction payload generalizing back with
  | nil => exact .nil ..
  | cons bit rest ih =>
    rw [List.length_cons, Nat.mul_succ, show 3*rest.length + 3 = 3*rest.length+1+1+1 by omega]
    simp only [frameBits, CellMacro.FieldDecoder.frame, List.cons_append, List.reverse_cons,
      List.append_assoc]
    decode_step
    decode_step
    decode_step
    exact ih _

include hd in
private theorem zeros (pad : ℕ) (suffix out back : List Bool) :
    StackRuns M pad (some .padding) (B (List.replicate pad false ++ suffix) out back)
      (some .padding) (B suffix out back) := by
  induction pad with
  | zero => exact .nil ..
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    decode_step
    exact ih

private theorem restore (back out : List Bool) :
    StackRuns M (2*back.length+1) (some .restore) (B [] out back) none
      (B [] (back.reverse ++ out) []) := by
  induction back generalizing out with
  | nil =>
    simp only [List.length_nil, mul_zero, zero_add, List.reverse_nil, List.nil_append]
    decode_step
    exact .nil ..
  | cons b bs ih =>
    rw [List.length_cons, Nat.mul_succ, show 2*bs.length+2+1 = (2*bs.length+1)+1+1 by omega]
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    decode_step
    decode_step
    exact ih _

private theorem startBank (s : Stacks K) (src dst : K) :
    (decode src dst).bank s = bank s src dst (s src) (s dst) [] := by
  simp [decode, bank, Fragment.bank]

/-- The decoder consumes the entire source, writes the payload in original order
and empties its scratch. All public stacks outside the two indicated ports retain
their original contents. The clock is exact, including the two empty-stack checks. -/
theorem decode_run {src dst : K} (different : src ≠ dst) (payload : List Bool) (pad : ℕ)
    (s : Stacks K) (input : s src = frameBits payload ++ List.replicate pad false)
    (empty : s dst = []) :
    (decode src dst).Runs (5*payload.length + pad + 3) s
      (Function.update (Function.update s src []) dst payload) := by
  have read := scan s different payload (List.replicate pad false) [] []
  rw [List.append_nil] at read
  have stop : StackRuns (routine src dst).standalone 1 (some .tag)
      (bank s src dst (false :: List.replicate pad false) [] payload.reverse) (some .padding)
      (bank s src dst (List.replicate pad false) [] payload.reverse) := by
    decode_step
    exact .nil ..
  have padding := zeros s different pad [] [] payload.reverse
  rw [List.append_nil] at padding
  have done : StackRuns (routine src dst).standalone 1 (some .padding)
      (bank s src dst [] [] payload.reverse) (some .restore) (bank s src dst [] [] payload.reverse) := by
    decode_step
    exact .nil ..
  have copy := restore s (src := src) (dst := dst) payload.reverse []
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at copy
  have all := (((read.trans stop).trans padding).trans done).trans copy
  rw [show 5*payload.length+pad+3 = 3*payload.length+1+pad+1+(2*payload.length+1) by omega]
  change StackRuns (routine src dst).standalone _ _ ((decode src dst).bank s) _ _
  rw [startBank, input, empty]
  exact all


include hd in
private theorem bad_padding (bits out back : List Bool)
    (bad : ¬ ∃ pad, bits = List.replicate pad false) :
    ∃ t ≤ bits.length, ∃ u, StackRuns M t (some .padding) (B bits out back) (some .reject) u := by
  induction bits with
  | nil => exact (bad ⟨0, rfl⟩).elim
  | cons bit bits ih =>
    cases bit with
    | false =>
      obtain ⟨t, ht, u, run⟩ := ih (by
        rintro ⟨n, rfl⟩
        exact bad ⟨n+1, List.replicate_succ.symm⟩)
      refine ⟨t+1, by simpa using ht, u, ?_⟩
      decode_step
      exact run
    | true =>
      refine ⟨1, by simp, B bits out back, ?_⟩
      decode_step
      exact .nil ..

include hd in
private theorem bad_tags (bits out back : List Bool)
    (bad : ¬ ∃ payload pad, bits = frameBits payload ++ List.replicate pad false) :
    ∃ t ≤ 2*bits.length+1, ∃ u, StackRuns M t (some .tag) (B bits out back) (some .reject) u := by
  match bits with
  | [] =>
    refine ⟨1, by simp, B [] out back, ?_⟩
    decode_step
    exact .nil ..
  | false :: tail =>
    obtain ⟨t, ht, u, run⟩ := bad_padding s hd tail out back (by
      rintro ⟨n, rfl⟩
      exact bad ⟨[], n, rfl⟩)
    refine ⟨t+1, by simp only [List.length_cons]; omega, u, ?_⟩
    decode_step
    exact run
  | [true] =>
    refine ⟨2, by decide, B [] out back, ?_⟩
    decode_step
    decode_step
    exact .nil ..
  | true :: b :: tail =>
    obtain ⟨t, ht, u, run⟩ := bad_tags tail out (b :: back) (by
      rintro ⟨payload, n, rfl⟩
      exact bad ⟨b :: payload, n, rfl⟩)
    refine ⟨t+1+1+1, by simp only [List.length_cons]; omega, u, ?_⟩
    decode_step
    decode_step
    decode_step
    exact run

/-- Every malformed source reaches an actual rejecting instruction in linear time.
The destination and other caller stacks may contain arbitrary data at entry. -/
theorem decode_rejects {src dst : K} (different : src ≠ dst) (s : Stacks K)
    (bad : ¬ ∃ payload pad, s src = frameBits payload ++ List.replicate pad false) :
    ∃ t ≤ 2*(s src).length+1, ∃ q u,
      StackRuns (decode src dst).body.body.standalone t (some (decode src dst).body.body.entry)
        ((decode src dst).bank s) (some q) u ∧ (decode src dst).body.body.code q = .halt false := by
  obtain ⟨t, ht, u, run⟩ := bad_tags s different (s src) (s dst) [] bad
  exact ⟨t, ht, .reject, u, startBank s src dst ▸ run, rfl⟩

end

private theorem step_eq {K Q : Type*} [DecidableEq K] {C : StackCode K Q} {q s q₁ s₁ q₂ s₂}
    (a : StackStep C q s q₁ s₁) (b : StackStep C q s q₂ s₂) : q₁ = q₂ ∧ s₁ = s₂ := by
  cases a <;> cases b <;> simp_all

private theorem halt_eq {K Q : Type*} [DecidableEq K] {C : StackCode K Q} {n k q s q₁ s₁ q₂ s₂ x y}
    (a : StackRuns C n q s q₁ s₁) (b : StackRuns C k q s q₂ s₂)
    (hx : C q₁ = .halt x) (hy : C q₂ = .halt y) : q₁ = q₂ := by
  induction a generalizing k with
  | nil =>
    cases b with
    | nil => rfl
    | cons hs _ => cases hs <;> simp_all
  | cons step _ ih =>
    cases b with
    | nil => cases step <;> simp_all
    | cons step' tail =>
      obtain ⟨rfl, rfl⟩ := step_eq step step'
      exact ih tail hx


/-- The decoder returns normally on precisely the tagged strings with a terminator
and all-zero padding. -/
theorem decode_returns_iff {src dst : K} (different : src ≠ dst) (s : Stacks K) (empty : s dst = []) :
    (∃ t u, (decode src dst).Runs t s u) ↔
      ∃ payload pad, s src = frameBits payload ++ List.replicate pad false := by
  constructor
  · rintro ⟨k, u, ret⟩
    by_contra bad
    obtain ⟨_, _, q, _, run, halted⟩ := decode_rejects different s bad
    have impossible : some q = none := halt_eq run ret halted rfl
    contradiction
  · rintro ⟨payload, pad, input⟩
    exact ⟨_, _, decode_run different payload pad s input empty⟩

end RoutingISA.CompactFrame

end BorderVNP
end Computability
end OAI
