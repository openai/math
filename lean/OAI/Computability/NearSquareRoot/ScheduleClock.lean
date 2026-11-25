import OAI.Computability.NearSquareRoot.ShortWordSpace
import OAI.Computability.NearSquareRoot.Specification
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic

/-!
# Interpreter budget clock

The clock uses two binary stacks compiled by P192’s two-step physical tape simulation.
The second stack first carries the unary exponent. The first stack then stores the
little-endian integer one less than the remaining number of ticks. Crossing a zero
moves one marker to the second stack. Rewind restores one bit at a time. Underflow
signals expiration, including when the clock has zero bits (a budget of one).
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ScheduleClock

open IntegerMultiplication

inductive State
  | initialize | ready | borrow | writeZero | rewind | expired
  deriving DecidableEq

instance : Fintype State :=
  ⟨{.initialize, .ready, .borrow, .writeZero, .rewind, .expired}, by
    intro q
    cases q <;> simp⟩

/-- `false` is the binary stack, `true` the unary exponent/rewind stack. -/
def pair {α : Type*} (x y : α) : Bool → α
  | false => x
  | true => y

def cfg (q : State) (bits scratch : List Bool) : SM.Config Bool State Bool :=
  ⟨q, pair bits scratch⟩

def rule : SM.Rule Bool State Bool
  | .initialize, top =>
    match top true with
    | some _ => some (.initialize, pair (.push true) .pop)
    | none => some (.ready, pair .skip .skip)
  | .ready, _ => some (.borrow, pair .skip .skip)
  | .borrow, top =>
    match top false with
    | some false => some (.borrow, pair .pop (.push true))
    | some true => some (.writeZero, pair .pop .skip)
    | none => some (.expired, pair .skip .skip)
  | .writeZero, _ => some (.rewind, pair (.push false) .skip)
  | .rewind, top =>
    match top true with
    | some _ => some (.rewind, pair (.push true) .pop)
    | none => some (.ready, pair .skip .skip)
  | .expired, _ => none

abbrev Step := SM.advance rule
abbrev PhysicalRule := SM.toTM rule

private theorem step_eq (q q' : State) (x y x' y' : List Bool) (a b : SM.Action Bool)
    (h : rule q (SM.tops (cfg q x y)) = some (q', pair a b))
    (hx : a.perform x = x') (hy : b.perform y = y') :
    Step (cfg q x y) = some (cfg q' x' y') := by
  unfold Step SM.advance
  change Option.map _ (rule q _) = _
  rw [h]
  simp only [Option.map_some, Option.some.injEq]
  change SM.Config.mk q' _ = SM.Config.mk q' _
  congr 1
  funext i
  cases i
  · exact hx
  · exact hy

private theorem init_aux (s b : List Bool) :
    Trace Step (cfg .initialize b s) (s.length + 1)
      (cfg .ready (List.replicate s.length true ++ b) []) := by
  induction s generalizing b with
  | nil => exact Trace.single (step_eq _ _ _ _ _ _ .skip .skip rfl rfl rfl)
  | cons x s ih =>
    have h := Trace.cons
      (step_eq .initialize .initialize b (x :: s) (true :: b) s
        (.push true) .pop rfl rfl rfl) (ih (true :: b))
    simpa [List.replicate_succ', Nat.add_comm, Nat.add_left_comm] using h

/-- Initializing reads one exponent marker per step. -/
theorem initialize_run (exponent : List Bool) :
    Trace Step (cfg .initialize [] exponent) (exponent.length + 1)
      (cfg .ready (List.replicate exponent.length true) []) := by
  simpa using init_aux exponent []

private theorem rewind_aux (k : ℕ) (x : List Bool) :
    Trace Step (cfg .rewind x (List.replicate k true)) (k + 1)
      (cfg .ready (List.replicate k true ++ x) []) := by
  induction k generalizing x with
  | zero => exact Trace.single (step_eq _ _ _ _ _ _ .skip .skip rfl rfl rfl)
  | succ k ih =>
    rw [List.replicate_succ]
    have h := Trace.cons
      (step_eq .rewind .rewind x (true :: List.replicate k true)
        (true :: x) (List.replicate k true) (.push true) .pop rfl rfl rfl)
      (ih (true :: x))
    have e : true :: List.replicate k true = List.replicate k true ++ [true] :=
      (List.replicate_succ ..).symm.trans (List.replicate_succ' ..)
    simpa only [e, List.append_assoc, List.singleton_append, Nat.add_comm 1] using h

private theorem borrow_aux (k : ℕ) (x scratch : List Bool) :
    Trace Step (cfg .borrow (List.replicate k false ++ x) scratch) k
      (cfg .borrow x (List.replicate k true ++ scratch)) := by
  induction k generalizing scratch with
  | zero => exact Trace.nil _
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    have h := Trace.cons
      (step_eq .borrow .borrow (false :: (List.replicate k false ++ x)) scratch
        (List.replicate k false ++ x) (true :: scratch) .pop (.push true) rfl rfl rfl)
      (ih (true :: scratch))
    simpa [List.replicate_succ', Nat.add_comm] using h

/-- A successful tick traverses the initial string of zero bits and rewinds across it. -/
theorem tick (k : ℕ) (x : List Bool) :
    Trace Step (cfg .ready (List.replicate k false ++ true :: x) []) (2*k + 4)
      (cfg .ready (List.replicate k true ++ false :: x) []) := by
  let b := List.replicate k false ++ true :: x
  let t := List.replicate k true
  have h₁ := Trace.single (step_eq .ready .borrow b [] b [] .skip .skip rfl rfl rfl)
  have h₂ : Trace Step (cfg .borrow b []) k (cfg .borrow (true :: x) t) := by
    simpa [b, t] using borrow_aux k (true :: x) []
  have h₃ := Trace.single
    (step_eq .borrow .writeZero (true :: x) t x t .pop .skip rfl rfl rfl)
  have h₄ := Trace.single
    (step_eq .writeZero .rewind x t (false :: x) t (.push false) .skip rfl rfl rfl)
  convert (((h₁.trans h₂).trans h₃).trans h₄).trans (rewind_aux k (false :: x)) using 1
  omega

/-- The final tick of a clock with `k` bits signals expiration. -/
theorem timeout (k : ℕ) :
    Trace Step (cfg .ready (List.replicate k false) []) (k+2)
      (cfg .expired [] (List.replicate k true)) := by
  let b := List.replicate k false
  let t := List.replicate k true
  have h₁ := Trace.single (step_eq .ready .borrow b [] b [] .skip .skip rfl rfl rfl)
  have h₂ : Trace Step (cfg .borrow b []) k (cfg .borrow [] t) := by
    simpa [b, t] using borrow_aux k [] []
  have h₃ := Trace.single (step_eq .borrow .expired [] t [] t .skip .skip rfl rfl rfl)
  convert (h₁.trans h₂).trans h₃ using 1
  omega

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * value bs + b.toNat

theorem zero_value (b : List Bool) (hb : value b = 0) :
    b = List.replicate b.length false := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    cases x
    · simp [value] at hb
      simpa only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and] using ih (by omega)
    · simp [value] at hb

private theorem decompose_nonzero (b : List Bool) (hb : 0 < value b) :
    ∃ k x, b = List.replicate k false ++ true :: x := by
  induction b with
  | nil => simp [value] at hb
  | cons q xs ih =>
    cases q
    · obtain ⟨k,x,e⟩ := ih (by simpa [value] using hb)
      exact ⟨k+1, x, by rw [List.replicate_succ]; simp [e]⟩
    · exact ⟨0, xs, rfl⟩

private theorem pred_value (k : ℕ) (x : List Bool) :
    value (List.replicate k true ++ false :: x) + 1 =
      value (List.replicate k false ++ true :: x) := by
  induction k with
  | zero => simp [value]
  | succ k ih =>
    rw [List.replicate_succ, List.replicate_succ]
    simp only [List.cons_append, value, Bool.toNat_true, Bool.toNat_false, Nat.add_zero]
    omega

private theorem tick_potential (k : ℕ) (x : List Bool) :
    2*k + 4 + 2 * (List.replicate k true ++ false :: x).count false =
      6 + 2 * (List.replicate k false ++ true :: x).count false := by
  simp [List.count_replicate]
  omega

/-- For an arbitrary prefix the potential is twice the number of zero bits.
This pays for both outward and return motion on a borrow run. -/
theorem ticks (v : ℕ) (b : List Bool) (hb : v ≤ value b) :
    ∃ t b', Trace Step (cfg .ready b []) t (cfg .ready b' []) ∧
      b'.length = b.length ∧ value b' + v = value b ∧
      t + 2*b'.count false ≤ 6*v + 2*b.count false := by
  induction v generalizing b with
  | zero => exact ⟨0, b, Trace.nil _, rfl, by omega, by omega⟩
  | succ v ih =>
    obtain ⟨k,x,rfl⟩ := decompose_nonzero b (by omega)
    have hv := pred_value k x
    have hc := tick_potential k x
    obtain ⟨t,b',ht,hlen,hval,htime⟩ :=
      ih (List.replicate k true ++ false :: x) (by omega)
    refine ⟨2*k+4+t, b', (tick k x).trans ht, ?_, by omega, by omega⟩
    simpa using hlen

theorem initial_value (a : ℕ) :
    value (List.replicate a true) + 1 = 2^a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [pow_succ, List.replicate_succ]; simp [value]; omega

private def mass (x : SM.Config Bool State Bool) : ℕ :=
  (x.stack false).length + (x.stack true).length + if x.pc = .writeZero then 1 else 0

private theorem mass_step {x y : SM.Config Bool State Bool} (h : Step x = some y) :
    mass y = mass x := by
  obtain ⟨q,f⟩ := x
  cases q <;> cases h₁ : f false <;> cases h₂ : f true <;>
    simp [Step, SM.advance, SM.tops, rule, h₁, h₂] at h <;>
    first
    | (subst y; simp [mass, SM.perform, pair, SM.Action.perform, h₁, h₂] <;> omega)
    | skip
  case borrow.cons.nil b bs =>
    cases b <;> simp at h <;> subst y <;>
      simp [mass, SM.perform, pair, SM.Action.perform, h₁, h₂]
  case borrow.cons.cons b bs c cs =>
    cases b <;> simp at h <;> subst y <;>
      simp [mass, SM.perform, pair, SM.Action.perform, h₁, h₂] <;> omega

private theorem mass_trace {x y : SM.Config Bool State Bool} {n : ℕ} (r : Trace Step x n y) :
    mass y = mass x := by
  induction r with
  | nil => rfl
  | cons h _ ih => exact ih.trans (mass_step h)

/-- All prefixes of the compiled clock occupy at most two intervals of `a+3` cells
each, with fixed bottoms set by the input tape positions. -/
theorem physical_space {e : List Bool} {y : SM.Config Bool State Bool} {n : ℕ}
    (r : Trace Step (cfg .initialize [] e) n y) (T : Bool → TM.Tape (Option Bool))
    (hf : SM.faithful (cfg .initialize [] e).stack T) :
    VisitsAtMost PhysicalRule ⟨.inl .initialize,T⟩ (2*n) (2*(e.length+3)) := by
  let bottom (i : Bool) := (T i).pos + (((cfg .initialize [] e).stack i).length : ℤ)
  let cells := (Finset.univ (α := Bool) ×ˢ Finset.range (e.length + 3)).image
    (fun p : Bool × ℕ => (p.1, bottom p.1 - e.length - 1 + p.2))
  refine ⟨cells, Finset.card_image_le.trans ?_, ?_⟩
  · simp
  intro t ht z hz i
  have space {k u} (_ : k ≤ n) (h : Trace Step (cfg .initialize [] e) k u) :
      (u.stack i).length ≤ e.length := by
    have M := mass_trace h
    simp [mass, cfg, pair] at M
    cases i <;> omega
  have ⟨l,h⟩ := stack_fence r T hf i e.length space ht hz
  change bottom i - e.length - 1 ≤ (z.tape i).pos at l
  change (z.tape i).pos ≤ bottom i + 1 at h
  let offset := (z.tape i).pos - (bottom i - e.length - 1)
  have hoff : 0 ≤ offset := by dsimp [offset]; omega
  refine Finset.mem_image.mpr ⟨(i,offset.toNat), Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · apply Finset.mem_range.mpr
    dsimp [offset]
    omega
  · simp only [Int.toNat_of_nonneg hoff, Prod.mk.injEq, true_and]
    dsimp [offset]
    omega

/-- From unary exponent input, any strict prefix of the budget completes within
linear time in the exponent plus completed ticks, including machine initialization. -/
theorem physical_prefix (e : List Bool) (v : ℕ) (hv : v < 2^e.length)
    (T : Bool → TM.Tape (Option Bool)) (hf : SM.faithful (cfg .initialize [] e).stack T) :
    ∃ t b' T', Trace (TM.advance PhysicalRule) ⟨.inl .initialize,T⟩ t ⟨.inl .ready,T'⟩ ∧
      SM.faithful (cfg .ready b' []).stack T' ∧ b'.length = e.length ∧
      value b' + v + 1 = 2^e.length ∧ t ≤ 2*(e.length + 1 + 6*v) ∧
      VisitsAtMost PhysicalRule ⟨.inl .initialize,T⟩ t (2*(e.length+3)) := by
  have hval := initial_value e.length
  obtain ⟨t,b',ht,hlen,hv',htime⟩ := ticks v (List.replicate e.length true) (by omega)
  obtain ⟨T',hf',hm⟩ := SM.simulate ((initialize_run e).trans ht) T hf
  refine ⟨_,b',T',hm,hf',by simpa using hlen,by omega,?_,physical_space ((initialize_run e).trans ht) T hf⟩
  simp [List.count_replicate] at htime
  omega

/-- The `2^a`-th requested tick reaches the expired physical control state. -/
theorem physical_expiration (e : List Bool) (T : Bool → TM.Tape (Option Bool))
    (hf : SM.faithful (cfg .initialize [] e).stack T) :
    ∃ t T', Trace (TM.advance PhysicalRule) ⟨.inl .initialize,T⟩ t ⟨.inl .expired,T'⟩ ∧
      TM.advance PhysicalRule ⟨.inl .expired,T'⟩ = none ∧
      t ≤ 2*(e.length + 1 + 6*2^e.length) ∧
      VisitsAtMost PhysicalRule ⟨.inl .initialize,T⟩ t (2*(e.length+3)) := by
  let b := List.replicate e.length true
  have hval : value b + 1 = 2^e.length := initial_value _
  obtain ⟨t,b',ht,hlen,hv,htime⟩ := ticks (value b) b (le_refl _)
  have hval' : value b' = 0 := by omega
  have hlen' : b'.length = e.length := by simpa [b] using hlen
  have hb' := (zero_value b' hval').trans (congrArg (List.replicate · false) hlen')
  rw [hb'] at ht htime
  have hc := ((initialize_run e).trans ht).trans (timeout e.length)
  obtain ⟨T',hf',hm⟩ := SM.simulate hc T hf
  refine ⟨_,T',hm,SM.simulate_halt (m := rule) (x := cfg .expired [] (List.replicate e.length true)) rfl hf',?_,physical_space hc T hf⟩
  simp [List.count_replicate,b] at htime
  dsimp [b] at hval ⊢
  omega

end ScheduleClock

end NearSquareRoot
end Computability
end OAI
