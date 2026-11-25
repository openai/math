import OAI.Computability.NearSquareRoot.FixedCandidateArena
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveGuard
import OAI.Computability.NearSquareRoot.FixedCandidateClock
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxDigitArenaBody

/-! # Effective protected-search candidates, including slow parameter guesses -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code Space CommonRegisters GeneratorSyntax EffectiveBoundedTask Filter
open private effective_tag effective_short from OAI.Computability.NearSquareRoot.FixedCandidateEffectiveGuard
open private input_count from OAI.Computability.NearSquareRoot.FixedCandidateGuard

variable {P : Type} [Primcodable P]

/-- The guard and ordinary finite-prefix branch keep their fixed commands.
The fast branch can have a width-dependent arena for every outer guess. -/
theorem effective_all_widths_atArena (K : P → ℕ) (hK : Computable K) (T A : P → ℕ → ℕ)
    (ha : ∀ p n, n ≤ A p n)
    (fast : Family (fun p (i : LargeInput (K p)) => T p i.val.width) (fun p i => A p i.val.width)
      (fun _ i => send i.val.operands) (fun _ i => send (Lea.answer i.val.operands))) :
    Family (fun p (i : MultiplicationInput) => i.width+T p i.width) (fun p i => 21*i.width+A p i.width)
      (fun _ i => send i.operands) (fun _ i => send (Lea.answer i.operands)) := by
  let t (p : P) (i : MultiplicationInput) := i.width + T p i.width
  let s (p : P) (i : MultiplicationInput) := 21*i.width+A p i.width
  have large := fast.on (fun p (i : longS (K p)) =>
    (⟨i.val,Nat.le_of_not_gt (of_decide_eq_false i.property)⟩ : LargeInput (K p)))
  have act := Family.control (t := t) (s := fun p (i : MultiplicationInput) => A p i.width)
    (u := fun _ (i : MultiplicationInput) => send i.operands) (v := fun _ i => send (Lea.answer i.operands))
    (fun p (i : MultiplicationInput) => tags (K p) i)
    (large.mono (fun p i => by dsimp [t]; omega) (fun _ _ => le_rfl))
    ((effective_short K).mono (fun _ _ => Nat.zero_le _) (fun p i => ha p (MultiplicationInput.width i.val)))
  change Family t s _ _
  apply Family.sequence (v := fun p (i : MultiplicationInput) => .fork (.atom (tags (K p) i)) (send i.operands))
  · exact (effective_tag K hK).mono (fun _ _ => Nat.le_add_right ..)
      (fun p i => by change i.width ≤ 21*i.width+A p i.width; omega)
  · apply act.mono (fun _ _ => le_rfl)
    intro p i
    change A p i.width + (send i.operands).count ≤ 21*i.width+A p i.width
    rw [input_count]
    have positive : 1 ≤ i.width := i.property
    omega

/-- Body files for all tuples, including every guess with superlinear space.
The proof fields impose no computability on resource coefficients or budgets. -/
structure ArenaFiles (T S : ℕ → ℕ → ℕ) where
  registers : ℕ
  positive : 0 < registers
  cmd : ℕ → Cmd
  effective : Effective ltr cmd
  bounded : ∀ j, Within registers (cmd j)
  coeff : ℕ → ℕ
  body : ∀ j, Pack.ArenaBody (cmd j) (T j) (S j) (coeff j) (fun i => Lea.answer i.operands)

def clockAt (c : Clocks) (A : ℕ → ℕ) (n : ℕ) := n + (c.total n + A n)

def arenaAt (A : ℕ → ℕ) (n : ℕ) := 21*n+A n

/-- Generate all the files without testing which tuples have good exponents or
linear tape bounds. The four transport bodies determine the files on every tuple. -/
theorem arenaFiles_of_transports (K : ℕ → ℕ) (hK : Computable K) (hN : ∀ p, 2 ≤ K p)
    (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
    (plan : ∀ p i, Plan (hv p i)) (c : ℕ → Clocks) (A : ℕ → ℕ → ℕ)
    (ha : ∀ p n, n ≤ A p n) (ops : EffectiveTransportsAt K hv plan c A) :
    Nonempty (ArenaFiles (fun p => clockAt (c p) (A p)) (fun p => arenaAt (A p))) := by
  let T p n := (c p).total n+A p n
  have big := effective_largeTask_atArena K hv plan c A T hN ha (fun _ _ => Nat.le_add_left ..)
    (fun _ _ => Nat.le_add_right ..) ops
  obtain ⟨cmd,R,ce,hR,ok⟩ := effective_all_widths_atArena K hK T A ha big
  choose coeff body using fun p => (ok p).2
  exact ⟨⟨R,hR,cmd,ce,fun p => (ok p).1,coeff,body⟩⟩

/-- A good tuple transfers its per-transport time and linear arena to its
complete guarded candidate with the same exponent. Other tuples do not enter
either bound. -/
theorem good_arena_clock (c : Clocks) (A : ℕ → ℕ) {γ : ℝ} (hγ : 0 < γ)
    (hA : ∃ L : ℕ, ∀ᶠ n in atTop, A n ≤ L*(n+1))
    (hc : ∀ clock ∈ [c.route,c.forward,c.inverse], ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n in atTop, (clock n : ℝ) ≤ C*n*logScale n^γ) :
    (∃ L : ℕ, ∀ᶠ n in atTop, arenaAt A n ≤ L*(n+1)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (clockAt c A n : ℝ) ≤ C*n*logScale n^γ := by
  obtain ⟨L,ha⟩ := hA
  obtain ⟨C,hC,ht⟩ := c.eventually_total hγ hc
  constructor
  · refine ⟨21+L,?_⟩
    filter_upwards [ha] with n h
    unfold arenaAt
    rw [Nat.add_mul]
    omega
  · refine ⟨1+C+2*L,by positivity,?_⟩
    filter_upwards [ha,ht,eventually_ge_atTop (1:ℕ),tendsto_logScale.eventually_ge_atTop 1] with n h q hn hs
    have na : A n ≤ (2*L)*n := h.trans <| calc
      L*(n+1) ≤ L*(2*n) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
    have hlin : (n:ℝ) ≤ n*logScale n^γ := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hs hγ.le)
    have scaled := mul_le_mul_of_nonneg_left hlin (show (0:ℝ) ≤ 2*L by positivity)
    have na' : (A n:ℝ) ≤ 2*(L:ℝ)*n := by exact_mod_cast na
    unfold clockAt
    push_cast
    linarith

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
