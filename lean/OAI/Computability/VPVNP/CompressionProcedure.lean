import OAI.Computability.VPVNP.CompressionState

/-!
# Composing exact compressor procedures

A procedure consumes a fixed number of lane coordinates and carries bounds
independent of the input widths and network order. Its execution tree
retains the exact local kernel at every substep. The position divisors
multiply under composition, as do the leading energy coefficients.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

variable {R : Type*} [CommSemiring R]

/-- Uniform cost and output bounds on an exact execution tree. -/
structure Procedure (R : Type*) [CommSemiring R] (a b k κ : ℕ) (μ : ℝ) where
  divisor_pos : 0 < κ
  gain_nonneg : 0 ≤ μ
  /-- Nonnegative coefficient multiplying the square of the input position count in the energy
  bound for every output branch. -/
  error : ℝ
  error_nonneg : 0 ≤ error
  /-- Construct the execution tree from a state with `n = k + g` lane coordinates. Every
  terminal state has degree exponent `b` and `g` lane coordinates. -/
  run (g n : ℕ) (h : n = k + g) (X : State a n) : StateExecution R b g X
  positions : ∀ g n h X (z : (run g n h X).Choices),
    X.positions = κ * ((run g n h X).finalState z).positions
  energy : ∀ g n h X (z : (run g n h X).Choices),
    ((run g n h X).finalState z).energy ≤ μ * X.energy + error * (X.positions : ℝ) ^ 2

namespace Procedure

/-- A single exact tensor substep with input-independent energy and count estimates. -/
def ofPass {a b k κ : ℕ} {μ C : ℝ} (hκ : 0 < κ) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (f : ∀ g (X : State a (k + g)), StatePass R X b g)
    (hcount : ∀ g X (i : (f g X).step.Choice), X.positions = κ * ((f g X).next i).positions)
    (henergy : ∀ g X (i : (f g X).step.Choice),
      ((f g X).next i).energy ≤ μ * X.energy + C * (X.positions : ℝ) ^ 2) :
    Procedure R a b k κ μ where
  divisor_pos := hκ
  gain_nonneg := hμ
  error := C
  error_nonneg := hC
  run g n h X := by
    subst n
    exact .more (f g X) fun i => .done ((f g X).next i)
  positions g n h X z := by
    subst n
    exact hcount g X z.1
  energy g n h X z := by
    subst n
    exact henergy g X z.1

private def stop {a g n : ℕ} (h : n = g) (X : State a n) : StateExecution R a g X := by
  cases h
  exact .done X

private theorem stop_positions {a g n : ℕ} (h : n = g) (X : State a n)
    (z : (stop (R := R) h X).Choices) : ((stop h X).finalState z).positions = X.positions := by
  cases h
  rfl

private theorem stop_energy {a g n : ℕ} (h : n = g) (X : State a n)
    (z : (stop (R := R) h X).Choices) : ((stop h X).finalState z).energy = X.energy := by
  cases h
  rfl

/-- An empty schedule preserves the entire state. -/
def id (R : Type*) [CommSemiring R] (a : ℕ) : Procedure R a a 0 1 1 where
  divisor_pos := one_pos
  gain_nonneg := zero_le_one
  error := 0
  error_nonneg := le_rfl
  run g _ h X := stop (h.trans (Nat.zero_add g)) X
  positions g _ h X z := by rw [one_mul, stop_positions (h.trans (Nat.zero_add g)) X z]
  energy g _ h X z := by
    rw [one_mul, zero_mul, add_zero, stop_energy (h.trans (Nat.zero_add g)) X z]

/-- The later step's order error is bounded by the squared original order,
since the earlier step has a positive integer position divisor. -/
def seq {a b c k l p q : ℕ} {μ ν : ℝ} (P : Procedure R a b k p μ)
    (Q : Procedure R b c l q ν) : Procedure R a c (k + l) (p * q) (ν * μ) where
  divisor_pos := Nat.mul_pos P.divisor_pos Q.divisor_pos
  gain_nonneg := mul_nonneg Q.gain_nonneg P.gain_nonneg
  error := ν * P.error + Q.error
  error_nonneg := add_nonneg (mul_nonneg Q.gain_nonneg P.error_nonneg) Q.error_nonneg
  run g n h X :=
    (P.run (l+g) n (h.trans (Nat.add_assoc k l g)) X).bind fun z =>
      Q.run g (l+g) rfl ((P.run (l+g) n (h.trans (Nat.add_assoc k l g)) X).finalState z)
  positions g n h X :=
    (P.run (l+g) n (h.trans (Nat.add_assoc k l g)) X).forall_final_bind
      (fun z => Q.run g (l+g) rfl ((P.run (l+g) n (h.trans (Nat.add_assoc k l g)) X).finalState z))
      (fun Y => X.positions = p*q*Y.positions) fun z y => by
      rw [P.positions _ _ _ X z, Q.positions _ _ _ _ y, Nat.mul_assoc]
  energy g n h X :=
    (P.run (l+g) n (h.trans (Nat.add_assoc k l g)) X).forall_final_bind
      (fun z => Q.run g (l+g) rfl ((P.run (l+g) n (h.trans (Nat.add_assoc k l g)) X).finalState z))
      (fun Y => Y.energy ≤ ν*μ*X.energy + (ν*P.error + Q.error) * (X.positions : ℝ)^2)
      fun z y => by
      let M := (P.run (l+g) n (h.trans (Nat.add_assoc k l g)) X).finalState z
      have hM := P.energy _ _ _ X z
      have hc : M.positions ≤ X.positions := by
        rw [P.positions _ _ _ X z]
        exact Nat.le_mul_of_pos_left _ P.divisor_pos
      have hc' : (M.positions : ℝ) ≤ X.positions := by exact_mod_cast hc
      have hpow := pow_le_pow_left₀ (Nat.cast_nonneg M.positions (α := ℝ)) hc' 2
      calc
        _ ≤ ν * M.energy + Q.error * (M.positions : ℝ) ^ 2 := Q.energy _ _ _ _ y
        _ ≤ ν * (μ * X.energy + P.error * (X.positions : ℝ) ^ 2) +
            Q.error * (X.positions : ℝ) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hM Q.gain_nonneg)
            (mul_le_mul_of_nonneg_left hpow Q.error_nonneg)
        _ = _ := by ring

end Procedure
end Compression

end VPVNP
end Computability
end OAI
