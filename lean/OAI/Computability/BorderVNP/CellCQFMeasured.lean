import OAI.Computability.BorderVNP.CellCQFPolynomialDegree
import OAI.Computability.BorderVNP.CellCQFMeterPair

/-! # Uniform constants for actual cell-printer calls

The parameter `s` measures the particular input and intermediate words of a family of
calls. Keeping it fixed across a composition adds their costs without multiplying degrees.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {I A B C : Type} {ea : A → List Bool} {eb : B → List Bool} {ec : C → List Bool}
variable {f : A → B} {g : B → C}

/-- A single fixed coefficient bounds every actual call in this family. -/
def Measured (s : I → ℕ) (d : ℕ) (p : Procedure ea eb f) (arg : I → A) : Prop :=
  ∃ K : ℕ, ∀ x, p.meter (arg x) ≤ K*(s x+1)^d

/-- The output word grows by at most one bit per transition in the actual clean run. -/
theorem output_le_cost (p : Procedure ea eb f) (a : A) : (eb (f a)).length ≤ (ea a).length+p.cost a := by
  have h := (p.ticks_cost a).length_le p.output
  simp only [singletonStore,Function.update_self] at h
  by_cases he : p.output = p.input
  · simpa only [he,Function.update_self] using h
  · simp only [Function.update_of_ne he,List.length_nil,Nat.zero_add] at h
    omega

/-- Bound the full call charge, including input and output lengths, at the degree of the
concrete primitive applied to its actual input encoding. -/
theorem Measured.of_degree (s : I → ℕ) (d : ℕ) (hd : 0 < d) (p : Procedure ea eb f) (arg : I → A)
    (hg : p.bound.natDegree ≤ d) {H : ℕ} (hlen : ∀ x, (ea (arg x)).length+1 ≤ H*(s x+1)) :
    Measured s d p arg := by
  refine ⟨(2*p.bound.eval 1+2)*H^d,fun x => ?_⟩
  have h := p.cost_pow (arg x) hg
  have ho := output_le_cost p (arg x)
  let n := (ea (arg x)).length
  have hbase : n+1 ≤ (n+1)^d := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (Nat.zero_lt_succ n) (show 1 ≤ d from hd))
  have hsize := Nat.pow_le_pow_left (hlen x) d
  rw [Nat.mul_pow] at hsize
  have hscaled := Nat.mul_le_mul_left (2*p.bound.eval 1+2) hsize
  rw [Nat.add_mul,Nat.mul_assoc] at hscaled
  unfold meter
  dsimp only [n] at hbase
  rw [Nat.mul_assoc]
  have hh : 2*(p.bound.eval 1*((ea (arg x)).length+1)^d) + 2*((ea (arg x)).length+1)^d ≤
      (2*p.bound.eval 1+2)*(H^d*(s x+1)^d) := by
    simpa only [Nat.add_mul, Nat.mul_assoc] using hscaled
  omega

/-- Two installed calls with the same physical size parameter preserve their clock degree. -/
theorem Measured.comp {s : I → ℕ} {d : ℕ} (p : Procedure ea eb f) (q : Procedure eb ec g)
    (arg : I → A) (hp : Measured s d p arg) (hq : Measured s d q (fun x => f (arg x))) :
    Measured s d (q.comp p) arg := by
  obtain ⟨P,hp⟩ := hp
  obtain ⟨Q,hq⟩ := hq
  refine ⟨6*(P+Q),fun x => (meter_comp q p (arg x)).trans ?_⟩
  rw [Nat.mul_assoc,Nat.add_mul]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add (hp x) (hq x))

/-- Capturing two computed fields shares the clock degree of the two subcalls. -/
theorem Measured.pair {s : I → ℕ} {d : ℕ} {h : A → C} (p : Procedure ea eb f) (q : Procedure ea ec h)
    (arg : I → A) (hp : Measured s d p arg) (hq : Measured s d q arg) :
    Measured s d (p.pair q) arg := by
  obtain ⟨P,hp⟩ := hp
  obtain ⟨Q,hq⟩ := hq
  refine ⟨(2*10^9)*(P+Q),fun x => (meter_pair p q (arg x)).trans ?_⟩
  rw [Nat.mul_assoc (2*10^9) (P+Q),Nat.add_mul]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add (hp x) (hq x))

/-- Semantic rewriting of a fixed program is transparent to the measured charge. -/
@[simp] theorem Measured.congrFun {s : I → ℕ} {d : ℕ} {h : A → B}
    (p : Procedure ea eb f) (eqn : ∀ a, f a = h a) (arg : I → A) :
    Measured s d (p.congrFun eqn) arg ↔ Measured s d p arg := by
  simp only [Measured,meter_congrFun]

/-- Apply a measured routine to a family of actual arguments whose physical sizes
are bounded linearly by the caller's size parameter. -/
theorem Measured.reparam {J : Type} {s : I → ℕ} {t : J → ℕ} {d : ℕ}
    {p : Procedure ea eb f} {arg : I → A} (hp : Measured s d p arg) (u : J → I)
    {H : ℕ} (hu : ∀ j, s (u j)+1 ≤ H*(t j+1)) :
    Measured t d p (fun j => arg (u j)) := by
  obtain ⟨K,hK⟩ := hp
  refine ⟨K*H^d,fun j => (hK (u j)).trans ?_⟩
  have h := Nat.mul_le_mul_left K (Nat.pow_le_pow_left (hu j) d)
  simpa only [Nat.mul_pow,Nat.mul_assoc] using h

/-- A clock bound is monotone in its natural exponent. -/
theorem Measured.enlarge {s : I → ℕ} {d e : ℕ} {p : Procedure ea eb f} {arg : I → A}
    (hp : Measured s d p arg) (h : d ≤ e) : Measured s e p arg := by
  obtain ⟨K,hK⟩ := hp
  exact ⟨K,fun x => (hK x).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by omega) h))⟩

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  Measured
  output_le_cost
  Measured.of_degree
  Measured.comp
  Measured.pair
  Measured.congrFun
  Measured.reparam
  Measured.enlarge)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
