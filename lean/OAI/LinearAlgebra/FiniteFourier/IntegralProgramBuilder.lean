import OAI.LinearAlgebra.SpectralBooks.FormalCircuit

/-! # Running division-free integral programs on previously computed registers

The value of a register is the evaluation of its formal polynomial. Constants
and inputs can be loaded at no arithmetic cost. A weighted binary sum costs at
most two multiplications and one addition.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open MatrixMultiplication.Arithmetic OAI.LinearAlgebra.SpectralBooks MvPolynomial

variable {I J : Type*} {r s : ℕ}

/-- Value of an integral register under an assignment of its inputs. -/
noncomputable def intRegisterValue (p : Program ℤ I r) (x : I → ℤ) (j : Fin r) : ℤ :=
  eval x (registerPolynomial p j)

/-- A register contains this function for every assignment of the inputs. -/
def IntAvailable (p : Program ℤ I r) (f : (I → ℤ) → ℤ) : Prop :=
  ∃ j : Fin r, ∀ x, intRegisterValue p x j = f x

/-- Extend the program within an additional operation budget while retaining
all previously available values. -/
abbrev IntCanExtend (p : Program ℤ I r) (cost : ℕ) (f : (I → ℤ) → ℤ) : Prop :=
  ∃ (m : ℕ) (z : Program ℤ I m), z.cost ≤ p.cost + cost ∧
    (∀ u, IntAvailable p u → IntAvailable z u) ∧ IntAvailable z f

private theorem IntAvailable.step {p : Program ℤ I r} {f : (I → ℤ) → ℤ}
    (g : Gate ℤ I (Fin r)) (hf : IntAvailable p f) : IntAvailable (p.step g) f := by
  obtain ⟨i, hi⟩ := hf
  exact ⟨i.succ, hi⟩

theorem intAvailable_const (p : Program ℤ I r) (a : ℤ) :
    IntCanExtend p 0 (fun _ => a) := by
  refine ⟨_, p.step (.constant a), le_rfl, fun _ => IntAvailable.step _, 0, ?_⟩
  intro x
  simp [intRegisterValue, gatePolynomial]

theorem intAvailable_input (p : Program ℤ I r) (i : I) :
    IntCanExtend p 0 (fun x => x i) := by
  refine ⟨_, p.step (.input i), le_rfl, fun _ => IntAvailable.step _, 0, ?_⟩
  intro x
  simp [intRegisterValue, gatePolynomial]

variable {f g : (I → ℤ) → ℤ}

theorem intAvailable_add (p : Program ℤ I r) (hf : IntAvailable p f) (hg : IntAvailable p g) :
    IntCanExtend p 1 (fun x => f x + g x) := by
  obtain ⟨i, hi⟩ := hf
  obtain ⟨j, hj⟩ := hg
  refine ⟨_, p.step (.add i j), le_rfl, fun _ => IntAvailable.step _, 0, ?_⟩
  intro x
  simp [intRegisterValue, gatePolynomial, ← hi x, ← hj x]

private theorem intAvailable_sub (p : Program ℤ I r) (hf : IntAvailable p f)
    (hg : IntAvailable p g) : IntCanExtend p 1 (fun x => f x - g x) := by
  obtain ⟨i, hi⟩ := hf
  obtain ⟨j, hj⟩ := hg
  refine ⟨_, p.step (.sub i j), le_rfl, fun _ => IntAvailable.step _, 0, ?_⟩
  intro x
  simp [intRegisterValue, gatePolynomial, ← hi x, ← hj x]

private theorem intAvailable_mul (p : Program ℤ I r) (hf : IntAvailable p f)
    (hg : IntAvailable p g) : IntCanExtend p 1 (fun x => f x * g x) := by
  obtain ⟨i, hi⟩ := hf
  obtain ⟨j, hj⟩ := hg
  refine ⟨_, p.step (.mul i j), le_rfl, fun _ => IntAvailable.step _, 0, ?_⟩
  intro x
  simp [intRegisterValue, gatePolynomial, ← hi x, ← hj x]

theorem intAvailable_scale (p : Program ℤ I r) (a : ℤ) (hf : IntAvailable p f) :
    IntCanExtend p 1 (fun x => a * f x) := by
  obtain ⟨_, q, hq, keep, ha⟩ := intAvailable_const p a
  obtain ⟨m, z, hz, keep', hf'⟩ := intAvailable_mul q ha (keep _ hf)
  exact ⟨m, z, by omega, fun u hu => keep' _ (keep u hu), hf'⟩

theorem intAvailable_combine (p : Program ℤ I r) (a b : ℤ) (hf : IntAvailable p f)
    (hg : IntAvailable p g) : IntCanExtend p 3 (fun x => a * f x + b * g x) := by
  obtain ⟨_, p₁, h₁, k₁, ha⟩ := intAvailable_scale p a hf
  obtain ⟨_, p₂, h₂, k₂, hb⟩ := intAvailable_scale p₁ b (k₁ _ hg)
  obtain ⟨m, z, hz, k₃, h⟩ := intAvailable_add p₂ (k₂ _ ha) hb
  exact ⟨m, z, by omega, fun u hu => k₃ _ (k₂ _ (k₁ u hu)), h⟩

/-- Execute an integral program using previously computed values as its inputs.
All outputs share a single run and each arithmetic gate is charged once. -/
theorem intSimulateProgram (p : Program ℤ I r) (q : Program ℤ J s)
    (y : (I → ℤ) → J → ℤ) (hy : ∀ i, IntAvailable p (fun x => y x i)) :
    ∃ (m : ℕ) (z : Program ℤ I m), z.cost ≤ p.cost + q.cost ∧
      (∀ f, IntAvailable p f → IntAvailable z f) ∧
      ∀ i, IntAvailable z (fun x => intRegisterValue q (y x) i) := by
  induction q with
  | nil => exact ⟨r, p, le_rfl, fun _ h => h, fun i => i.elim0⟩
  | @step s q gate ih =>
    obtain ⟨m, z, hz, keep, hav⟩ := ih
    have he : IntCanExtend z gate.cost (fun x => intRegisterValue (q.step gate) (y x) 0) := by
      cases gate with
      | input i =>
        exact ⟨m, z, le_rfl, fun _ h => h, by
          simpa [intRegisterValue, gatePolynomial] using keep _ (hy i)⟩
      | constant c =>
        simpa [intRegisterValue, gatePolynomial, Gate.cost] using intAvailable_const z c
      | add i j =>
        simpa [intRegisterValue, gatePolynomial, Gate.cost] using intAvailable_add z (hav i) (hav j)
      | sub i j =>
        simpa [intRegisterValue, gatePolynomial, Gate.cost] using intAvailable_sub z (hav i) (hav j)
      | mul i j =>
        simpa [intRegisterValue, gatePolynomial, Gate.cost] using intAvailable_mul z (hav i) (hav j)
    obtain ⟨m', z', hz', keep', hgate⟩ := he
    exact ⟨m', z', by rw [Program.cost_step]; omega, fun u hu => keep' _ (keep u hu),
      Fin.cases hgate (fun j => keep' _ (hav j))⟩

end FiniteFourier
end LinearAlgebra
end OAI
