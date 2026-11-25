import OAI.LinearAlgebra.FiniteFourier.IntegralProgramBuilder
import OAI.LinearAlgebra.FiniteFourier.Circuit

/-! # Compiling integral binary linear circuits into arithmetic programs

Two constant multiplications and one addition implement each binary gate. A
scaled readout costs one multiplication. Inputs and previous registers remain
available throughout.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open MatrixMultiplication
variable {I J O : Type*}

/-- Append a family of operations to a shared arithmetic program. Each operation
may use the original registers and retains every previously computed register. -/
theorem intProgram_collect {r : ℕ} (p : Arithmetic.Program ℤ I r) {B : Type*} [Fintype B]
    (U : B → Type*) (f : ∀ b, U b → (I → ℤ) → ℤ) (cost : B → ℕ)
    (build : ∀ b {v : ℕ} (q : Arithmetic.Program ℤ I v),
      (∀ h, IntAvailable p h → IntAvailable q h) →
      ∃ m, ∃ z : Arithmetic.Program ℤ I m, z.cost ≤ q.cost + cost b ∧
        (∀ h, IntAvailable q h → IntAvailable z h) ∧ ∀ u, IntAvailable z (f b u)) :
    ∃ m, ∃ z : Arithmetic.Program ℤ I m, z.cost ≤ p.cost + ∑ b, cost b ∧
      (∀ h, IntAvailable p h → IntAvailable z h) ∧ ∀ b u, IntAvailable z (f b u) := by
  classical
  suffices H : ∀ t : Finset B, ∃ m, ∃ z : Arithmetic.Program ℤ I m,
      z.cost ≤ p.cost + ∑ b ∈ t, cost b ∧ (∀ h, IntAvailable p h → IntAvailable z h) ∧
        ∀ b ∈ t, ∀ u, IntAvailable z (f b u) by
    obtain ⟨m, z, hc, hk, hv⟩ := H Finset.univ
    exact ⟨m, z, hc, hk, fun b => hv b (Finset.mem_univ b)⟩
  intro t
  induction t using Finset.induction_on with
  | empty => exact ⟨r, p, by simp, fun _ h => h, by simp⟩
  | @insert b t hb ih =>
    obtain ⟨v, q, hc, hk, hv⟩ := ih
    obtain ⟨m, z, hc', hk', hv'⟩ := build b q hk
    refine ⟨m, z, ?_, fun _ h => hk' _ (hk _ h), fun i hi u => ?_⟩
    · rw [Finset.sum_insert hb]
      omega
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hv' u
      · exact hk' _ (hv i hi u)

private theorem compileLinearRegisters {v r : ℕ} (p : Arithmetic.Program ℤ I v)
    (q : Program ℤ J r) (y : (I → ℤ) → J → ℤ)
    (hy : ∀ j, IntAvailable p (fun x => y x j)) :
    ∃ m, ∃ z : Arithmetic.Program ℤ I m, z.cost ≤ p.cost + 3 * r ∧
      (∀ f, IntAvailable p f → IntAvailable z f) ∧
      ∀ w : J ⊕ Fin r, IntAvailable z (fun x => Sum.elim (y x) (q.value (y x)) w) := by
  induction q with
  | nil =>
    refine ⟨v, p, by simp, fun _ h => h, ?_⟩
    rintro (j | j)
    · exact hy j
    · exact j.elim0
  | @step r q g ih =>
    obtain ⟨m, z, hc, hk, hv⟩ := ih
    obtain ⟨m', z', hc', hk', hv'⟩ := intAvailable_combine z g.leftCoeff g.rightCoeff
      (hv g.left) (hv g.right)
    refine ⟨m', z', by omega, fun _ h => hk' _ (hk _ h), ?_⟩
    rintro (j | j)
    · exact hk' _ (hk _ (hy j))
    · exact Fin.cases hv' (fun k => hk' _ (hv (.inr k))) j

/-- Append an integer linear circuit to an arithmetic program, using the given
available registers as inputs. -/
theorem intCompileLinear {v s : ℕ} [Fintype O] (p : Arithmetic.Program ℤ I v)
    (q : Circuit ℤ J O s) (y : (I → ℤ) → J → ℤ) (hy : ∀ j, IntAvailable p (fun x => y x j)) :
    ∃ m, ∃ z : Arithmetic.Program ℤ I m, z.cost ≤ p.cost + 3 * s + Fintype.card O ∧
      (∀ f, IntAvailable p f → IntAvailable z f) ∧
      ∀ o, IntAvailable z (fun x => q.eval (y x) o) := by
  obtain ⟨u, r, hc, hk, hv⟩ := compileLinearRegisters p q.program y hy
  let result (o : O) (_ : Unit) (x : I → ℤ) := q.eval (y x) o
  have build (o : O) {l : ℕ} (v : Arithmetic.Program ℤ I l)
      (keep : ∀ h, IntAvailable r h → IntAvailable v h) :
      ∃ m, ∃ z : Arithmetic.Program ℤ I m, z.cost ≤ v.cost + 1 ∧
        (∀ h, IntAvailable v h → IntAvailable z h) ∧ ∀ u : Unit, IntAvailable z (result o u) := by
    cases he : q.output o with
    | zero =>
      obtain ⟨m, z, hc', hk', hv'⟩ := intAvailable_const v 0
      exact ⟨m, z, by omega, hk', fun _ => by simpa [result, Circuit.eval, he, Readout.eval] using hv'⟩
    | scaled a w =>
      obtain ⟨m, z, hc', hk', hv'⟩ := intAvailable_scale v a (keep _ (hv w))
      exact ⟨m, z, hc', hk', fun _ => by simpa [result, Circuit.eval, he, Readout.eval] using hv'⟩
  obtain ⟨m, z, hc', hk', hv'⟩ := intProgram_collect r (fun _ : O => Unit) result (fun _ => 1) build
  exact ⟨m, z, hc'.trans (by simp; omega), fun _ h => hk' _ (hk _ h), fun o => hv' o ()⟩

end FiniteFourier
end LinearAlgebra
end OAI
