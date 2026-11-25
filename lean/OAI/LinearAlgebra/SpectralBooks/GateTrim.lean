import OAI.LinearAlgebra.SpectralBooks.FormalCircuit

/-! # Bounding the register count of division-free programs

Inputs and constants cost no arithmetic operations. We can defer their
introduction until they occur as operands of a charged gate or as the output.
Each binary operation then uses at most three new registers.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial

noncomputable section

variable {F I : Type*} [CommRing F]

private def outputs {r : ℕ} (p : Program F I r) : Set (MvPolynomial I F) :=
  Set.range (registerPolynomial p)

private def available {r : ℕ} (p : Program F I r) : Set (MvPolynomial I F) :=
  outputs p ∪ (Set.range C ∪ Set.range X)

private theorem outputs_step {r : ℕ} (p : Program F I r) (g : Gate F I (Fin r)) :
    outputs p ⊆ outputs (p.step g) := by
  rintro _ ⟨i, rfl⟩
  exact ⟨i.succ, rfl⟩

private theorem available_mono {r m : ℕ} {p : Program F I r} {q : Program F I m}
    (h : outputs p ⊆ outputs q) : available p ⊆ available q :=
  Set.union_subset_union_left _ h

/-- Materialize a single deferred input or constant, if required. -/
private theorem materialize {r : ℕ} (p : Program F I r) {f : MvPolynomial I F}
    (h : f ∈ available p) :
    ∃ (m : ℕ) (q : Program F I m), m ≤ r + 1 ∧ q.cost = p.cost ∧
      outputs p ⊆ outputs q ∧ f ∈ outputs q := by
  rcases h with h | ⟨c, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨r, p, by omega, rfl, Set.Subset.rfl, h⟩
  · exact ⟨r + 1, p.step (.constant c), le_rfl, rfl, outputs_step _ _, 0, rfl⟩
  · exact ⟨r + 1, p.step (.input i), le_rfl, rfl, outputs_step _ _, 0, rfl⟩

private theorem binary_step {r : ℕ} (p : Program F I r) {f h : MvPolynomial I F}
    (hf : f ∈ available p) (hh : h ∈ available p)
    (g : ∀ {n}, Fin n → Fin n → Gate F I (Fin n))
    (op : MvPolynomial I F → MvPolynomial I F → MvPolynomial I F)
    (hc : ∀ {n} (i j : Fin n), (g i j).cost = 1)
    (hv : ∀ {n} (i j : Fin n) (v : Fin n → MvPolynomial I F),
      gatePolynomial (g i j) v = op (v i) (v j)) :
    ∃ (m : ℕ) (q : Program F I m), m ≤ r + 3 ∧ q.cost = p.cost + 1 ∧
      available p ⊆ available q ∧ op f h ∈ available q := by
  obtain ⟨a, A, ha, hAc, hA, hfA⟩ := materialize p hf
  obtain ⟨b, B, hb, hBc, hB, hhB⟩ := materialize A (available_mono hA hh)
  obtain ⟨i, hi⟩ := hB hfA
  obtain ⟨j, hj⟩ := hhB
  refine ⟨b + 1, B.step (g i j), by omega, ?_, ?_, Or.inl ⟨0, ?_⟩⟩
  · simp only [Program.cost, hc, hBc, hAc]
  · exact available_mono (hA.trans (hB.trans (outputs_step _ _)))
  · rw [registerPolynomial_zero, hv, hi, hj]

private theorem registers_available_step {r m : ℕ} {p : Program F I r} {q : Program F I m}
    (g : Gate F I (Fin r)) (h : ∀ i, registerPolynomial p i ∈ available q)
    (hg : gatePolynomial g (registerPolynomial p) ∈ available q) :
    ∀ i, registerPolynomial (p.step g) i ∈ available q :=
  Fin.cases hg h

private theorem defer_sources {r : ℕ} (p : Program F I r) :
    ∃ (m : ℕ) (q : Program F I m), m ≤ 3 * p.cost ∧ q.cost = p.cost ∧
      ∀ i, registerPolynomial p i ∈ available q := by
  induction p with
  | nil => exact ⟨0, .nil, le_rfl, rfl, fun i => i.elim0⟩
  | step p gate ih =>
    obtain ⟨m, q, hm, hq, h⟩ := ih
    have binary (g : ∀ {n}, Fin n → Fin n → Gate F I (Fin n))
        (op : MvPolynomial I F → MvPolynomial I F → MvPolynomial I F)
        (hc : ∀ {n} (i j : Fin n), (g i j).cost = 1)
        (hv : ∀ {n} (i j : Fin n) (v : Fin n → MvPolynomial I F),
          gatePolynomial (g i j) v = op (v i) (v j)) (i j) :
        ∃ (k : ℕ) (Q : Program F I k), k ≤ 3 * (p.step (g i j)).cost ∧
          Q.cost = (p.step (g i j)).cost ∧
          ∀ z, registerPolynomial (p.step (g i j)) z ∈ available Q := by
      obtain ⟨k, Q, hk, hQc, hQ, hnew⟩ := binary_step q (h i) (h j) g op hc hv
      refine ⟨k, Q, ?_, ?_, registers_available_step _ (fun z => hQ (h z)) ?_⟩
      · simp only [Program.cost, hc]
        omega
      · simp only [Program.cost, hc, hQc, hq]
      · rwa [hv]
    cases gate with
    | constant c =>
      exact ⟨m, q, hm, hq, registers_available_step _ h (Or.inr (Or.inl ⟨c, rfl⟩))⟩
    | input i =>
      exact ⟨m, q, hm, hq, registers_available_step _ h (Or.inr (Or.inr ⟨i, rfl⟩))⟩
    | add i j => exact binary Gate.add (· + ·) (fun _ _ => rfl) (fun _ _ _ => rfl) i j
    | sub i j => exact binary Gate.sub (· - ·) (fun _ _ => rfl) (fun _ _ _ => rfl) i j
    | mul i j => exact binary Gate.mul (· * ·) (fun _ _ => rfl) (fun _ _ _ => rfl) i j

/-- An output computed in at most `s` arithmetic operations has a program
with the same operation bound and at most `3 * s + 1` registers. -/
theorem exists_bounded_register_program {r s : ℕ} (p : Program F I r) (o : Fin r)
    (hs : p.cost ≤ s) :
    ∃ (m : ℕ) (q : Program F I m) (i : Fin m), m ≤ 3 * s + 1 ∧ q.cost ≤ s ∧
      registerPolynomial q i = registerPolynomial p o := by
  obtain ⟨a, A, ha, hAc, hA⟩ := defer_sources p
  obtain ⟨b, B, hb, hBc, _, i, hi⟩ := materialize A (hA o)
  exact ⟨b, B, i, by omega, by omega, hi⟩

private theorem pad_output {r m : ℕ} (p : Program F I m) (o : Fin m) (hm : m ≤ r) :
    ∃ (q : Program F I r) (i : Fin r), registerPolynomial q i = registerPolynomial p o := by
  induction hm with
  | refl => exact ⟨p, o, rfl⟩
  | step h ih =>
    obtain ⟨q, i, hi⟩ := ih
    exact ⟨q.step (.constant 0), i.succ, hi⟩

/-- A circuit of cost at most `s` may use a fixed register format with its
distinguished output in slot zero, uniformly in the circuit and its output. -/
theorem exists_fixed_register_program {r s : ℕ} (p : Program F I r) (o : Fin r)
    (hs : p.cost ≤ s) :
    ∃ q : Program F I (3 * s + 3), registerPolynomial q 0 = registerPolynomial p o := by
  obtain ⟨m, q, i, hm, _, hi⟩ := exists_bounded_register_program p o hs
  obtain ⟨v, j, hj⟩ := pad_output q i hm
  refine ⟨(v.step (.constant 0)).step (.add j.succ 0), ?_⟩
  simpa [gatePolynomial] using hj.trans hi

end

end SpectralBooks
end LinearAlgebra
end OAI
