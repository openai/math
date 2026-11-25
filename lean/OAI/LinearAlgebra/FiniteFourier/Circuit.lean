import Mathlib

/-! # Unrestricted binary linear circuits

Inputs and earlier registers may be reused. Each gate computes one linear combination
of two available scalars. Output wires have free scaling, and zero outputs are free.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- A binary linear gate over two previously available wires. -/
structure BinaryGate (K W : Type*) where
  left : W
  right : W
  leftCoeff : K
  rightCoeff : K

def BinaryGate.eval {K W : Type*} [Semiring K] (g : BinaryGate K W) (v : W → K) : K :=
  g.leftCoeff * v g.left + g.rightCoeff * v g.right

/-- Outputs may select and scale a wire, or output zero. -/
inductive Readout (K W : Type*) where
  | zero
  | scaled (coeff : K) (wire : W)

def Readout.eval {K W : Type*} [Semiring K] (z : Readout K W) (v : W → K) : K :=
  match z with
  | .zero => 0
  | .scaled c w => c * v w

/-- A straight-line program of precisely the displayed number of binary gates. -/
inductive Program (K I : Type*) : ℕ → Type _ where
  | nil : Program K I 0
  | step {r : ℕ} (p : Program K I r) (g : BinaryGate K (I ⊕ Fin r)) : Program K I (r + 1)

namespace Program

variable {K I : Type*} [Semiring K]

/-- Evaluation of the stored registers, with the newest value in register zero. -/
def value : {r : ℕ} → Program K I r → (I → K) → Fin r → K
  | _, .nil, _ => Fin.elim0
  | _, .step p g, x => Fin.cases (g.eval (Sum.elim x (p.value x))) (p.value x)

end Program

/-- A program together with its readouts. -/
structure Circuit (K I O : Type*) (s : ℕ) where
  program : Program K I s
  output : O → Readout K (I ⊕ Fin s)

namespace Circuit

variable {K I O : Type*} [Semiring K] {s : ℕ}

def eval (p : Circuit K I O s) (x : I → K) (o : O) : K :=
  (p.output o).eval (Sum.elim x (p.program.value x))

noncomputable def matrix (p : Circuit K I O s) : Matrix O I K := by
  classical
  exact fun o i => p.eval (Pi.single i 1) o

theorem matrix_apply [DecidableEq I] (p : Circuit K I O s) (o : O) (i : I) :
    p.matrix o i = p.eval (Pi.single i 1) o := by
  simp only [matrix]
  exact congrArg (fun x => p.eval x o) (by ext j; by_cases h : j = i <;> simp [h])

end Circuit

/-- Exact realization with at most the given number of gates. -/
def RealizableAtMost {K I O : Type*} [Semiring K] (M : Matrix O I K) (S : ℕ) : Prop :=
  ∃ s ≤ S, ∃ p : Circuit K I O s, p.matrix = M

section Existence

variable {K I O : Type*} [Semiring K]

/-- A row obtainable from the current registers by a free readout. -/
private def HasRow {r : ℕ} (p : Program K I r) (f : (I → K) → K) : Prop :=
  ∃ z : Readout K (I ⊕ Fin r), ∀ x, z.eval (Sum.elim x (p.value x)) = (f x)

private theorem hasRow_step {r : ℕ} {p : Program K I r} {f : (I → K) → K}
    (hf : HasRow p f) (g : BinaryGate K (I ⊕ Fin r)) : HasRow (p.step g) f := by
  obtain ⟨z, hz⟩ := hf
  cases z with
  | zero => exact ⟨.zero, hz⟩
  | scaled c w =>
    cases w with
    | inl i => exact ⟨.scaled c (.inl i), hz⟩
    | inr j => exact ⟨.scaled c (.inr j.succ), hz⟩

/-- Add one weighted input to an available output in a single gate. -/
private theorem addInput {r : ℕ} {p : Program K I r} {f : (I → K) → K}
    (hf : HasRow p f) (i : I) (a : K) :
    ∃ g : BinaryGate K (I ⊕ Fin r), HasRow (p.step g) (fun x => a * x i + f x) := by
  obtain ⟨z, hz⟩ := hf
  cases z with
  | zero =>
    refine ⟨⟨.inl i, .inl i, a, 0⟩, .scaled 1 (.inr 0), fun x => ?_⟩
    change _ = a * x i + f x
    rw [← hz x]
    simp [Readout.eval, Program.value, BinaryGate.eval]
  | scaled c w =>
    refine ⟨⟨.inl i, w, a, c⟩, .scaled 1 (.inr 0), fun x => ?_⟩
    change _ = a * x i + f x
    rw [← hz x]
    simp [Readout.eval, Program.value, BinaryGate.eval]

private theorem addRow [DecidableEq I] {r : ℕ} (p : Program K I r) (s : Finset I)
    (f : I → K) : ∃ n ≤ r + s.card, ∃ q : Program K I n,
      (∀ u, HasRow p u → HasRow q u) ∧ HasRow q (fun x => ∑ i ∈ s, f i * x i) := by
  induction s using Finset.induction with
  | empty => exact ⟨r, by simp, p, fun _ h => h, .zero, by simp [Readout.eval]⟩
  | @insert i s hi ih =>
    obtain ⟨n, hn, q, hpq, hrow⟩ := ih
    obtain ⟨g, hg⟩ := addInput hrow i (f i)
    refine ⟨n + 1, ?_, q.step g, fun u h => hasRow_step (hpq u h) _, ?_⟩
    · rw [Finset.card_insert_of_notMem hi]
      omega
    · simpa only [Finset.sum_insert hi] using hg

private theorem addRows [Fintype I] (t : Finset O) (M : Matrix O I K) :
    ∃ n ≤ t.card * Fintype.card I, ∃ q : Program K I n,
      ∀ o ∈ t, HasRow q (fun x => ∑ i, M o i * x i) := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨0, by simp, .nil, by simp⟩
  | @insert o t ho ih =>
    obtain ⟨r, hr, p, hrows⟩ := ih
    obtain ⟨n, hn, q, hpq, hrow⟩ := addRow p Finset.univ (M o)
    refine ⟨n, ?_, q, fun j hj => ?_⟩
    · rw [Finset.card_insert_of_notMem ho, Nat.succ_mul]
      exact hn.trans (Nat.add_le_add_right hr _)
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hrow
      · exact hpq _ (hrows j hj)

/-- The row-by-row construction realizes every finite matrix, including empty formats. -/
theorem realizableAtMost_card_mul_card [Fintype I] [Fintype O] (M : Matrix O I K) :
    RealizableAtMost M (Fintype.card O * Fintype.card I) := by
  classical
  obtain ⟨n, hn, q, hrows⟩ := addRows Finset.univ M
  choose z hz using fun o => hrows o (Finset.mem_univ o)
  refine ⟨n, hn, ⟨q, z⟩, ?_⟩
  ext o i
  change (z o).eval (Sum.elim _ _) = _
  rw [hz]
  simp [Pi.single_apply, mul_ite]

/-- Least number of binary linear gates needed to apply a matrix. -/
noncomputable def complexity [Fintype I] [Fintype O] (M : Matrix O I K) : ℕ :=
  sInf {n | RealizableAtMost M n}

theorem realizableAtMost_complexity [Fintype I] [Fintype O] (M : Matrix O I K) :
    RealizableAtMost M (complexity M) := by
  classical
  exact Nat.sInf_mem (s := {n | RealizableAtMost M n}) ⟨_, realizableAtMost_card_mul_card M⟩

theorem complexity_le_iff [Fintype I] [Fintype O] (M : Matrix O I K) (s : ℕ) :
    complexity M ≤ s ↔ RealizableAtMost M s := by
  constructor
  · intro h
    obtain ⟨r, hr, p, hp⟩ := realizableAtMost_complexity M
    exact ⟨r, hr.trans h, p, hp⟩
  · intro h
    classical
    exact Nat.sInf_le h

end Existence

end FiniteFourier
end LinearAlgebra
end OAI
