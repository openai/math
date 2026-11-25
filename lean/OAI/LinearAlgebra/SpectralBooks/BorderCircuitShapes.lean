import OAI.LinearAlgebra.SpectralBooks.BorderCircuit

/-!
# Scalar parameters of a circuit shape

Erase the scalar labels of a division-free program. Restoring arbitrary labels gives a polynomial
map from a finite affine space to the space of degree-`d` coefficient vectors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial

noncomputable section

variable {σ A B : Type*}

/-- Assign a scalar to an unlabelled gate when it is a scalar input. -/
private def labelGate (a : A) {ρ : Type*} : Gate Unit σ ρ → Gate A σ ρ
  | .constant _ => .constant a
  | .input i => .input i
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

/-- The scalar label of a register is used precisely when the register is a scalar input. -/
def labelProgram : {r : ℕ} → Program Unit σ r → (Fin r → A) → Program A σ r
  | 0, .nil, _ => .nil
  | _ + 1, .step p g, a => (labelProgram p (fun i ↦ a i.succ)).step (labelGate (a 0) g)

private theorem labelProgram_cost {r : ℕ} (p : Program Unit σ r) (a : Fin r → A) :
    (labelProgram p a).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih =>
    cases g <;> simp only [labelProgram, labelGate, Program.cost_step, ih, Gate.cost]

/-- Every labelled program is realized by its unlabelled shape. -/
private theorem exists_labelProgram [Zero A] {r : ℕ} (p : Program A σ r) :
    ∃ (q : Program Unit σ r) (a : Fin r → A), labelProgram q a = p := by
  induction p with
  | nil => exact ⟨.nil, Fin.elim0, rfl⟩
  | step p g ih =>
    obtain ⟨q, a, rfl⟩ := ih
    cases g with
    | constant c => exact ⟨q.step (.constant ()), Fin.cases c a, rfl⟩
    | input i => exact ⟨q.step (.input i), Fin.cases 0 a, rfl⟩
    | add i j => exact ⟨q.step (.add i j), Fin.cases 0 a, rfl⟩
    | sub i j => exact ⟨q.step (.sub i j), Fin.cases 0 a, rfl⟩
    | mul i j => exact ⟨q.step (.mul i j), Fin.cases 0 a, rfl⟩

/-- Mapping all scalar labels in a fixed circuit commutes with computing its formal output. -/
private theorem map_labelProgram_register [CommRing A] [CommRing B] (h : A →+* B)
    {r : ℕ} (q : Program Unit σ r) (a : Fin r → A) (i : Fin r) :
    MvPolynomial.map h (registerPolynomial (labelProgram q a) i) =
      registerPolynomial (labelProgram q (h ∘ a)) i := by
  induction q with
  | nil => exact Fin.elim0 i
  | step p g ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · cases g <;> simp [labelProgram, labelGate, gatePolynomial, ih, Function.comp_def]
    · exact ih (fun j ↦ a j.succ) j

/-- A size-bounded circuit shape with one designated output. The size bound counts binary
operations, so it is independent of scalar labels. -/
structure CircuitShape (σ : Type*) (s : ℕ) where
  registers : ℕ
  program : Program Unit σ registers
  output : Fin registers
  cost_le : program.cost ≤ s

/-- Polynomial map on the scalar labels of the registers of this shape. Coordinates corresponding
to variable inputs and arithmetic gates do not affect the map. -/
def circuitShapeCoordinates (K : Type*) [Field K] {s : ℕ} (d : ℕ) (q : CircuitShape σ s)
    (i : DegreeMonomial σ d) : MvPolynomial (Fin q.registers) K :=
  degreeCoefficientVector d (registerPolynomial (labelProgram q.program X) q.output) i

private theorem aeval_circuitShapeCoordinates {K L : Type*} [Field K] [Field L] [Algebra K L]
    {s : ℕ} (d : ℕ) (q : CircuitShape σ s) (a : Fin q.registers → L)
    (i : DegreeMonomial σ d) :
    aeval a (circuitShapeCoordinates K d q i) =
      degreeCoefficientVector d (registerPolynomial (labelProgram q.program a) q.output) i := by
  let h : MvPolynomial (Fin q.registers) K →+* L := (aeval a).toRingHom
  have hm := map_labelProgram_register h q.program X q.output
  have ha : h ∘ X = a := _root_.funext fun j ↦ aeval_X a j
  rw [ha] at hm
  simpa only [circuitShapeCoordinates, degreeCoefficientVector, coeff_map, h, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    using congrArg (fun f : MvPolynomial σ L ↦ f.coeff i.val) hm

/-- The union of parametrized circuit-shape images is exactly the family of degree-component
outputs, in any extension field. -/
theorem mem_circuitCoefficientVectors_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {d s : ℕ} {v : DegreeMonomial σ d → L} :
    v ∈ circuitCoefficientVectors L σ d s ↔
      ∃ (q : CircuitShape σ s) (a : Fin q.registers → L),
        (fun i ↦ aeval a (circuitShapeCoordinates K d q i)) = v := by
  constructor
  · rintro ⟨r, p, o, hp, rfl⟩
    obtain ⟨q, a, rfl⟩ := exists_labelProgram p
    let shape : CircuitShape σ s := ⟨r, q, o, (labelProgram_cost q a) ▸ hp⟩
    exact ⟨shape, a, _root_.funext (aeval_circuitShapeCoordinates (K := K) d shape a)⟩
  · rintro ⟨q, a, rfl⟩
    refine ⟨q.registers, labelProgram q.program a, q.output,
      (labelProgram_cost q.program a).trans_le q.cost_le, ?_⟩
    exact (_root_.funext (aeval_circuitShapeCoordinates (K := K) d q a)).symm

end

end SpectralBooks
end LinearAlgebra
end OAI
