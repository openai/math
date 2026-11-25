import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyScale

/-! # Matrix actions on arrays of jets in operand coordinates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] {e h : ℕ}

/-- Decode a full array of jets in the coordinate order used for each operand. -/
noncomputable def jetOperandArray {I : Type*} (φ : R →+* S) (η : S) (m : S[X])
    (x : I × ((Fin h × Fin e) × Fin 2) → R) (i : I) : JetQuotient m h :=
  jetOperandValue φ η m (fun j => x (i,j))

/-- A base-ring circuit acting by a prescribed jet matrix after coordinate decoding. -/
def JetMatrixCircuit (φ : R →+* S) (η : S) (m : S[X]) (e h : ℕ)
    {I O : Type*} [Fintype I] (A : Matrix O I (JetQuotient m h)) (C : ℝ) : Prop :=
  ∃ g : ℕ, (g : ℝ) ≤ C ∧
    ∃ q : Circuit R (I × ((Fin h × Fin e) × Fin 2)) (O × ((Fin h × Fin e) × Fin 2)) g,
      ∀ x, jetOperandArray φ η m (q.eval x) = A *ᵥ jetOperandArray φ η m x

variable {φ : R →+* S} {η : S} {m : S[X]}

/-- An identity layer only rewires the array. -/
theorem JetMatrixCircuit.one (I : Type*) [Fintype I] [DecidableEq I] :
    JetMatrixCircuit φ η m e h (1 : Matrix I I _) 0 := by
  let q : Circuit R (I × ((Fin h × Fin e) × Fin 2)) (I × ((Fin h × Fin e) × Fin 2)) 0 :=
    ⟨.nil, fun j => .scaled 1 (.inl j)⟩
  refine ⟨0, by simp, q, fun x => ?_⟩
  have heval : q.eval x = x := funext fun j => by simp [q, Circuit.eval, Readout.eval]
  rw [heval, one_mulVec]

/-- Matrix multiplication composes the two circuits and adds their budgets. -/
theorem JetMatrixCircuit.mul {I J O : Type*} [Fintype I] [Fintype J]
    {A : Matrix O J (JetQuotient m h)} {B : Matrix J I (JetQuotient m h)} {a b : ℝ}
    (hA : JetMatrixCircuit φ η m e h A a) (hB : JetMatrixCircuit φ η m e h B b) :
    JetMatrixCircuit φ η m e h (A * B) (a + b) := by
  obtain ⟨s, hs, p, hp⟩ := hA
  obtain ⟨t, ht, q, hq⟩ := hB
  obtain ⟨g, hg, r, hr⟩ := circuit_comp q p
  refine ⟨g, ?_, r, fun x => ?_⟩
  · have hg' : (g : ℝ) ≤ (t : ℝ) + s := by exact_mod_cast hg
    linarith
  · rw [hr, hp, hq, mulVec_mulVec]

end FiniteFourier
end LinearAlgebra
end OAI
