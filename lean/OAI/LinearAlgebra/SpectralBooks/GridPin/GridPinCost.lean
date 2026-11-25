import OAI.LinearAlgebra.SpectralBooks.GridPin.GridPinTables
import OAI.LinearAlgebra.SpectralBooks.GridPin.GridPinFaces
import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.UniformDecorations

/-! # One-bit variable tables and the polynomial cost of initial pinning -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped BigOperators Classical
noncomputable section

namespace GridPin

open UniformDecorations PortGraph PlanarPatch

variable {m n : ℕ} {K : Type*} [Field K]

abbrev Vars (m n : ℕ) := (Fin m ⊕ Fin n) × Bool

/-- Read a one-bit word as an occupation bit. Only the two entrance tables
depend on the independent-set variables. -/
def bitTable (E : Fin m → Fin n → Prop) (v : Vertex m n)
    (x : (graph m n).Port v → Bits 1) : MvPolynomial (Vars m n) K :=
  table E (fun i b => MvPolynomial.X (Sum.inl i, b))
    (fun j b => MvPolynomial.X (Sum.inr j, b)) v (fun p => finTwoEquiv (x p))

/-- Every original local entry is a variable or a field constant. -/
theorem bitTable_hasFormula (E : Fin m → Fin n → Prop) (v : Vertex m n)
    (x : (graph m n).Port v → Bits 1) : HasFormula 1 (bitTable (K := K) E v x) := by
  rcases v with ⟨i,_|_⟩ | (⟨j,_|_⟩ | ⟨i,j⟩)
  · apply HasFormula.input
  · simpa [bitTable, table, entry] using (HasFormula.const (I:=Vars m n) (1 : K))
  · apply HasFormula.input
  · simpa [bitTable, table, entry] using (HasFormula.const (I:=Vars m n) (1 : K))
  · simp only [bitTable, table, entry, IndependentSetGrid.crossing]
    split
    · simpa using (HasFormula.const (I := Vars m n) (1 : K))
    · simpa using (HasFormula.const (I := Vars m n) (0 : K))

theorem contraction_bitTable (E : Fin m → Fin n → Prop) :
    (graph m n).contraction (A := fun _ => Bits 1) (bitTable (K := K) E) =
      IndependentSetGrid.polynomial E := by
  rw [← contraction_eq_polynomial (R:=K)]
  unfold PortGraph.contraction
  let : DecidableEq (Edge m n) := fun _ _ => Classical.propDecidable _
  apply Fintype.sum_equiv ((Equiv.refl (Edge m n)).arrowCongr finTwoEquiv)
  intro x
  rfl

/-- One absolute constant bounds both the input width and the logarithm of
the number of gates needed to construct every entry. -/
def pinConstant : ℕ := Nat.clog 2 (Fintype.card MapType) + 8*tagWidth + 20

theorem pinBounds {h N : ℕ} (hN : 0 < N) (hh : h ≤ Nat.clog 2 (2*N)) :
    0 < width 1 h ∧ width 1 h ≤ pinConstant * Nat.clog 2 (2*N) ∧
      Fintype.card (Address (width 1 h)) * (2^h+1) ≤ 2^(pinConstant * Nat.clog 2 (2*N)) := by
  let L := Nat.clog 2 (2*N)
  let t := Nat.clog 2 (Fintype.card MapType)
  have hL : 0 < L := Nat.clog_pos (by decide) (by omega)
  have hv : 2^h+1 ≤ 2^(h+1) := by rw [pow_succ]; have := Nat.two_pow_pos h; omega
  have ht : Fintype.card MapType ≤ 2^t := Nat.le_pow_clog (by decide) _
  have hfixed := Nat.le_mul_of_pos_right (t+8*tagWidth+5) hL
  have hExp : t + 4*(width 1 h) + (h+1) ≤ pinConstant*L := by
    change h ≤ L at hh
    change _ ≤ (t+8*tagWidth+20)*L
    unfold width
    ring_nf at hfixed ⊢
    omega
  refine ⟨by unfold width; omega, by change _ ≤ pinConstant*L; omega, ?_⟩
  calc
    _ ≤ (2^t*2^(4*width 1 h))*2^(h+1) :=
      Nat.mul_le_mul ((card_address_le _).trans (Nat.mul_le_mul_right _ ht)) hv
    _ = 2^(t + 4*(width 1 h) + (h+1)) := by simp [pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hExp

end GridPin

end

end SpectralBooks
end LinearAlgebra
end OAI
