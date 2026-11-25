import OAI.LinearAlgebra.SpectralBooks.GridPin.GridPinCost
import OAI.LinearAlgebra.SpectralBooks.GridPin.GridPinUniform
import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.GridUniversalPolynomial

/-! # Initializing the map sum with a bipartite independent-set grid -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace GridPin

open UniformDecorations Arithmetic.RecursiveBlock

variable {K : Type*} [Field K]

/-- A single family of shared, type-indexed tables realizes a prescribed
spherical map. Its input tables may contain both variables and constants. -/
theorem pinCircuit {V D I : Type*} [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D]
    (H : PortGraph.RootedMap V D) {N : ℕ} (hc : Fintype.card V ≤ N) (hs : H.Spherical)
    (T : (v : V) → (H.graph.Port v → Bits 1) → MvPolynomial I K)
    (hT : ∀ v x, PlanarPatch.HasFormula 1 (T v x)) :
    ∃ W, 0 < W ∧ W ≤ pinConstant * Nat.clog 2 (2*N) ∧
      ∃ p : Family K I (Address W),
        p.cost ≤ 2^(pinConstant * Nat.clog 2 (2*N)) ∧
        H.graph.contraction (A:=fun _ => Bits 1) T =
          MvPolynomial.bind₁ (familyPolynomial p) (Zpoly N W) := by
  let h := Nat.clog 2 (Fintype.card V)
  let S := pinSpec H T
  have hN : 0 < N := (Fintype.card_pos_iff.mpr ⟨H.root⟩).trans_le hc
  have hh : h ≤ Nat.clog 2 (2*N) := Nat.clog_mono_right _ (hc.trans (by omega))
  obtain ⟨hwpos, hw, hcost⟩ := pinBounds hN hh
  obtain ⟨p, heval, hp⟩ := S.compile_family (W:=1) le_rfl
    (pinSpec_tensor_hasFormula H T le_rfl hT)
  refine ⟨width 1 h, hwpos, hw, p, ?_, ?_⟩
  · exact (by simpa only [mul_one] using hp : p.cost ≤ Fintype.card (Address (width 1 h)) * (2^h+1)).trans hcost
  · calc
      H.graph.contraction (A:=fun _ => Bits 1) T = Z N (width 1 h) S.compiled := (Z_pinSpec H T hc hs).symm
      _ = Z N (width 1 h) (fun θ a => familyPolynomial p ⟨θ,a⟩) := by
        apply congrArg (Z N (width 1 h))
        funext θ a
        exact (heval ⟨θ,a⟩).symm
      _ = _ := (bind₁_Zpoly (familyPolynomial p) N).symm

/-- For nonempty vertex classes one type-keyed table family pins the precise
independent-set polynomial in the map sum. The wire width is logarithmic in
the size of the grid and all entries are formed with polynomially many gates. -/
theorem initialPin {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (E : Fin m → Fin n → Prop) :
    let N := m*n + 2*(m+n)
    ∃ W, 0 < W ∧ W ≤ pinConstant * Nat.clog 2 (2*N) ∧
      ∃ p : Family K (Vars m n) (Address W),
        p.cost ≤ 2^(pinConstant * Nat.clog 2 (2*N)) ∧
        IndependentSetGrid.polynomial (R := K) E =
          MvPolynomial.bind₁ (familyPolynomial p) (Zpoly N W) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨W, hpos, hw, p, hc, he⟩ := pinCircuit (rooted m n) (vertex_count _ _).le
    (spherical m n) (bitTable (K := K) E) (bitTable_hasFormula E)
  exact ⟨W, hpos, hw, p, hc, (contraction_bitTable E).symm.trans he⟩

end GridPin

end

end SpectralBooks
end LinearAlgebra
end OAI
