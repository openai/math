import OAI.ThreeFlat.Diagonal.PortTileKernel
import OAI.ThreeFlat.Diagonal.PortMotifGrid

namespace OAI
/-! # Finite grid identities in the original port coordinates -/

namespace ThreeFlat.Diagonal.PortMotifGrid

open LinearAlgebra.SpectralBooks SiteTensor ChordGraph Computability.VPVNP.MotifGrid
open scoped Classical BigOperators
noncomputable section

variable {m : ℕ} {E S : Type} [Fintype E] [Fintype S]

private def chordHom (D : PortGraph (Fin m) E) (e : E) : ℕ →+ Widths m :=
  if h : D.tail e < D.head e then Finsupp.singleAddHom ⟨(D.tail e,D.head e),h⟩
  else if h : D.head e < D.tail e then Finsupp.singleAddHom ⟨(D.head e,D.tail e),h⟩
  else 0

omit [Fintype E] in
private theorem chordHom_apply (D : PortGraph (Fin m) E) (e : E) (n : ℕ) :
    chordHom D e n = D.chordWidth e n := by
  unfold chordHom PortGraph.chordWidth
  split_ifs <;> rfl

private def chordWidthsHom (D : PortGraph (Fin m) E) : (E → ℕ) →+ Widths m where
  toFun w := D.chordWidths w
  map_zero' := by simp [PortGraph.chordWidths, ← chordHom_apply]
  map_add' := by intro x y; simp [PortGraph.chordWidths, ← chordHom_apply, Finset.sum_add_distrib]

/-- A whole base grid identity in the original format of the demanded and
supplied graphs. Parallel edge labels and the two ends of loops stay
visible to the local kernels. -/
theorem exists_grid_kernel {K : Type*} [Field K] [Nonempty (Fin m)]
    (D : PortGraph (Fin m) E) (P : PortGraph (Fin m) S)
    {p : E → ℝ} {q : S → ℝ} {H R : ℝ} (G : StrictGrids p q H R)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i)
    (comparison : ∀ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin m) K → _ → Prop),
      distanceEnergy p (fun i => rawWireDistance φ 1 (D.tail i) (D.head i)) ≤
        H * distanceEnergy q (fun i => rawWireDistance φ 1 (P.tail i) (P.head i)))
    {t : ℕ} (ht : 0 < t) (z : G.demands) {η : ℝ} (hη : 0 < η) (N : ℕ) :
    ∃ b s : ℕ, N < b ∧ (s : ℝ) ≤ η*b ∧ ∃ L : ℕ, L ≤ 2^s ∧
      ∃ n : Fin L → G.supplies → ℕ, (∀ l, ∑ j, n l j = b) ∧
      let A := fun e => Fin (2^(b * G.demandWidths t z e))
      let B := fun l e => Fin (2^(∑ j, n l j*G.supplyWidths t j e))
      ∃ M : ∀ l v, D.State A v → P.State (B l) v → K,
        ∀ x, D.wiring A x = ∑ l, ∑ y : ∀ e, B l e, ∏ v, M l v (x v) (P.atVertex y v) := by
  obtain ⟨b,s,hb,hs,L,hL,u,hu,hrest⟩ := exists_port_grid_tile D P G hp hq comparison ht z hη N
  choose n hn hr using hrest
  refine ⟨b,s,hb,hs,L,hL,n,hn,?_⟩
  dsimp only
  refine port_kernel_of_tile D P _ _ (raw K (b • D.chordWidths (G.demandWidths t z))) ?_ u hu ?_
  · apply ofRaw_le_iff.mp
    rw [ofRaw_raw, PortGraph.ofRaw_rawWiring_eq_graphClass]
    apply le_of_eq
    congr 1
    have hfun : b • G.demandWidths t z = (fun e => b * G.demandWidths t z e) := by
      funext e
      change b • (G.demandWidths t z e) = _
      simp []
    rw [← hfun]
    exact (chordWidthsHom D).map_nsmul b (G.demandWidths t z)
  · intro l
    apply ofRaw_le_iff.mp
    apply (ofRaw_le_iff.mpr (hr l)).trans_eq
    rw [ofRaw_raw, PortGraph.ofRaw_rawWiring_eq_graphClass]
    congr 1
    have hfun : (∑ j, n l j • G.supplyWidths t j) = (fun e => ∑ j, n l j * G.supplyWidths t j e) := by
      funext e
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      change n l j • (G.supplyWidths t j e) = _
      simp []
    rw [← hfun]
    change (∑ j, n l j • (chordWidthsHom P) (G.supplyWidths t j)) = (chordWidthsHom P) _
    simp only [map_sum, map_nsmul]

end
end ThreeFlat.Diagonal.PortMotifGrid

end OAI
