import OAI.LinearAlgebra.SpectralBooks.ChordGraph.BoundedPatchReplacement
import OAI.LinearAlgebra.SpectralBooks.BoundedPatchReplacementSmall
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortChordWidths
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPruneMap

/-! # The patch replacement theorem on the original open incidence graph -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace PortGraph

open SiteTensor ChordGraph PlanarPatch Arithmetic

variable {V E B : Type} [Fintype E] [Fintype V] [Fintype B]

/-- One independent variable for each entry of an original local table. -/
abbrev PatchEntry (G : PortGraph V E) (attach : B → V) (q : ℕ) :=
  (v : V) × (G.Port v → Fin q) × ({b // attach b = v} → Fin q)

def inputTable (G : PortGraph V E) (attach : B → V) (q : ℕ) (F : Type*) [Field F] :
    G.StubTable attach (Fin q) (MvPolynomial (G.PatchEntry attach q) F) :=
  fun v a s => MvPolynomial.X ⟨v,a,s⟩

omit [Fintype B] in
/-- Specialize the independent input entries to any tables over a commutative
algebra. The enumeration of internal assignments is unchanged. -/
theorem specialize_inputTable (G : PortGraph V E) (attach : B → V) (q : ℕ)
    {F R : Type*} [Field F] [CommSemiring R] (h : F →+* R) (u : G.StubTable attach (Fin q) R)
    (x : B → Fin q) :
    MvPolynomial.eval₂Hom h (fun e : G.PatchEntry attach q => u e.1 e.2.1 e.2.2)
      (G.openValue attach (G.inputTable attach q F) x) = G.openValue attach u x := by
  simp [openValue, inputTable]

private theorem card_le_transport {α : Type*} {f g : Fintype α} {N : ℕ}
    (h : @Fintype.card α f ≤ N) : @Fintype.card α g ≤ N := by
  cases Subsingleton.elim f g
  exact h

private theorem contraction_eq_raw_pairing {J D : Type} [Fintype J] [Fintype D]
    {F R : Type*} [Field F] [CommSemiring R] (h : F →+* R)
    (H : PortGraph J D) (A : D → Type) [∀ e, Fintype (A e)]
    (U : ∀ j, (H.rawWiring F A).Leg j → R) :
    H.contraction (A := A) U = tablePairing h (H.rawWiring F A).coeff U := by
  unfold rawWiring at U ⊢
  dsimp only at U ⊢
  rw [contraction_eq_wiring]
  unfold tablePairing
  apply Finset.sum_congr (by ext; simp)
  intro a _
  congr 1
  unfold wiring
  split <;> simp

set_option maxHeartbeats 1200000 in
/-- The large-stub case of patch replacement. The closure uses an arbitrary polygon
numbering with the prescribed boundary order, ending at the designated root.
The symbolic trees and the program for their entries depend only on this numbering,
the original incidence map, and the ground field. -/
theorem large_stub_replacement {F : Type*} [Field F]
    (noPlane : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))))
    (K : ℕ) (hK : 0 < K) :
    ∃ c : ℕ, ∀ {V E B : Type} [Fintype E] [Fintype V] [Fintype B] (G : PortGraph V E) (attach : B → V) (w n : ℕ)
      (order : V ⊕ B ≃ Fin (n+1)) (b : B), order (.inr b) = Fin.last n →
      Fintype.card V ≤ K → (∀ v, Fintype.card (G.Port v) + Fintype.card {s // attach s = v} ≤ 4) →
      4 ≤ Fintype.card B →
      ∃ (L : ℕ) (u : Fin L → TrivalentTree (MvPolynomial (G.PatchEntry attach (2^w)) F)
        (fun _ : B => 2^w) (2^w)),
        L ≤ 2^(w+c) ∧
        (∀ j, (u j).labels = (List.finRange n).filterMap (fun i => stubLabel order i.castSucc) ∧
          (u j).Bounded (2^(8*w)) ∧ (u j).vertices + 2 = Fintype.card B) ∧
        (∀ j, (u j).FormulaBound (2^((20*(2*(5*K)+1)+7)*(w+1)))) ∧
        (∀ x, G.openValue attach (G.inputTable attach (2^w) F) x = ∑ j, (u j).eval x (x b)) ∧
        ∃ (r : ℕ) (p : Program F (G.PatchEntry attach (2^w)) r) (out : (j : Fin L) → (u j).Entry → Fin r),
          (∀ j e, registerPolynomial p (out j e) = (u j).entry e) ∧
          p.cost ≤ 2^((c+1+5*K+24+20*(2*(5*K)+1)+7)*(w+1)) := by
  obtain ⟨c,hc⟩ := bounded_replacement_in_format noPlane K hK
  refine ⟨c,?_⟩
  intro V E B _ _ _ G attach w n order b hroot hVK hdeg hlarge
  let H := G.closeStubs attach order
  let g := H.chordWidths (fun _ => w)
  let A := fun _ : E ⊕ B => Fin (2^w)
  let R := H.rawWiring F A
  let table := G.inputTable attach (2^w) F
  let U : ∀ i, CornerTable (MvPolynomial (G.PatchEntry attach (2^w)) F) (fun _ : B => 2^w) (R.Leg i) :=
    G.closedCorners attach order table
  obtain ⟨hv,he⟩ := G.closed_size_bounds attach hVK hdeg
  have hverts := Fintype.card_congr order
  rw [Fintype.card_fin] at hverts
  have hsum : total g ≤ 4*K*w := (H.total_chordWidths_le _).trans (by simpa using Nat.mul_le_mul_right w he)
  have hdeg' (i) : Fintype.card (H.Port i) ≤ 4 :=
    card_le_transport (G.closed_degree_le attach order hdeg i)
  have hload i : load i g ≤ 4*w := (H.load_chordWidths_le _ i).trans
    (by simpa using Nat.mul_le_mul_right w (hdeg' i))
  have hstate i : Fintype.card (R.Leg i) ≤ 2^(4*w) := by
    have h : Fintype.card (H.Port i → Fin (2^w)) ≤ 2^(4*w) := by
      rw [Fintype.card_fun, Fintype.card_fin, ← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right w (hdeg' i))
    exact card_le_transport h
  have hUF (i) : (U i).FormulaBound 1 :=
    G.closedCorners_formula attach order table (fun v a s => HasFormula.input _) i
  have hUlabel (i) : (U i).label = stubLabel order i := G.closedCorners_label attach order table i
  have hlab : (List.finRange n).filterMap (fun i => (U i.castSucc).label) =
      (List.finRange n).filterMap (fun i => stubLabel order i.castSucc) := by simp only [hUlabel]
  have hlen := nonroot_stub_count order hroot
  have hn : 0 < n := by rw [Fintype.card_sum] at hverts; omega
  obtain ⟨L,u,hL,hu,hform,hval,r,p,out,hp,hcost⟩ := hc hn (hverts ▸ hv) g hsum hload R
    (H.ofRaw_rawWiring_eq_graphClass F _) hstate U b
    (by rw [hUlabel, ← hroot]; simp [stubLabel])
    (fun _ _ _ => Nat.pow_le_pow_right (by decide) (by omega : w ≤ 8*w)) hUF
    (by rw [hlab]; omega)
  refine ⟨L,u,hL,fun j => ⟨?_,(hu j).2.1,?_⟩,hform,?_,r,p,out,hp,hcost⟩
  · simpa only [hlab] using (hu j).1
  · have hj := (hu j).2.2
    simpa only [hlab, hlen] using hj
  · intro x
    rw [G.openValue_eq_closed attach order table x]
    refine Eq.trans ?_ (hval x)
    exact contraction_eq_raw_pairing MvPolynomial.C H A (fun i => (U i).value x)

end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
