import OAI.LinearAlgebra.SpectralBooks.PortGraph.BoundedPatchReplacementOpen
import OAI.LinearAlgebra.SpectralBooks.PortGraph.BoundedPatchReplacementOrder

/-! # Patch replacement with a prescribed cyclic order on the named stubs -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace PortGraph

open PlanarPatch Arithmetic

/-- A cut of the prescribed cyclic order lists the stubs in `Fin (b+1)`, with
the last one serving as the root. The wiring alone determines the list of
trees. Their symbolic identity specializes to every assignment of patch entries
over every commutative ground-field algebra. -/
theorem ordered_patch_replacement {F : Type*} [Field F]
    (noPlane : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))))
    (K : ℕ) (hK : 0 < K) :
    ∃ c : ℕ, ∀ {V E B : Type} [Fintype E] [Fintype V] [Fintype B]
      (G : PortGraph V E) (attach : B → V) (w b : ℕ) (stubs : B ≃ Fin (b+1)),
      Fintype.card V ≤ K → (∀ v, Fintype.card (G.Port v) + Fintype.card {s // attach s = v} ≤ 4) →
      3 ≤ b →
      ∃ (L : ℕ) (u : Fin L → TrivalentTree (MvPolynomial (G.PatchEntry attach (2^w)) F)
        (fun _ : B => 2^w) (2^w)), L ≤ 2^(w+c) ∧
        (∀ j, (u j).labels = (List.finRange b).map (fun i => stubs.symm i.castSucc) ∧
          (u j).Bounded (2^(8*w)) ∧ (u j).vertices + 2 = Fintype.card B) ∧
        (∀ j, (u j).FormulaBound (2^((20*(2*(5*K)+1)+7)*(w+1)))) ∧
        (∀ {R : Type*} [CommSemiring R] (h : F →+* R) (T : G.StubTable attach (Fin (2^w)) R)
          (x : B → Fin (2^w)), G.openValue attach T x =
            ∑ j, ((u j).map (MvPolynomial.eval₂Hom h (fun e : G.PatchEntry attach (2^w) =>
              T e.1 e.2.1 e.2.2))).eval x (x (stubs.symm (Fin.last b)))) ∧
        ∃ (r : ℕ) (p : Program F (G.PatchEntry attach (2^w)) r) (out : (j : Fin L) → (u j).Entry → Fin r),
          (∀ j e, registerPolynomial p (out j e) = (u j).entry e) ∧
          p.cost ≤ 2^((c+1+5*K+24+20*(2*(5*K)+1)+7)*(w+1)) := by
  obtain ⟨c,hc⟩ := large_stub_replacement noPlane K hK
  refine ⟨c,?_⟩
  intro V E B _ _ _ G attach w b stubs hv hd hlarge
  let old := Fintype.equivFin V
  let order := polygonOrder old stubs
  have hb : Fintype.card B = b+1 := (Fintype.card_congr stubs).trans (Fintype.card_fin _)
  obtain ⟨L,u,hL,hu,hw,hval,hprog⟩ := hc G attach w (Fintype.card V + b) order
    (stubs.symm (Fin.last b)) (polygonOrder_root old stubs) hv hd (by omega)
  refine ⟨L,u,hL,fun j => ⟨(hu j).1.trans (polygonOrder_stubs old stubs),(hu j).2⟩,
    hw,?_,hprog⟩
  intro R _ h T x
  let f := MvPolynomial.eval₂Hom h (fun e : G.PatchEntry attach (2^w) => T e.1 e.2.1 e.2.2)
  calc
    _ = f (G.openValue attach (G.inputTable attach (2^w) F) x) :=
      (G.specialize_inputTable attach _ h T x).symm
    _ = ∑ j, f ((u j).eval x (x (stubs.symm (Fin.last b)))) := by rw [hval, map_sum]
    _ = _ := Finset.sum_congr rfl (fun j _ => ((u j).eval_map f _ _).symm)

end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
