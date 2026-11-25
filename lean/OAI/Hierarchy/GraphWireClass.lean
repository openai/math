import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortWiringClass

namespace OAI
/-! # The graph coefficient tensor on its separate edge ends

Each edge has two independent indices. Its equality test is a two-site
diagonal, so the tensor on all edge ends represents the product of these
individual diagonals in the tensor semiring.
-/

namespace Hierarchy

open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators
noncomputable section

/-- One independent equality test per edge, with a separate site for each end. -/
def equalityWireRaw (E : Type) [Fintype E] (F : Type*) [Field F] (q : ℕ) :
    Raw.{0} (E × Bool) F where
  Leg _ := Fin q
  finiteLeg _ := inferInstance
  coeff x := ∏ e, if x (e,false) = x (e,true) then 1 else 0

theorem equalityWireRaw_coeff_ne_zero (E : Type) [Fintype E] (F : Type*) [Field F]
    (q : ℕ) (hq : 0 < q) : (equalityWireRaw E F q).coeff ≠ 0 := by
  intro h
  have h0 : (equalityWireRaw E F q).coeff (fun _ => (⟨0,hq⟩ : Fin q)) = (0 : F) :=
    congrFun h _
  simp [equalityWireRaw] at h0

private def endPairing (E : Type) : PortGraph (E × Bool) E :=
  ⟨fun e => (e,false), fun e => (e,true)⟩

private theorem vertex_endPairing {E : Type} (p : E × Bool) :
    (endPairing E).vertex p.1 p.2 = p := by
  obtain ⟨e,b⟩ := p
  cases b <;> rfl

private def singletonPortState {E : Type} (q : ℕ) (p : E × Bool) :
    Fin q ≃ (endPairing E).State (fun _ => Fin q) p where
  toFun a _ := a
  invFun y := y ⟨p, vertex_endPairing p⟩
  left_inv _ := rfl
  right_inv y := by
    funext t
    exact congrArg y (Subtype.ext ((vertex_endPairing t.val).symm.trans t.property).symm)

/-- Keeping the two ends of every wire as separate sites realizes the product
of the `q`-dimensional two-site wires in the restriction semiring. -/
theorem ofRaw_equalityWireRaw (E : Type) [Fintype E] [Nonempty E]
    (F : Type*) [Field F] (q : ℕ) :
    ofRaw (equalityWireRaw E F q) =
      ∏ e : E, ofRaw ((Raw.diagonal (Fin 2) F (Fin q)).group ![(e,false),(e,true)]) := by
  classical
  let G := endPairing E
  change _ = ∏ e : E, ofRaw (G.edgeRaw F (fun _ => Fin q) e)
  rw [← G.ofRaw_rawWiring]
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (singletonPortState q)
  intro (x : E × Bool → Fin q)
  simp only [equalityWireRaw, PortGraph.rawWiring, PortGraph.wiring]
  by_cases h : ∀ e : E, x (e,false) = x (e,true)
  · trans (1 : F)
    · apply Finset.prod_eq_one
      exact fun e _ => ite_eq_left (h e)
    · symm
      apply ite_eq_left
      exact h
  · trans (0 : F)
    · obtain ⟨e, he⟩ := not_forall.mp h
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      exact ite_eq_right he
    · symm
      apply ite_eq_right
      exact h

end
end Hierarchy

end OAI
