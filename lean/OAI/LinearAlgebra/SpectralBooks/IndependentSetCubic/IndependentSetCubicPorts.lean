import OAI.LinearAlgebra.SpectralBooks.IndependentSetCubic.IndependentSetSignedPath

/-! # Ports for the cubic independent-set reduction

Enumerating the incident ends at each vertex assigns every end to a different
copy in that vertex's chain.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace IndependentSetCubic

open scoped Classical BigOperators

variable {V E : Type*} {d : V → ℕ}

theorem prev_injective : Function.Injective (prev (d := d)) :=
  (Function.Embedding.sigmaMap (β := fun v => Fin (2 * d v)) (β' := fun v => Fin (2 * d v + 1))
    (Function.Embedding.refl V) (fun v => Fin.castSuccEmb (n := 2 * d v))).injective

theorem nextCopy_injective : Function.Injective (nextCopy (d := d)) :=
  (Function.Embedding.sigmaMap (β := fun v => Fin (2 * d v)) (β' := fun v => Fin (2 * d v + 1))
    (Function.Embedding.refl V) (fun v => Fin.succEmb (2 * d v))).injective

def flagVertex (l r : E → V) : E ⊕ E → V := Sum.elim l r

variable [Fintype E]

def incidenceDegree (l r : E → V) (v : V) : ℕ :=
  Fintype.card {p : E ⊕ E // flagVertex l r p = v}

/-- Number the ends at each vertex, then embed their numbers into its copy chain. -/
def port (l r : E → V) : E ⊕ E ↪ Copies (incidenceDegree l r) :=
  (Equiv.sigmaFiberEquiv (flagVertex l r)).symm.toEmbedding.trans <|
    Function.Embedding.sigmaMap (Function.Embedding.refl V) fun v =>
      (Fintype.equivFin {p : E ⊕ E // flagVertex l r p = v}).toEmbedding.trans
        (Fin.castLEEmb (show incidenceDegree l r v ≤ 2 * incidenceDegree l r v + 1 by omega))

@[simp] theorem port_fst (l r : E → V) (p : E ⊕ E) :
    (port l r p).1 = flagVertex l r p := rfl

theorem sum_incidenceDegree [Fintype V] (l r : E → V) :
    ∑ v, incidenceDegree l r v = 2 * Fintype.card E := by
  simpa [Fintype.card_sigma, Fintype.card_sum, two_mul, incidenceDegree] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv (flagVertex l r))

theorem incidenceDegree_eq_card_incident (l r : E → V) (hloop : ∀ e, l e ≠ r e) (v : V) :
    incidenceDegree l r v = Fintype.card {e : E // l e = v ∨ r e = v} := by
  have hd : Disjoint (fun e => l e = v) (fun e => r e = v) := by
    intro t hl hr e he
    exact hloop e ((hl e he).trans (hr e he).symm)
  exact Fintype.card_congr (Equiv.subtypeSum.trans <| (subtypeOrEquiv _ _ hd).symm)

end IndependentSetCubic

end

end SpectralBooks
end LinearAlgebra
end OAI
