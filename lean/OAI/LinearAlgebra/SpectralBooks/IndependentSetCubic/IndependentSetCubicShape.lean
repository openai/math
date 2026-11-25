import OAI.LinearAlgebra.SpectralBooks.IndependentSetCubic.IndependentSetCubicPorts

/-! # The graph of degree at most three obtained by splitting every vertex -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace IndependentSetCubic
open scoped Classical BigOperators

variable {V E : Type*} [Fintype E] (l r : E → V)

abbrev Vertex := Copies (incidenceDegree l r) ⊕ (Links (incidenceDegree l r) ⊕ Links (incidenceDegree l r))
abbrev Edge := E ⊕ (Links (incidenceDegree l r) ⊕ (Links (incidenceDegree l r) ⊕ Links (incidenceDegree l r)))

/-- Keep the original edges at distinct ports and insert three edges on each link. -/
def left : Edge l r → Vertex l r :=
  Sum.elim (fun e => .inl (port l r (.inl e))) <|
    Sum.elim (fun j => .inl (prev j)) (Sum.elim (fun j => .inr (.inl j)) (fun j => .inr (.inr j)))

def right : Edge l r → Vertex l r :=
  Sum.elim (fun e => .inl (port l r (.inr e))) <|
    Sum.elim (fun j => .inr (.inl j)) (Sum.elim (fun j => .inr (.inr j)) (fun j => .inl (nextCopy j)))

theorem loopless (e : Edge l r) : left l r e ≠ right l r e := by
  rcases e with e | j | j | j <;> simp [left, right]

/-- Color the old edges and all middle edges alike. The two outer edges of each
link have their own colors. Incident edges have distinct colors. -/
private def color : Edge l r → Fin 3 :=
  Sum.elim (fun _ => 0) <| Sum.elim (fun _ => 1) <| Sum.elim (fun _ => 0) (fun _ => 2)

variable [Fintype V]

theorem degree_le_three (v : Vertex l r) :
    Fintype.card {e : Edge l r // left l r e = v ∨ right l r e = v} ≤ 3 := by
  let f (e : {e : Edge l r // left l r e = v ∨ right l r e = v}) := color l r e.1
  suffices hf : Function.Injective f by simpa using Fintype.card_le_of_injective f hf
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  apply Subtype.ext
  change color l r a = color l r b at h
  rcases v with v | v | v <;> rcases a with a | a | a | a <;> rcases b with b | b | b | b <;>
    simp [color, left, right] at h ha hb ⊢
  all_goals first
    | exact prev_injective (ha.trans hb.symm)
    | exact nextCopy_injective (ha.trans hb.symm)
    | exact ha.trans hb.symm
    | rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simpa using (port l r).injective (ha.trans hb.symm)

private theorem card_links : Fintype.card (Links (incidenceDegree l r)) = 4 * Fintype.card E := by
  simp only [Links, Fintype.card_sigma, Fintype.card_fin, ← Finset.mul_sum, sum_incidenceDegree]
  omega

private theorem card_copies : Fintype.card (Copies (incidenceDegree l r)) =
    Fintype.card V + 4 * Fintype.card E := by
  simp only [Copies, Fintype.card_sigma, Fintype.card_fin, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_incidenceDegree, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  omega

theorem card_vertex : Fintype.card (Vertex l r) = Fintype.card V + 12 * Fintype.card E := by
  simp only [Vertex, Fintype.card_sum, card_copies, card_links]
  omega

theorem card_edge : Fintype.card (Edge l r) = 13 * Fintype.card E := by
  simp only [Edge, Fintype.card_sum, card_links]
  omega

end IndependentSetCubic

end

end SpectralBooks
end LinearAlgebra
end OAI
