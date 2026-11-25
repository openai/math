import OAI.LinearAlgebra.SpectralBooks.PlanarFace.PlanarFaceCertificate
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPortRotation

/-!
# Euler's test on the port graph

For a connected rotation system with edges, its vertex cycles are the
graph vertices, and its darts give two representatives of each edge. The
count of certified face minima therefore gives the exact graph-level Euler
test. For the isolated vertex, the convention of one exterior face is used.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph

variable {V E : Type*} (G : PortGraph V E)

private theorem port_eq_of_number_eq (num : (v : V) → G.Port v ↪ Fin 4)
    {v w : V} (p : G.Port v) (q : G.Port w) (hv : v = w)
    (hn : num v p = num w q) : p.val = q.val := by
  subst w
  exact congrArg Subtype.val ((num v).injective hn)

/-- Name a port by the name of its incident vertex followed by its number
there. Injectivity holds for the two distinct ports of a loop as well. -/
def namedPortKey (key : V ↪ ℕ) (num : (v : V) → G.Port v ↪ Fin 4) :
    (E × Bool) ↪ (ℕ ×ₗ Fin 4) where
  toFun d := toLex (key (G.vertex d.1 d.2), num _ ⟨d, rfl⟩)
  inj' := by
    intro a b h
    have h₁ := congrArg (fun k : ℕ ×ₗ Fin 4 => (ofLex k).1) h
    have h₂ := congrArg (fun k : ℕ ×ₗ Fin 4 => (ofLex k).2) h
    exact port_eq_of_number_eq G num ⟨a, rfl⟩ ⟨b, rfl⟩ (key.injective h₁) h₂

/-- The exact port order used to identify the least port on a face. -/
@[instance_reducible] def namedPortOrder (key : V ↪ ℕ) (num : (v : V) → G.Port v ↪ Fin 4) : LinearOrder (E × Bool) :=
  LinearOrder.lift' (G.namedPortKey key num) (G.namedPortKey key num).injective

theorem namedPortOrder_lt (key : V ↪ ℕ) (num : (v : V) → G.Port v ↪ Fin 4) (a b : E × Bool) :
    letI := G.namedPortOrder key num
    a < b ↔ key (G.vertex a.1 a.2) < key (G.vertex b.1 b.2) ∨
      (key (G.vertex a.1 a.2) = key (G.vertex b.1 b.2) ∧ num _ ⟨a, rfl⟩ < num _ ⟨b, rfl⟩) :=
  Prod.Lex.toLex_lt_toLex

namespace Rotation

open Equiv HyperbolicObstruction.PictureSwitch PlanarPatch

variable {G} (ρ : G.Rotation)

theorem nonempty_ports_of_connected [Nonempty E] (hc : (underlying G.tail G.head).Connected)
    (v : V) : Nonempty (G.Port v) := by
  cases subsingleton_or_nontrivial V with
  | inl h => exact ⟨(Classical.choice ‹Nonempty E›, false), Subsingleton.elim _ _⟩
  | inr h => exact ports_nonempty hc.preconnected v

variable [DecidableEq E] [Fintype E]

omit [DecidableEq E] [Fintype E] in
/-- Every vertex-cycle in the picture is the cycle of an original vertex. -/
theorem vertexCycle_bijective (hp : ∀ v, Nonempty (G.Port v)) :
    Function.Bijective (ρ.vertexCycle hp) := by
  refine ⟨ρ.vertexCycle_injective hp, ?_⟩
  intro a
  induction a using Quotient.inductionOn with
  | h p => exact ⟨G.vertex p.1 p.2, ρ.vertexCycle_port hp p⟩

omit [DecidableEq E] in
/-- All the darts of a connected graph with edges belong to a single
component of the picture. -/
theorem picture_component_card [Nonempty E] (hc : (underlying G.tail G.head).Connected) :
    Nat.card (Quotient ρ.picture.components) = 1 := by
  let hp := nonempty_ports_of_connected hc
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨?_⟩, ⟨Quotient.mk _ (Classical.choice ‹Nonempty E›, false)⟩⟩
  intro a b
  induction a,b using Quotient.inductionOn₂ with
  | h p q =>
    apply Quotient.sound
    apply (ρ.picture.underlying_reachable_iff p q).mp
    have h := (hc (G.vertex p.1 p.2) (G.vertex q.1 q.2)).map (ρ.graphHom hp)
    change ρ.picture.underlyingGraph.Reachable (ρ.vertexCycle hp (G.vertex p.1 p.2))
      (ρ.vertexCycle hp (G.vertex q.1 q.2)) at h
    simpa only [vertexCycle_port] using h

variable [Fintype V]

/-- The vertex term in the side-pairing Euler formula is the graph's actual
vertex count when every vertex is incident to a port. -/
theorem picture_vertex_count (hp : ∀ v, Nonempty (G.Port v)) :
    cycles ρ.picture.vertex = (Fintype.card V : ℤ) := by
  rw [cycles_eq_card_classes]
  have he := Nat.card_congr (Equiv.ofBijective (ρ.vertexCycle hp) (ρ.vertexCycle_bijective hp))
  exact_mod_cast he.symm.trans Nat.card_eq_fintype_card

omit [DecidableEq E] [Fintype E] in
private theorem isolated_vertex_card [IsEmpty E] (hc : (underlying G.tail G.head).Connected) :
    Fintype.card V = 1 := by
  have hg : underlying G.tail G.head = ⊥ := by
    ext v w
    simp [underlying]
  rw [hg] at hc
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_eq_one_iff_unique.mpr (SimpleGraph.connected_bot_iff.mp hc)

omit [Fintype V] in
private theorem picture_genusZero_of_no_edges [IsEmpty E] : ρ.picture.GenusZero := by
  simp [PictureMap.GenusZero, PictureMap.euler, cycles_eq_card_classes]

/-- With the manuscript's single-face convention on the isolated vertex, the
reported graph counts test precisely genus zero of the connected rotation system. -/
theorem certifiedEuler_iff_genusZero [LinearOrder (E × Bool)]
    (hc : (underlying G.tail G.head).Connected) {record : (E × Bool) → (E × Bool) × ℕ}
    (h : PlanarFace.Valid ρ.picture.face record) :
    (Fintype.card V : ℤ) - Fintype.card E + PlanarFace.faceCount record = 2 ↔ ρ.picture.GenusZero := by
  cases isEmpty_or_nonempty E with
  | inl hE =>
    rw [isolated_vertex_card hc]
    simp [PlanarFace.faceCount_dartless, ρ.picture_genusZero_of_no_edges]
  | inr hE =>
    have hcounts := ρ.picture_vertex_count (nonempty_ports_of_connected hc)
    have hfaces := PlanarFace.faceCount_eq_cycles h
    rw [hfaces, ← hcounts, PictureMap.GenusZero, PictureMap.euler, ρ.picture_component_card hc]
    simp only [cycles_eq_card_classes, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    omega

end Rotation
end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
