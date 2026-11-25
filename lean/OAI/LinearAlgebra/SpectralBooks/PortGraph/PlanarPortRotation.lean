import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchAveraging
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarSeparatorCharge
import OAI.Geometry.HyperbolicGroups.PictureFullSeparator

/-! # Balanced separators for spherical port graphs

Turning around each vertex gives a permutation of the darts. Crossing an edge
and turning once gives the face permutation. This realizes a port graph as a
finite rotation system so that the planar separator theorem applies.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph

open HyperbolicObstruction.PictureSwitch
open SpectralBooks.PlanarPatch

variable {V E : Type*} (G : PortGraph V E)

/-- The cyclic successor on ports has exactly one cycle at each nonisolated vertex. -/
structure Rotation where
  turn : Equiv.Perm (E × Bool)
  sameCycle : ∀ a b, turn.SameCycle a b ↔ G.vertex a.1 a.2 = G.vertex b.1 b.2

/-- Switch to the port at the other end of this edge. -/
def cross : Equiv.Perm (E × Bool) where
  toFun p := (p.1, !p.2)
  invFun p := (p.1, !p.2)
  left_inv := by rintro ⟨e, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨e, b⟩; cases b <;> rfl

private theorem cross_sq : (cross (E := E)) * cross = 1 := by
  apply Equiv.ext
  rintro ⟨e, b⟩
  cases b <;> rfl

namespace Rotation

variable {G} (ρ : G.Rotation)

/-- The boundary permutation of an oriented ribbon graph turns immediately
after crossing the edge. -/
def picture : PictureMap (E × Bool) where
  face := ρ.turn * cross
  edge := cross
  edge_sq := cross_sq
  edge_ne := by
    rintro ⟨e, b⟩ h
    have := congrArg Prod.snd h
    cases b <;> contradiction

@[simp] theorem picture_vertex : ρ.picture.vertex = ρ.turn := by
  change (ρ.turn * cross) * cross = ρ.turn
  rw [mul_assoc, cross_sq, mul_one]

/-- Map each vertex to its literal dart cycle. All vertices are incident when
a connected graph has more than one vertex. -/
noncomputable def vertexCycle (hp : ∀ v, Nonempty (G.Port v)) (v : V) : ρ.picture.GraphVertex :=
  ρ.picture.vertexClass (Classical.choice (hp v)).val

@[simp] theorem vertexCycle_port (hp : ∀ v, Nonempty (G.Port v)) (p : E × Bool) :
    ρ.vertexCycle hp (G.vertex p.1 p.2) = ρ.picture.vertexClass p := by
  apply (ρ.picture.vertexClass_eq_iff _ _).mpr
  rw [ρ.picture_vertex, ρ.sameCycle]
  exact (Classical.choice (hp _)).property

theorem vertexCycle_injective (hp : ∀ v, Nonempty (G.Port v)) :
    Function.Injective (ρ.vertexCycle hp) := by
  intro v w h
  have h' := (ρ.picture.vertexClass_eq_iff _ _).mp h
  rw [ρ.picture_vertex, ρ.sameCycle] at h'
  exact (Classical.choice (hp v)).property.symm.trans (h'.trans (Classical.choice (hp w)).property)

/-- Parallel edges retain their darts, and loops induce no simple adjacency. -/
noncomputable def graphHom (hp : ∀ v, Nonempty (G.Port v)) :
    underlying G.tail G.head →g ρ.picture.underlyingGraph where
  toFun := ρ.vertexCycle hp
  map_rel' := by
    rintro v w ⟨hne, e, he⟩
    refine ⟨(ρ.vertexCycle_injective hp).ne hne, ?_⟩
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨(e, false), (ρ.vertexCycle_port hp (e, false)).symm,
        (ρ.vertexCycle_port hp (e, true)).symm⟩
    · exact ⟨(e, true), (ρ.vertexCycle_port hp (e, true)).symm,
        (ρ.vertexCycle_port hp (e, false)).symm⟩

theorem ports_nonempty [Nontrivial V] (hc : (underlying G.tail G.head).Preconnected) (v : V) :
    Nonempty (G.Port v) := by
  obtain ⟨w, _, e, he⟩ := hc.exists_adj_of_nontrivial v
  rcases he with ⟨hh, _⟩ | ⟨_, hh⟩
  · exact ⟨(e, false), hh⟩
  · exact ⟨(e, true), hh⟩

variable [DecidableEq E] [Fintype E] [DecidableEq V]

/-- The hereditary separator bound follows from genus zero of the rotation
system. The subsingleton case also includes the isolated root with no darts. -/
theorem balancedSeparators (hc : (underlying G.tail G.head).Connected)
    (hg : ρ.picture.GenusZero) (S : Finset V) :
    BalancedSeparators (underlying G.tail G.head) S 11 := by
  classical
  intro T _ hn
  cases subsingleton_or_nontrivial V with
  | inl h =>
    refine ⟨T, Finset.Subset.refl _, ∅, ?_, ?_, ?_⟩
    · rw [Finset.sdiff_self]
      exact ⟨by simp, by simp, by simp, by simp, by simp⟩
    · have hcard : T.card = 1 := by
        have hle := Finset.card_le_one_of_subsingleton T
        have hpos := Finset.card_pos.mpr hn
        omega
      rw [hcard]
      norm_num
    · simp
  | inr h =>
    let hp := ports_nonempty hc.preconnected
    obtain ⟨D, hD, hcost, hparts⟩ := HyperbolicObstruction.PlanarRecursion.component_separator_pullback
      _ _ (ρ.graphHom hp) (ρ.vertexCycle_injective hp) 11 (ρ.picture.genusZero_component_separator hg) T
    obtain ⟨blocks, hblocks⟩ := componentPieces_exists (underlying G.tail G.head) (T \ D)
    refine ⟨D, hD, blocks, hblocks, ?_, ?_⟩
    · calc
        (D.card : ℝ) ≤ 11 * (Nat.sqrt T.card : ℝ) := by exact_mod_cast hcost
        _ ≤ 11 * Real.sqrt T.card := by gcongr; exact Real.nat_sqrt_le_real_sqrt
    · intro P hP
      have hp := hblocks.subset P hP
      have hh := hparts P (hp.trans Finset.sdiff_subset)
        (Finset.disjoint_left.mpr fun v hv => (Finset.mem_sdiff.mp (hp hv)).2) (hblocks.connected P hP).preconnected
      omega

end Rotation
end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
