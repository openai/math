import OAI.Geometry.Hirsch.Graph

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch

structure Polytope where
  Space : Type
  [group : NormedAddCommGroup Space]
  [moduleSpace : NormedSpace ℝ Space]
  [finiteDim : FiniteDimensional ℝ Space]
  Coord : Type
  basis : Basis Coord ℝ Space
  Row : Type
  [finiteRow : Finite Row]
  sys : System Space Row
  rationalNormal : ∀ row coord, ∃ value : ℚ, sys.normal row (basis coord) = value
  rationalRhs : ∀ row, ∃ value : ℚ, sys.rhs row = value
  compact : IsCompact sys.body
  nonempty : sys.body.Nonempty

attribute [instance] Polytope.group Polytope.moduleSpace Polytope.finiteDim Polytope.finiteRow

namespace Polytope

variable (poly : Polytope)

abbrev body := poly.sys.body
abbrev V := Vertex poly.body
def dimension := dim poly.body
def facetCount := (facets poly.body).ncard
abbrev dist (moves : ℕ) := (graph poly.body moves).dist

instance : Nonempty poly.V := poly.compact.extremePoints_nonempty poly.nonempty |>.to_subtype
instance : Finite poly.V := poly.sys.finite_vertices.to_subtype

theorem connected (reg : poly.sys.Regular) {moves : ℕ} (hm : 1 ≤ moves) :
    (graph poly.body moves).Connected :=
  ⟨reg.preconnected poly.compact hm⟩

theorem dist_anti (reg : poly.sys.Regular) {small large : ℕ}
    (hs : 1 ≤ small) (hm : small ≤ large) (first last : poly.V) :
    poly.dist large first last ≤ poly.dist small first last := by
  obtain ⟨walk, hw⟩ := (poly.connected reg hs first last).exists_walk_length_eq_dist
  simpa [hw] using SimpleGraph.dist_le (walk.mapLe (graph_mono poly.body hm))

theorem adj_iff (reg : poly.sys.Regular) {moves : ℕ} {first last : poly.V} :
    (graph poly.body moves).Adj first last ↔ first ≠ last ∧
      finrank ℝ poly.Space ≤ (poly.sys.active first.val ∩ poly.sys.active last.val).ncard + moves := by
  let common := poly.sys.active first.val ∩ poly.sys.active last.val
  have hd := reg.dim_locus first.property.1 (show common ⊆ _ from inter_subset_left)
  change _ ↔ first ≠ last ∧ finrank ℝ poly.Space ≤ common.ncard + moves
  constructor
  · rintro ⟨hn, face, hf, hm, hx, hy⟩
    obtain ⟨point, hp, he⟩ := System.face_eq_locus hf ⟨_, hx⟩
    rw [he] at hx hy hm
    have hc := ncard_le_ncard (show poly.sys.active point ⊆ common from subset_inter hx.2 hy.2)
    have hk := reg.dim_locus (hf.extreme.subset hp) Subset.rfl
    exact ⟨hn, by omega⟩
  · rintro ⟨hn, hm⟩
    exact ⟨hn, poly.sys.locus common, poly.sys.isFace_locus _, by omega,
      ⟨first.property.1, inter_subset_left⟩, last.property.1, inter_subset_right⟩

structure Objective where
  lin : poly.Space →ₗ[ℝ] ℝ
  low : poly.V
  high : poly.V
  bounds : ∀ point ∈ poly.body, lin low.val ≤ lin point ∧ lin point ≤ lin high.val
  positive : lin low.val < lin high.val

def Objective.gap {poly : Polytope} (obj : poly.Objective) (first last : poly.V) : ℝ :=
  |obj.lin first.val - obj.lin last.val| / (obj.lin obj.high.val - obj.lin obj.low.val)

theorem Objective.gap_extremes {poly : Polytope} (obj : poly.Objective) :
    obj.gap obj.high obj.low = 1 := by
  have hh := sub_pos.mpr obj.positive
  simp [gap, abs_of_pos hh, hh.ne']

end Polytope
end OAI.Geometry.Hirsch
