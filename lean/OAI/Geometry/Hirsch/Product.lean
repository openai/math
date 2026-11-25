import OAI.Geometry.Hirsch.Polytope

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch

theorem dist_projection {α β : Type} {outer : SimpleGraph α} {inner : SimpleGraph β}
    (proj : α → β) (hp : ∀ {u v}, outer.Adj u v → proj u = proj v ∨ inner.Adj (proj u) (proj v))
    {first last : α} (hr : outer.Reachable first last) :
    inner.dist (proj first) (proj last) ≤ outer.dist first last := by
  obtain ⟨walk, he⟩ := hr.exists_walk_length_eq_dist
  rw [← he]
  clear he hr
  induction walk with
  | nil => simp
  | @cons first next last hadj walk ih =>
    rw [SimpleGraph.Walk.length_cons]
    rcases hp hadj with he | he
    · rw [he]
      omega
    · have hh := he.reachable.dist_triangle_left (proj last)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr he] at hh
      omega

namespace Polytope

variable (left right : Polytope)

def productSystem : System (left.Space × right.Space) (left.Row ⊕ right.Row) where
  normal := Sum.elim (fun row => (left.sys.normal row).comp (LinearMap.fst ℝ _ _))
    (fun row => (right.sys.normal row).comp (LinearMap.snd ℝ _ _))
  rhs := Sum.elim left.sys.rhs right.sys.rhs

theorem productBody : (left.productSystem right).body = left.body ×ˢ right.body := by
  ext point
  constructor
  · exact fun hh => ⟨fun row => hh (.inl row), fun row => hh (.inr row)⟩
  · rintro ⟨hl, hr⟩ (row | row)
    · exact hl row
    · exact hr row

def product : Polytope where
  Space := left.Space × right.Space
  Coord := left.Coord ⊕ right.Coord
  basis := left.basis.prod right.basis
  Row := left.Row ⊕ right.Row
  sys := left.productSystem right
  rationalNormal := by
    rintro (row | row) (coord | coord)
    · simpa [productSystem] using left.rationalNormal row coord
    · exact ⟨0, by simp [productSystem]⟩
    · exact ⟨0, by simp [productSystem]⟩
    · simpa [productSystem] using right.rationalNormal row coord
  rationalRhs := by
    rintro (row | row)
    · exact left.rationalRhs row
    · exact right.rationalRhs row
  compact := by rw [productBody]; exact left.compact.prod right.compact
  nonempty := by rw [productBody]; exact left.nonempty.prod right.nonempty

theorem product_regular (hl : left.sys.Regular) (hr : right.sys.Regular) :
    (left.product right).sys.Regular := by
  change (left.productSystem right).Regular
  intro point hp values
  rw [productBody] at hp
  obtain ⟨dl, hdl⟩ := hl _ hp.1 (values ∘ Sum.inl)
  obtain ⟨dr, hdr⟩ := hr _ hp.2 (values ∘ Sum.inr)
  refine ⟨(dl, dr), ?_⟩
  rintro (row | row) hh
  · exact hdl row hh
  · exact hdr row hh

theorem product_dimension (hl : left.sys.Regular) (hr : right.sys.Regular) :
    (left.product right).dimension = left.dimension + right.dimension := by
  unfold dimension
  rw [(left.product_regular right hl hr).dim_body (left.product right).nonempty,
    hl.dim_body left.nonempty, hr.dim_body right.nonempty]
  exact finrank_prod

private theorem sum_count {α β : Type} [Finite α] [Finite β] (rows : Set (α ⊕ β)) :
    rows.ncard = (Sum.inl ⁻¹' rows).ncard + (Sum.inr ⁻¹' rows).ncard := by
  have he : rows = Sum.inl '' (Sum.inl ⁻¹' rows) ∪ Sum.inr '' (Sum.inr ⁻¹' rows) := by
    ext (row | row) <;> simp
  nth_rw 1 [he]
  rw [ncard_union_eq disjoint_image_inl_image_inr, ncard_image_of_injective _ Sum.inl_injective,
    ncard_image_of_injective _ Sum.inr_injective]

theorem product_facetCount (hl : left.sys.Regular) (hr : right.sys.Regular) :
    (left.product right).facetCount = left.facetCount + right.facetCount := by
  unfold facetCount
  rw [(left.product_regular right hl hr).facet_count, hl.facet_count, hr.facet_count]
  change (left.productSystem right).used.ncard = _
  rw [sum_count]
  congr 2
  · ext row
    constructor
    · rintro ⟨point, hp, hh⟩
      exact ⟨point.1, (left.productBody right ▸ hp).1, hh⟩
    · rintro ⟨point, hp, hh⟩
      obtain ⟨other, ho⟩ := right.nonempty
      exact ⟨(point, other), (left.productBody right).symm ▸ ⟨hp, ho⟩, hh⟩
  · ext row
    constructor
    · rintro ⟨point, hp, hh⟩
      exact ⟨point.2, (left.productBody right ▸ hp).2, hh⟩
    · rintro ⟨point, hp, hh⟩
      obtain ⟨other, ho⟩ := left.nonempty
      exact ⟨(other, point), (left.productBody right).symm ▸ ⟨ho, hp⟩, hh⟩

theorem product_vertices : (left.productSystem right).body.extremePoints ℝ =
    left.body.extremePoints ℝ ×ˢ right.body.extremePoints ℝ := by
  rw [productBody, extremePoints_prod]

def pair (first : left.V) (second : right.V) : (left.product right).V :=
  ⟨(first.val, second.val), (left.product_vertices right).symm ▸ ⟨first.property, second.property⟩⟩

def project (point : (left.product right).V) : left.V :=
  ⟨point.val.1, ((left.product_vertices right).subset point.property).1⟩

theorem product_dist (hl : left.sys.Regular) (hr : right.sys.Regular)
    {moves : ℕ} (hm : 1 ≤ moves) (first last : (left.product right).V) :
    left.dist moves (left.project right first) (left.project right last) ≤
      (left.product right).dist moves first last := by
  have reg := left.product_regular right hl hr
  apply dist_projection (left.project right) _ ((left.product right).connected reg hm first last)
  intro src dst hadj
  by_cases he : left.project right src = left.project right dst
  · exact Or.inl he
  right
  refine (left.adj_iff hl).mpr ⟨he, ?_⟩
  have hh := (((left.product right).adj_iff reg).mp hadj).2
  change finrank ℝ (left.Space × right.Space) ≤
    ((left.productSystem right).active src.val ∩ (left.productSystem right).active dst.val).ncard +
      moves at hh
  rw [finrank_prod, sum_count] at hh
  change _ ≤ (left.sys.active src.val.1 ∩ left.sys.active dst.val.1).ncard +
    (right.sys.active src.val.2 ∩ right.sys.active dst.val.2).ncard + moves at hh
  have hv := ((left.product_vertices right).subset src.property).2
  have hd := (hr.vertex_card hv.1).mp hv
  have hc := ncard_le_ncard (inter_subset_left (s := right.sys.active src.val.2)
    (t := right.sys.active dst.val.2))
  change _ ≤ (left.sys.active src.val.1 ∩ left.sys.active dst.val.1).ncard + moves
  omega

def productObjective (obj : left.Objective) : (left.product right).Objective where
  lin := obj.lin.comp (LinearMap.fst ℝ _ _)
  low := left.pair right obj.low (Classical.arbitrary _)
  high := left.pair right obj.high (Classical.arbitrary _)
  bounds point hp := obj.bounds point.1 ((left.productBody right).subset hp).1
  positive := obj.positive

end Polytope
end OAI.Geometry.Hirsch
