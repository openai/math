import OAI.Geometry.Hirsch.Perturbation

noncomputable section

open Set Module Filter
open scoped Topology

namespace OAI.Geometry.Hirsch

variable {Space Row Coord : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [FiniteDimensional ℝ Space] [Fintype Row]

def System.Chain (sys : System Space Row) (allowed : Set Row → Prop)
    {len : ℕ} (pts : Fin (len + 1) → Space) : Prop :=
  (∀ idx, pts idx ∈ sys.body) ∧ ∀ idx : Fin len, ∃ rows, allowed rows ∧
    rows ⊆ sys.active (pts idx.castSucc) ∧ rows ⊆ sys.active (pts idx.succ)

def System.Cost (sys : System Space Row) (allowed : Set Row → Prop)
    (obj : Space →ₗ[ℝ] ℝ) (sep : ℝ) (cost : ℕ) : Prop :=
  ∀ len (pts : Fin (len + 1) → Space), sys.Chain allowed pts →
    sep ≤ |obj (pts 0) - obj (pts (Fin.last len))| → cost ≤ len

def System.lowDim (sys : System Space Row) (moves : ℕ) (rows : Set Row) : Prop :=
  finrank ℝ (sys.directions rows) ≤ moves

def manyRows (Space : Type) [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (moves : ℕ) (rows : Set Row) : Prop :=
  finrank ℝ Space ≤ rows.ncard + moves

theorem System.Regular.cost_card {sys : System Space Row} (reg : sys.Regular)
    {moves : ℕ} {obj : Space →ₗ[ℝ] ℝ} {sep : ℝ} {cost : ℕ}
    (hc : sys.Cost (sys.lowDim moves) obj sep cost) :
    sys.Cost (manyRows Space moves) obj sep cost := by
  intro len pts ⟨hp, ha⟩
  refine hc len pts ⟨hp, fun idx => ?_⟩
  obtain ⟨rows, hn, hl, hr⟩ := ha idx
  have hh := reg.rank (hp _) hl
  exact ⟨rows, by unfold manyRows at hn; unfold System.lowDim; omega, hl, hr⟩

namespace Data

omit [FiniteDimensional ℝ Space] [Fintype Row] in
theorem closed_active {Param : Type} [TopologicalSpace Param]
    {get : Param → Data Space Row} {point : Param → Space}
    (hg : Continuous get) (hp : Continuous point) (rows : Set Row) :
    IsClosed {param | rows ⊆ (get param).sys.active (point param)} := by
  change IsClosed {param | ∀ row ∈ rows, (get param).1 row (point param) = (get param).2 row}
  simp only [ofPred_forall]
  exact isClosed_iInter fun row => isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)

omit [FiniteDimensional ℝ Space] in
theorem closed_chain (allowed : Set Row → Prop) (len : ℕ) :
    IsClosed {pair : Data Space Row × (Fin (len + 1) → Space) |
      pair.1.sys.Chain allowed pair.2} := by
  simp only [System.Chain, ofPred_and, ofPred_forall, ofPred_exists]
  refine (isClosed_iInter fun idx => closed_body continuous_fst (by fun_prop)).inter ?_
  refine isClosed_iInter fun idx => isClosed_iUnion_of_finite fun rows => ?_
  exact isClosed_const.inter ((closed_active continuous_fst (by fun_prop) rows).inter
    (closed_active continuous_fst (by fun_prop) rows))

variable {data : Data Space Row} {allowed : Set Row → Prop} {cost moves : ℕ}
  {obj : Space →ₗ[ℝ] ℝ} {sep : ℝ} {first last : Space}

theorem stable_cost (compact : IsCompact data.sys.body) (hp : data.Strict first)
    (hc : data.sys.Cost allowed obj sep cost) :
    ∀ᶠ other in 𝓝 data, IsCompact other.sys.body ∧ other.sys.Cost allowed obj sep cost := by
  obtain ⟨box, hb, hev⟩ := uniform_compact compact hp
  have hshort : ∀ᶠ other in 𝓝 data, ∀ len : Fin cost,
      ∀ pts ∈ univ.pi (fun _ : Fin (len.val + 1) => box),
        ¬(other.sys.Chain allowed pts ∧ sep ≤ |obj (pts 0) - obj (pts (Fin.last len.val))|) := by
    apply eventually_all.mpr
    intro len
    apply (isCompact_univ_pi fun _ => hb).eventually_forall_of_forall_eventually
    intro pts _
    have hcont := obj.continuous_of_finiteDimensional
    have hcl : IsClosed {pair : Data Space Row × (Fin (len.val + 1) → Space) |
        sep ≤ |obj (pair.2 0) - obj (pair.2 (Fin.last len.val))|} :=
      isClosed_le continuous_const (by fun_prop)
    apply ((closed_chain allowed len.val).inter hcl).isOpen_compl.mem_nhds
    exact fun hh => len.isLt.not_ge (hc len pts hh.1 hh.2)
  filter_upwards [hev, hshort] with other ho hs
  refine ⟨hb.of_isClosed_subset other.sys.isClosed_body ho, ?_⟩
  intro len pts hh hsep
  by_contra! hn
  exact hs ⟨len, hn⟩ pts (fun idx _ => ho (hh.1 idx)) ⟨hh, hsep⟩

theorem regularize (compact : IsCompact data.sys.body) (hf : data.Strict first)
    (hl : data.Strict last) (hc : data.sys.Cost (data.sys.lowDim moves) obj sep cost) :
    ∃ other : Data Space Row, IsCompact other.sys.body ∧ other.Strict first ∧ other.Strict last ∧
      other.sys.Cost (manyRows Space moves) obj sep cost := by
  have he := (stable_cost compact hf hc).and (hf.eventually.and hl.eventually)
  have ht : Tendsto (fun rhs => (data.1, rhs)) (𝓝 data.2) (𝓝 data) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  obtain ⟨rhs, ⟨⟨hb, hh⟩, hfirst, hlast⟩, hreg, _⟩ :=
    mem_closure_iff_nhds.mp (dense_regular_rhs data.1 data.2) _ (ht.eventually he)
  exact ⟨(data.1, rhs), hb, hfirst, hlast, hreg.cost_card hh⟩

end Data

theorem Polytope.distance_of_cost (poly : Polytope) (reg : poly.sys.Regular)
    {obj : poly.Space →ₗ[ℝ] ℝ} {sep : ℝ} {cost moves : ℕ} (hm : 1 ≤ moves)
    (hc : poly.sys.Cost (manyRows poly.Space moves) obj sep cost)
    (first last : poly.V) (hs : sep ≤ |obj first.val - obj last.val|) :
    cost ≤ poly.dist moves first last := by
  obtain ⟨walk, he⟩ := (poly.connected reg hm first last).exists_walk_length_eq_dist
  change cost ≤ (graph poly.body moves).dist first last
  rw [← he]
  let pts := fun idx : Fin (walk.length + 1) => (walk.getVert idx.val).val
  refine hc walk.length pts ⟨fun idx => (walk.getVert idx.val).property.1, fun idx => ?_⟩ ?_
  · have ha := ((poly.adj_iff reg).mp (walk.adj_getVert_succ idx.isLt)).2
    exact ⟨_, ha, inter_subset_left, inter_subset_right⟩
  · simpa [pts] using hs

theorem rationalize [Fintype Coord] (basis : Basis Coord ℝ Space)
    {data : Data Space Row} {obj : Space →ₗ[ℝ] ℝ} {sep : ℝ} {cost moves : ℕ}
    {first last : Space} (compact : IsCompact data.sys.body)
    (hf : data.Strict first) (hl : data.Strict last) (hgap : 1 ≤ obj last - obj first)
    (hm : 1 ≤ moves) (hc : data.sys.Cost (data.sys.lowDim moves) obj sep cost) :
    ∃ poly : Polytope, ∃ objective : poly.Objective, poly.sys.Regular ∧
      poly.dimension = finrank ℝ Space ∧ poly.facetCount ≤ Fintype.card Row ∧
      ∀ src dst, sep ≤ objective.gap src dst → cost ≤ poly.dist moves src dst := by
  obtain ⟨realData, hb, hfirst, hlast, hcost⟩ := Data.regularize compact hf hl hc
  obtain ⟨rat, ⟨⟨hcompact, hc'⟩, hf', hl'⟩, reg, hn, hr⟩ := Data.exists_rational_regular basis
    ((Data.stable_cost hb hfirst hcost).and (hfirst.eventually.and hlast.eventually))
  let poly : Polytope := {
    Space := Space, Coord := Coord, Row := Row, basis := basis, sys := rat.sys,
    rationalNormal := hn, rationalRhs := hr, compact := hcompact, nonempty := ⟨first, hf'.mem⟩ }
  obtain ⟨high, hu⟩ := vertex_max hcompact poly.nonempty obj
  obtain ⟨low, hd⟩ := vertex_max hcompact poly.nonempty (-obj)
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at hd
  have hw : 1 ≤ obj high.val - obj low.val := by linarith [hu _ hl'.mem, hd _ hf'.mem]
  let objective : poly.Objective :=
    ⟨obj, low, high, fun pt hp => ⟨hd pt hp, hu pt hp⟩, by change obj low.val < obj high.val; linarith⟩
  refine ⟨poly, objective, reg, reg.dim_body poly.nonempty, ?_, ?_⟩
  · change (facets rat.sys.body).ncard ≤ _
    rw [reg.facet_count]
    simpa using ncard_le_ncard (subset_univ rat.sys.used)
  · intro src dst hsep
    apply poly.distance_of_cost reg hm hc' src dst
    exact hsep.trans (div_le_self (abs_nonneg _) hw)

end OAI.Geometry.Hirsch
