import OAI.Geometry.Hirsch.Signatures

noncomputable section

open Set Filter
open scoped Topology

namespace OAI.Geometry.Hirsch

namespace System

variable {E R : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype R] (sys : System E R)

theorem nearby_vertices {eps : ℝ} (he : 0 < eps) :
    ∀ᶠ rhs in 𝓝 sys.rhs, ∀ x ∈ (sys.assign rhs).body.extremePoints ℝ,
      ∃ y ∈ sys.body.extremePoints ℝ, (sys.assign rhs).active x ⊆ sys.active y ∧ dist x y < eps := by
  have near : ∀ᶠ rhs in 𝓝 sys.rhs, ∀ rows : Set R, sys.directions rows = ⊥ →
      ∀ x y, rows ⊆ (sys.assign rhs).active x → rows ⊆ sys.active y → dist x y < eps := by
    apply eventually_all.mpr
    intro rows
    by_cases hd : sys.directions rows = ⊥
    swap
    · exact Eventually.of_forall (fun _ hh => (hd hh).elim)
    obtain ⟨solve,hs⟩ := sys.determining rows hd
    filter_upwards [solve.continuous_of_finiteDimensional.continuousAt.eventually
      (Metric.ball_mem_nhds (solve sys.rhs) he)] with rhs hh _ x y hx hy
    rwa [← hs rhs x hx, ← hs sys.rhs y hy]
  filter_upwards [near,sys.stable_patterns sys.rhs] with rhs hn hh x hx
  let rows := (sys.assign rhs).active x
  have hd : sys.directions rows = ⊥ := (vertex_iff hx.1).mp hx
  obtain ⟨y,hy,ha⟩ := hh rows hd ⟨x,hx.1,Subset.rfl⟩
  refine ⟨y,(vertex_iff hy).mpr ?_,ha,hn rows hd x y Subset.rfl ha⟩
  apply le_bot_iff.mp
  intro dir hv
  rw [← hd]
  exact (mem_directions _).mpr fun row hr => (mem_directions _).mp hv row (ha hr)

end System

namespace Layer

variable {V : ℕ}

abbrev Values (V : ℕ) := Vec (Fin V)

def dot (c : Values V) : Values V →ₗ[ℝ] ℝ where
  toFun z := ∑ l, c l * z l
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum, mul_left_comm]

def region (cuts : Finset (Values V)) : System (Values V) (Fin V ⊕ ↥cuts) where
  normal := Sum.elim LinearMap.proj (fun c => dot c.val)
  rhs := Sum.elim (fun _ => 0) (fun _ => 1)

theorem mem_region {cuts : Finset (Values V)} {x : Values V} :
    x ∈ (region cuts).body ↔ (∀ l, 0 ≤ x l) ∧ ∀ c ∈ cuts, 1 ≤ dot c x := by
  exact ⟨fun hx => ⟨fun l => hx (.inl l),fun c hc => hx (.inr ⟨c,hc⟩)⟩,
    fun ⟨hl,hc⟩ row => by cases row with
      | inl l => exact hl l
      | inr c => exact hc _ c.property⟩

def Pinned (cuts : Finset (Values V)) (x : Values V) (tol : ℝ) : Prop :=
  ∀ dir : Values V, (∀ l, x l ≤ tol → dir l = 0) →
    (∀ c ∈ cuts, dot c x = 1 → dot c dir = 0) → dir = 0

theorem pinned_vertex (cuts : Finset (Values V)) {eps : ℝ} (he : 0 < eps) :
    ∃ tau > 0, ∀ tol ≤ tau, ∀ x ∈ (region cuts).body, Pinned cuts x tol →
      ∃ y ∈ (region cuts).body.extremePoints ℝ,
        (∀ l, x l ≤ tol → y l = 0) ∧ ∀ l, y l = 0 → x l < eps := by
  classical
  let sys := region cuts
  obtain ⟨rad,hr,hn⟩ := Metric.eventually_nhds_iff.mp (sys.nearby_vertices he)
  refine ⟨rad/2,half_pos hr,fun tol ht x hx hp => ?_⟩
  let rhs : Fin V ⊕ ↥cuts → ℝ := Sum.elim (fun l => if x l ≤ tol then x l else 0) (fun _ => 1)
  have close : dist rhs sys.rhs < rad := by
    apply (dist_pi_lt_iff hr).mpr
    rintro (l | c)
    · change dist (if x l ≤ tol then x l else 0) 0 < rad
      split
      · rw [Real.dist_eq,sub_zero,abs_of_nonneg ((mem_region.mp hx).1 l)]
        linarith
      · simpa
    · change dist (1 : ℝ) 1 < rad
      simpa
  let raised := sys.assign rhs
  have feas : x ∈ raised.body := by
    rintro (l | c)
    · change (if x l ≤ tol then x l else 0) ≤ x l
      split
      · rfl
      · exact hx (.inl l)
    · exact hx (.inr c)
  have small : ∀ l, x l ≤ tol → Sum.inl l ∈ raised.active x := by
    intro l hl
    change x l = if x l ≤ tol then x l else 0
    simp [hl]
  have vert : x ∈ raised.body.extremePoints ℝ := by
    apply (System.vertex_iff feas).mpr
    apply le_bot_iff.mp
    intro dir hd
    have hh := (raised.mem_directions).mp hd
    exact hp dir (fun l hl => hh _ (small l hl)) (fun c hc he => hh (.inr ⟨c,hc⟩) he)
  obtain ⟨y,hy,ha,hd⟩ := hn close x vert
  refine ⟨y,hy,fun l hl => ha (small l hl),fun l hl => ?_⟩
  have hh := (dist_pi_lt_iff he).mp hd l
  simpa [Real.dist_eq,hl,abs_of_nonneg ((mem_region.mp hx).1 l)] using hh

end Layer
end OAI.Geometry.Hirsch
