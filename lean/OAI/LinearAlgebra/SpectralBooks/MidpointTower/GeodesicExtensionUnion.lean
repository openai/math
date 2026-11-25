import OAI.LinearAlgebra.SpectralBooks.GeodesicExtensionTower
import OAI.LinearAlgebra.SpectralBooks.SpectralMetricLimit

/-! # The increasing union of finite spectral extensions

Each stage embeds into a single pointed ultralimit by following the site
through all later stages. The union of these images is closed under taking
midpoints and inherits every tensor price from the ultralimit.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace MidpointTower

open Filter Topology HyperbolicObstruction MetricLimit SiteTensor

variable {K : Type*} [Field K] (T : MidpointTower K)

private def push {n m : ℕ} (h : n ≤ m) (x : (T.stage n).carrier) : (T.stage m).carrier :=
  Nat.leRecOn (C := fun i ↦ (T.stage i).carrier) h (fun {i} ↦ (T.step i).map) x

private theorem push_trans {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (x : (T.stage n).carrier) :
    T.push (h.trans h') x = T.push h' (T.push h x) :=
  Nat.leRecOn_trans (C := fun i ↦ (T.stage i).carrier) h h' x

private def pushEmbedding {n m : ℕ} (h : n ≤ m) :
    PriceEmbedding (T.stage n).prices (T.stage m).prices where
  map := T.push h
  isometry := by
    induction m, h using Nat.le_induction with
    | base =>
      apply Isometry.of_dist_eq
      intro x y
      simp only [push, Nat.leRecOn_self]
    | succ m h ih =>
      apply Isometry.of_dist_eq
      intro x y
      simpa only [push, Nat.leRecOn_succ h, (T.step m).isometry.dist_eq] using ih.dist_eq x y
  price := by
    intro I _ R p
    induction m, h using Nat.le_induction with
    | base => simp [push, Function.comp_def, Nat.leRecOn_self]
    | succ m h ih =>
      rw [← ih, ← (T.step m).price R (T.push h ∘ p)]
      simp only [push, Function.comp_def, Nat.leRecOn_succ h]

variable (o : (T.stage 0).carrier)

private abbrev basepoint (n : ℕ) := T.push (Nat.zero_le n) o

private abbrev tailU := Ultrafilter.of (atTop : Filter ℕ)

private def sectionAt (n : ℕ) (x : (T.stage n).carrier) :
    Bounded tailU (fun i ↦ (T.stage i).carrier) (T.basepoint o) where
  val k := if h : n ≤ k then T.push h x else T.basepoint o k
  bound := by
    refine ⟨dist (T.basepoint o n) x, fun k ↦ ?_⟩
    split_ifs with h
    · change dist (T.push (Nat.zero_le k) o) _ ≤ _
      rw [T.push_trans (Nat.zero_le n) h]
      exact ((T.pushEmbedding h).isometry.dist_eq _ _).le
    · simp [dist_nonneg]

private abbrev ambient := Space (U := tailU) (X := fun i ↦ (T.stage i).carrier) (o := T.basepoint o)

private abbrev prices : SpectralPlacementPrices K (T.ambient o) :=
  SpectralPlacementPrices.metricLimit tailU (fun n ↦ (T.stage n).prices)

private def embed (n : ℕ) : PriceEmbedding (T.stage n).prices (T.prices o) where
  map x := point (T.sectionAt o n x)
  isometry := by
    apply Isometry.of_dist_eq
    intro x y
    apply tendsto_nhds_unique (tendsto_point_dist (T.sectionAt o n x) (T.sectionAt o n y))
    apply tendsto_const_nhds.congr'
    filter_upwards [Ultrafilter.of_le (atTop : Filter ℕ) (eventually_ge_atTop n)] with k hk
    simpa only [sectionAt, dite_eq_left hk, pushEmbedding] using ((T.pushEmbedding hk).isometry.dist_eq x y).symm
  price := by
    intro I _ R p
    apply tendsto_nhds_unique (SpectralPlacementPrices.metricLimit_price_tendsto tailU
      (fun k ↦ (T.stage k).prices) R (T.sectionAt o n ∘ p))
    apply tendsto_const_nhds.congr'
    filter_upwards [Ultrafilter.of_le (atTop : Filter ℕ) (eventually_ge_atTop n)] with k hk
    exact (by simpa only [Function.comp_def, sectionAt, dite_eq_left hk, pushEmbedding] using
      ((T.pushEmbedding hk).price R p).symm)

private theorem embed_push {n m : ℕ} (h : n ≤ m) (x : (T.stage n).carrier) :
    (T.embed o m).map (T.push h x) = (T.embed o n).map x := by
  apply dist_eq_zero.mp
  apply tendsto_nhds_unique (tendsto_point_dist (T.sectionAt o m (T.push h x)) (T.sectionAt o n x))
  apply tendsto_const_nhds.congr'
  filter_upwards [Ultrafilter.of_le (atTop : Filter ℕ) (eventually_ge_atTop m)] with k hk
  simp only [sectionAt, dite_eq_left hk, dite_eq_left (h.trans hk), T.push_trans h hk, dist_self]

/-- The union of the finite stages is a metric spectral space with exact
midpoints, preserving the placement prices of the first stage. -/
theorem exists_midpoint_union (o : (T.stage 0).carrier) :
    ∃ (X : Type) (_ : MetricSpace X) (P : SpectralPlacementPrices K X),
      Nonempty (PriceEmbedding (T.stage 0).prices P) ∧
      ∀ a b : X, ∃ m, IsWireMidpoint a b m := by
  classical
  let S : Set (T.ambient o) := ⋃ n, Set.range (T.embed o n).map
  let ι (n : ℕ) (x : (T.stage n).carrier) : S :=
    ⟨(T.embed o n).map x, Set.mem_iUnion.mpr ⟨n, x, rfl⟩⟩
  let P := (T.prices o).pullback (Subtype.val : S → _) isometry_subtype_coe
  let f : PriceEmbedding (T.stage 0).prices P := {
    map := ι 0
    isometry := (T.embed o 0).isometry
    price := (T.embed o 0).price }
  refine ⟨S, inferInstance, P, ⟨f⟩, ?_⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, y, rfl⟩ := Set.mem_iUnion.mp hb
  let k := max i j
  let u := T.push (le_max_left i j) x
  let v := T.push (le_max_right i j) y
  obtain ⟨m, hm⟩ := T.midpoint k u v
  refine ⟨ι (k+1) m, ?_⟩
  change IsWireMidpoint ((T.embed o i).map x) ((T.embed o j).map y) ((T.embed o (k+1)).map m)
  have eqstep (w : (T.stage k).carrier) :
      (T.embed o (k+1)).map ((T.step k).map w) = (T.embed o k).map w := by
    simpa only [push, Nat.leRecOn_succ'] using T.embed_push o (Nat.le_succ k) w
  have h := hm.map (T.embed o (k+1)).isometry
  rw [eqstep, eqstep] at h
  dsimp only [u, v, k] at h
  rwa [T.embed_push, T.embed_push] at h

end MidpointTower

end

end SpectralBooks
end LinearAlgebra
end OAI
