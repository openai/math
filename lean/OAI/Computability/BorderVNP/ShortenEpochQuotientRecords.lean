import OAI.Computability.BorderVNP.ShortenEpochPhysicalMidpoints
import OAI.Computability.BorderVNP.ShortenEpochRecordCap

/-! # Uniform tile caps for the quotient-sewn physical layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.CombiningStep

open Crossing Cover Epoch Finset SeedIntervals
open scoped Classical

variable {D m d : ℕ} [NeZero D] {I B : Type} [Fintype I] [Fintype B]
    {K : Type*} [Field K] {P : Type*} {bits : P → ℕ}

variable (p : Pack D P bits K) (bin : p.layout.Edge → Option ((I → Deck (d+1)) × B))
    (perm : Fin D → Equiv.Perm ((I → Deck (d+1)) × B)) (e : PaidIdentity K D m) (positive : p.layout.Edge → Bool)
    (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1))) (q : Counts e p bin perm)

/-- Each old-side hook end and its new-side attachment lie within a uniform
distance. This estimate applies also to hooks of zero width. -/
theorem Placement.hook_attachment_distance {h ν : ℝ} (hν : 0 ≤ ν)
    (fits : g.fits p bin perm positive h ν) :
    let t := partition p.layout bin perm m
    let G := seedNetwork e _ (p := pieces (m := m) p bin perm) t (bundle p.layout bin perm m positive) q
    ∀ k, dist (g.old (oldHookSite (layout p.layout bin perm m) t.selected k))
      (g.postSites p bin perm e positive q (.inr ((t.parallel G).attach k))) ≤ 2*h + ν/4*h := by
  intro t G k
  obtain ⟨⟨a,u⟩,rfl⟩ := t.portIndex.surjective k
  let C := g.chart a
  let π := g.project a
  let v := (G a).attach u
  let x := (G a).position v
  let z := (bundle p.layout bin perm m positive a).terminal u
  have ho : g.old (oldHookSite (layout p.layout bin perm m) t.selected (t.includePort a u)) =
      π (g.lift a u) := by
    refine Eq.trans ?_ (g.projects a u).symm
    cases u <;> rfl
  have hn : g.postSites p bin perm e positive q (.inr ((t.parallel G).attach (t.includePort a u))) =
      π (C.atSite x) :=
    congrArg (fun s => g.postSites p bin perm e positive q (.inr s)) (t.attach_include G a u)
  rw [show t.portIndex ⟨a,u⟩ = t.includePort a u from rfl,ho,hn]
  apply (g.nonexpanding a _ _).trans
  have ht := dist_triangle (g.lift a u) (C.atTerminal z) C.center
  rw [Epoch.SeedChart.dist_atTerminal_center C (fits.1 a).1] at ht
  have hx := Epoch.SeedChart.dist_atSite_center C (fits.1 a).1 x ((G a).in_ball v)
  have hd := dist_triangle (g.lift a u) C.center (C.atSite x)
  rw [dist_comm C.center (C.atSite x)] at hd
  have hz := mul_le_mul_of_nonneg_left (fits.1 a).2 (show 0 ≤ ν/4 by positivity)
  linarith only [hd,ht,hx,fits.2 a u,(fits.1 a).2,hz]

private theorem nearby_tiles {ρ : ℝ} :
    ∃ V : ℕ, ∀ d, ∃ near : (I → Deck (d+1)) → Finset ((I → Deck (d+1))),
      (∀ t, (near t).card ≤ V) ∧ ∀ x y : SurfaceHost I (d+1), dist x y ≤ ρ →
      productTileName d x ∈ near (productTileName d y) := by
  obtain ⟨V,hV⟩ := quotient_seed_neighbors (I := I) (B := Unit) ρ
  refine ⟨V,?_⟩
  intro d
  obtain ⟨near,hin,_,hm⟩ := hV d
  refine ⟨fun t => (near t).image Prod.fst,fun t => card_image_le.trans (by simpa using hin t),?_⟩
  exact fun x y hd => mem_image_of_mem _ (hm x y hd ())

/-- One constant controls the physical descriptor and expanded-record counts
after the simultaneous replacements at every depth. Only the chart fit, the
actual input-midpoint addresses, and the donor seed center's tile are supplied.
All incidence and finite-neighborhood bounds are discharged geometrically. -/
theorem physical_quotient_record_cap (hm : 0 < m) (h ν : ℝ) (hh : 0 ≤ h) (hν : 0 ≤ ν) :
    ∃ C : ℕ, ∀ d, ∀ {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
        (bin : p.layout.Edge → Option ((I → Deck (d+1)) × B)) (perm : Fin D → Equiv.Perm ((I → Deck (d+1)) × B))
        (positive : p.layout.Edge → Bool) (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1))),
      g.fits p bin perm positive h ν →
      ∀ (oldMid : p.layout.Edge → SurfaceHost I (d+1)),
      (∀ c a, bin c = some a → a.1 = productTileName d (oldMid c) ∧
        dist (oldMid c) (g.old (p.layout.src c)) ≤ dist (g.old (p.layout.src c)) (g.old (p.layout.dst c))/2) →
      (∀ a, (perm 0 a).1 = productTileName d (g.project a (g.chart a).center)) →
      ∀ (q : Counts e p bin perm) (expanded : Bool) (prior payload : p.layout.Site → ℕ) (M : ℕ),
      (∀ o, localRecords p.layout expanded prior payload (fun v => productTileName d (g.old v) = o) ≤ M) →
      let t := partition p.layout bin perm m
      let b := bundle p.layout bin perm m positive
      let j := blocks p.layout bin perm m
      ∀ o, 1 + localRecords (physical p bin perm e positive q) expanded
        (sewnPrior e j (p := pieces (m := m) p bin perm) t b q prior)
        (sewnPayload e j (p := pieces (m := m) p bin perm) t b q payload)
        (fun v => productTileName d (g.postSites p bin perm e positive q v) = o) ≤ C * (1+M) := by
  classical
  let ρ := 2*h + ν/4*h
  have hr : h ≤ ρ := by dsimp [ρ]; nlinarith only [hh,mul_nonneg hν hh]
  obtain ⟨V,hV⟩ := nearby_tiles (I := I) (ρ := ρ)
  obtain ⟨L,hL⟩ := quotient_seed_neighbors (I := I) (B := B) ρ
  let S := L * Fintype.card B
  let U := 1 + V + S*V
  refine ⟨1+(3*Fintype.card (Band D)+profilePayloadBound e)*U+S*profileDescriptorBound e,?_⟩
  intro d P _ bits p bin perm positive g fits oldMid hmid hctr q expanded prior payload M hcap t b j o
  obtain ⟨neighbor,hcard,hmem⟩ := hV d
  obtain ⟨seeds,hseeds,_,hseedmem⟩ := hL d
  let near := (seeds o).map (perm 0).symm.toEmbedding
  let tiles := insert o (neighbor o ∪ (seeds o).biUnion (fun a => neighbor a.1))
  have hnear (a : (I → Deck (d+1)) × B) : a ∈ near ↔ perm 0 a ∈ seeds o := by simp [near]
  have htiles : tiles.card ≤ U := by
    have hbi := card_biUnion_le (s := seeds o) (t := fun a => neighbor a.1)
    have hs : (∑ a ∈ seeds o, (neighbor a.1).card) ≤ S*V :=
      (sum_le_sum (s := seeds o) fun a _ => hcard a.1).trans (by simpa using Nat.mul_le_mul_right V (hseeds o))
    have hi := card_insert_le o (neighbor o ∪ (seeds o).biUnion (fun a => neighbor a.1))
    have hu := card_union_le (neighbor o) ((seeds o).biUnion (fun a => neighbor a.1))
    have hn := hcard o
    dsimp only [tiles,U]
    omega
  have hncard : near.card ≤ S := (card_map _).le.trans (hseeds o)
  let tile := fun v => productTileName d (g.old v)
  let post := fun v => productTileName d (g.postSites p bin perm e positive q v) = o
  apply physical_records_le p bin perm e hm positive q expanded prior payload tile tiles near post
    M U S hcap htiles hncard
  · intro v hv
    exact (show tile v = o from hv) ▸ mem_insert_self _ _
  · intro k hk
    have he := hmem _ _ (g.hook_attachment_distance p bin perm e positive q hν fits k)
    change productTileName d _ = o at hk
    rw [hk] at he
    exact mem_insert_of_mem (mem_union_left _ he)
  · intro a v hv
    let G := seedNetwork e j (p := pieces (m := m) p bin perm) t b q
    let x := g.project a ((g.chart a).atSite ((G a).position v))
    have hd : dist x (g.project a (g.chart a).center) ≤ ρ :=
      (g.nonexpanding a _ _).trans ((Epoch.SeedChart.dist_atSite_center _ (fits.1 a).1 _ ((G a).in_ball v)).trans
        ((fits.1 a).2.trans hr))
    have he := hseedmem _ x ((dist_comm _ _).le.trans hd) (perm 0 a).2
    rw [←hctr,show productTileName d x = o from hv] at he
    exact (hnear a).mpr he
  · intro c a ha hc
    obtain ⟨ht,hd⟩ := hmid c (perm 0 a) hc
    have hlen := g.bin_length c (perm 0 a) hc
    have hb : dist (g.old (p.layout.src c)) (oldMid c) ≤ ρ := by
      rw [dist_comm]; linarith only [hd,hlen,(fits.1 (perm 0 a)).2,hr]
    have he := hmem _ _ hb
    rw [←ht] at he
    exact mem_insert_of_mem (mem_union_right _ (mem_biUnion.mpr ⟨_,(hnear a).mp ha,he⟩))

end Shortening.CombiningStep

end BorderVNP
end Computability
end OAI
