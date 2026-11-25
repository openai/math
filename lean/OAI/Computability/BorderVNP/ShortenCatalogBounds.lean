import OAI.Computability.BorderVNP.ShortenProfileCatalog

/-!
# Uniform charged-wire types in the next round

Finite chart templates bound every inserted interior wire. A hook uses its
own old endpoint lift, so its length is bounded by the bin tolerance plus a
template distance. Retained charged wires keep their old length bound.
Consequently the finite catalog of relative segments contains every positive
charged output and has a positive minimum length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Epoch Cover Catalog Set
open scoped Classical

namespace AddressPartition

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits} {A : Type} [Fintype A]
variable {Q : Type*} [PseudoMetricSpace Q]

/-- Every charged wire in the sewn pack is a retained wire, a named hook,
or one of the profile's internal cables. Bounds on these three classes suffice. -/
theorem edge_bound (t : AddressPartition N A)
    (G : ∀ a, Network D (N.CutPorts (t.part a)) (N.cutWidths (t.part a)))
    (old : N.Site → Q) (sites : ∀ a, (G a).Site → Q) (charged : N.Edge → Bool) {L : ℝ}
    (hret : ∀ c, charged c = true → dist (old (N.src c)) (old (N.dst c)) ≤ L)
    (hhook : ∀ a k, dist (oldEndpoint N (t.part a) old k) (sites a ((G a).attach k)) ≤ L)
    (hint : ∀ a c, dist (sites a ((G a).src c)) (sites a ((G a).dst c)) ≤ L) :
    let out := (N.cut t.selected).sew (t.parallel G)
    let z : out.Site → Q := Sum.elim old (t.parallelSites G sites)
    ∀ c : out.Edge, profileCharges N t.selected (t.parallel G) charged c = true →
      dist (z (out.src c)) (z (out.dst c)) ≤ L := by
  intro out z c hc
  rcases c with k | c | ⟨a,c⟩
  · obtain ⟨⟨a,u⟩,rfl⟩ := t.portIndex.surjective k
    change dist (oldEndpoint N t.selected old (t.includePort a u))
      (t.parallelSites G sites ((t.parallel G).attach (t.includePort a u))) ≤ L
    rw [t.attach_include]
    cases u with
    | inl e => exact hhook a (.inl e)
    | inr e => exact hhook a (.inr e)
  · exact hret c.val hc
  · exact hint a c

end AddressPartition

namespace Catalog

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {I : Type*} [Fintype I]

/-- The finite catalog's radii are the actual half-lengths of its wires. -/
theorem SegmentType.distance_ends (v : SegmentType I) : dist v.ends.1 v.ends.2 = 2*v.radius := by
  unfold SegmentType.ends
  rw [(shiftTo_isometry v.center).dist_eq, dist_productLine, v.unit, mul_one]
  rw [show -v.radius-v.radius = -(2*v.radius) by ring,abs_neg,abs_of_nonneg (by linarith [v.positive])]

/-- A finite positive segment catalog gives a positive minimum for the next
step's bins, including the case in which there are no charged segments. -/
theorem minimum_length {V : Set (SegmentType I)} (hv : V.Finite) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ d (x y : SurfaceHost I (d+1)) v, v ∈ V → Realizes x y v.ends → μ ≤ dist x y := by
  let s := insert (1 : ℝ) (hv.toFinset.image fun v => 2*v.radius)
  have hn : s.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hn,?_,?_⟩
  · have h := Finset.min'_mem s hn
    rcases Finset.mem_insert.mp h with h | h
    · rw [h]; norm_num
    · obtain ⟨v,_,h⟩ := Finset.mem_image.mp h
      rw [← h]; linarith only [v.positive]
  · intro d x y v h hxy
    obtain ⟨_,_,_,hd⟩ := hxy
    rw [← hd,v.distance_ends]
    exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (hv.mem_toFinset.mpr h)))

/-- Actual output widths do not affect the uniform geometric length bound.
Old endpoints may live in any quotient admitting the indicated local lifts. -/
theorem uniform_wire_length (e : PaidIdentity K D m) (pat : Pattern I D) (L δ : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ {Q : Type*} [PseudoMetricSpace Q] {P : Type*} {bits : P → ℕ}
      {A : Type} [Fintype A] (p : Pack D P bits K) (bin : p.layout.Edge → Option A)
      (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
      (g : CombiningStep.Placement (m := m) p bin perm I Q) (q : CombiningStep.Counts e p bin perm)
      (code : A → Fin pat.bins), (∀ a, g.chart a = pat.chart (code a)) →
      (∀ c, (bin c).isSome = true → dist (g.old (p.layout.src c)) (g.old (p.layout.dst c)) ≤ L) →
      (∀ a u, dist (g.lift a u) ((g.chart a).atTerminal ((SeedIntervals.bundle p.layout bin perm m positive a).terminal u)) ≤ δ) →
      ∀ c, CombiningStep.postMask p bin perm e positive q c = true →
        let N := CombiningStep.physical p bin perm e positive q
        let z := g.postSites p bin perm e positive q
        dist (z (N.src c)) (z (N.dst c)) ≤ R := by
  let inner := fun u : Fin pat.bins × BankSite e => (pat.chart u.1).atSite (bankPosition e u.2)
  let term := fun u : Fin pat.bins × (Fin D × Bool) => (pat.chart u.1).atTerminal u.2
  let window := (range inner) ∪ (range term)
  have hw : window.Finite := (finite_range inner).union (finite_range term)
  obtain ⟨C,hC⟩ := ((hw.prod hw).image (fun z => dist z.1 z.2)).bddAbove
  have bound {x y} (hx : x ∈ window) (hy : y ∈ window) : dist x y ≤ C := hC ⟨(x,y),⟨hx,hy⟩,rfl⟩
  let R := max (max 0 L) (max C (δ+C))
  have hR : 0 ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨R,hR,?_⟩
  intro Q _ P bits A _ p bin perm positive g q code hcharts hret hnear
  let t := SeedIntervals.partition p.layout bin perm m
  let b := SeedIntervals.bundle p.layout bin perm m positive
  let j := SeedIntervals.blocks p.layout bin perm m
  let G := seedNetwork e j (p := CombiningStep.pieces (m := m) p bin perm) t b q
  let up := fun a v => (g.chart a).atSite ((G a).position v)
  let down := fun a v => g.project a (up a v)
  have hin (a : A) (v : (G a).Site) : up a v ∈ window := by
    left
    exact ⟨(code a,(v : BankSite e)),congrArg₂ SeedChart.atSite (hcharts a).symm
      (profile_position e (j a) (q a).val v).symm⟩
  apply t.edge_bound G g.old down (fun c => (bin c.1).isSome)
  · intro c hc
    exact (hret _ hc).trans ((le_max_right _ _).trans (le_max_left _ _))
  · intro a k
    rw [← g.projects a k]
    refine (g.nonexpanding a _ _).trans ?_
    let mid := (g.chart a).atTerminal ((b a).terminal k)
    have hmid : mid ∈ window := Or.inr ⟨(code a,(b a).terminal k),
      congrArg (fun c : SeedChart I D => c.atTerminal ((b a).terminal k)) (hcharts a).symm⟩
    have hdist := dist_triangle (g.lift a k) mid (up a ((G a).attach k))
    exact (hdist.trans (add_le_add (hnear _ _) (bound hmid (hin _ _)))).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  · intro a c
    exact (g.nonexpanding a _ _).trans ((bound (hin a ((G a).src c)) (hin a ((G a).dst c))).trans
      ((le_max_left _ _).trans (le_max_right _ _)))

end Catalog
end Shortening

end BorderVNP
end Computability
end OAI
