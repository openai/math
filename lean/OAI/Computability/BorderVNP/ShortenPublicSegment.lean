import OAI.Computability.BorderVNP.ShortenPreparedBins

/-!
# Reading an oriented segment from its two public endpoint records

A single congruence level distinguishes all integral endpoint displacements in
the finite catalog. The two normalized site tags and the quotient of the low
tile addresses therefore identify a jointly lifted, distance-realizing segment.
This permits the geometric labels to be recovered after cables have been split
and sewn, when the stored records give only ordered site identifiers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Epoch Catalog PreparedBins PackMotions
open scoped Classical

variable {I : Type*} [Fintype I]

/-- Integral name of the tile containing a lifted point. -/
noncomputable def origin (x : HyperbolicHost I) : I → gamma 1 := (toTile x)⁻¹

/-- The integral tile displacement of the destination relative to the source. -/
noncomputable def displacement (s : SegmentType I) : I → gamma 1 :=
  (origin s.ends.1)⁻¹ * origin s.ends.2

omit [Fintype I] in
private theorem translate_comp (a b : I → gamma 1) (x : HyperbolicHost I) :
    translatePoint a (translatePoint b x) = translatePoint (a*b) x := by
  ext1 i
  change gammaSL 1 (a i) • (gammaSL 1 (b i) • x i) = gammaSL 1 (a i * b i) • x i
  rw [map_mul,mul_smul]

omit [Fintype I] in
private theorem origin_normalize (x : HyperbolicHost I) : translatePoint (origin x) (normalize x) = x := by
  ext1 i
  change gammaSL 1 ((toTile x i)⁻¹) • (gammaSL 1 (toTile x i) • x i) = x i
  rw [map_inv,inv_smul_smul]

/-- A fixed low residue determines every integral displacement in any given finite
table, including simultaneous displacement in all product factors. -/
theorem exists_separating_level {T : Type*} [Finite T] (v : T → I → gamma 1) :
    ∃ k, ∀ t u, (∀ i, (v t i : Deck k) = (v u i : Deck k)) → v t = v u := by
  let matrix (z : (T × T) × I) : Mat := split ((v z.1.1 z.2)⁻¹ * v z.1.2 z.2).val.val
  obtain ⟨k,hk⟩ := eventually_identity_on_compact (Set.finite_range matrix).isCompact
  refine ⟨k,fun t u h => funext fun i => ?_⟩
  let w := (v t i)⁻¹ * v u i
  have hw : (w : Deck k) = 1 := by
    change (↑((v t i)⁻¹ * v u i) : Deck k) = 1
    rw [QuotientGroup.mk_mul,QuotientGroup.mk_inv,h i,inv_mul_cancel]
  have hmem : w ∈ (gamma k).subgroupOf (gamma 1) := (QuotientGroup.eq_one_iff w).mp hw
  have he := hk k le_rfl ⟨w.val,hmem⟩ (Set.mem_range_self (f := matrix) ((t,u),i))
  exact inv_mul_eq_one.mp (Subtype.ext he : w = 1)

/-- The fixed low-level table key of an oriented catalog segment. -/
noncomputable def key (k : ℕ) (s : SegmentType I) :
    HyperbolicHost I × HyperbolicHost I × (I → Deck k) :=
  (normalize s.ends.1,normalize s.ends.2,fun i => (displacement s i : Deck k))

/-- Key computed on the public records of a source and a destination site. -/
noncomputable def endpointKey {k d : ℕ} (hk : k ≤ d+1) (x y : SurfaceHost I (d+1)) :
    HyperbolicHost I × HyperbolicHost I × (I → Deck k) :=
  (relative d x,relative d y,fun i => deckReduction hk ((productAddress d x i)⁻¹ * productAddress d y i))

omit [Fintype I] in
private theorem reduced_origin (d : ℕ) (x : HyperbolicHost I) :
    productAddress d (productProjection (d+1) x) = reduceMove d (origin x) := rfl

/-- A real shortest segment has the key read from its endpoints, for every low window. -/
theorem key_of_realizes {k d : ℕ} (hk : k ≤ d+1) {x y : SurfaceHost I (d+1)}
    {s : SegmentType I} (h : Realizes x y s.ends) : key k s = endpointKey hk x y := by
  rcases h with ⟨a,rfl,rfl,_⟩
  apply Prod.ext
  · simp [key,endpointKey,relative_projection,normalize_translate]
  apply Prod.ext
  · simp [key,endpointKey,relative_projection,normalize_translate]
  funext i
  change (displacement s i : Deck k) = deckReduction hk (_⁻¹ * _)
  rw [productAddress_translate,productAddress_translate,reduced_origin,reduced_origin]
  simp only [Pi.mul_apply]
  rw [show ((reduceMove d a i * reduceMove d (origin s.ends.1) i)⁻¹ *
    (reduceMove d a i * reduceMove d (origin s.ends.2) i)) =
    (reduceMove d (origin s.ends.1) i)⁻¹ * reduceMove d (origin s.ends.2) i by group]
  change (↑((origin s.ends.1 i)⁻¹ * origin s.ends.2 i) : Deck k) =
    deckReduction hk ((↑(origin s.ends.1 i) : Deck (d+1))⁻¹ * ↑(origin s.ends.2 i))
  rw [map_mul,map_inv,QuotientGroup.mk_mul,QuotientGroup.mk_inv]
  rfl

/-- Segments with the same full normalized endpoint data differ only by one
integral translation. Their orientation and length agree. -/
private theorem congruent_ends {s t : SegmentType I}
    (hl : normalize s.ends.1 = normalize t.ends.1) (hr : normalize s.ends.2 = normalize t.ends.2)
    (hm : displacement s = displacement t) :
    let b := origin t.ends.1 * (origin s.ends.1)⁻¹
    translatePoint b s.ends.1 = t.ends.1 ∧ translatePoint b s.ends.2 = t.ends.2 := by
  let b := origin t.ends.1 * (origin s.ends.1)⁻¹
  change translatePoint b s.ends.1 = t.ends.1 ∧ translatePoint b s.ends.2 = t.ends.2
  have ends {x y : HyperbolicHost I} (hn : normalize x = normalize y)
      (ha : b * origin x = origin y) : translatePoint b x = y := by
    calc
      _ = translatePoint b (translatePoint (origin x) (normalize x)) := by rw [origin_normalize]
      _ = translatePoint (origin y) (normalize y) := by rw [translate_comp,ha,hn]
      _ = y := origin_normalize y
  refine ⟨ends hl (by simp [b,mul_assoc]),ends hr ?_⟩
  change origin t.ends.1 * (origin s.ends.1)⁻¹ * origin s.ends.2 = origin t.ends.2
  rw [mul_assoc,show (origin s.ends.1)⁻¹ * origin s.ends.2 = displacement t from hm]
  simp [displacement]

variable {D : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)

/-- Finite table entry at a normalized endpoint and low-displacement key. -/
noncomputable def lookup (k : ℕ) (u : HyperbolicHost (Cube D) × HyperbolicHost (Cube D) ×
    (Cube D → Deck k)) : Option B.types :=
  if hm : ∃ s : B.types, key k s.val = u then some hm.choose else none

private theorem lookup_correct_of_separates (k : ℕ)
    (hk : ∀ t u : B.types, (∀ i, (displacement t.val i : Deck k) = (displacement u.val i : Deck k)) →
      displacement t.val = displacement u.val) {d : ℕ} (hkd : k ≤ d+1) (x y : SurfaceHost (Cube D) (d+1))
    (hx : relative d x ∈ S) (hy : relative d y ∈ S) (hne : x ≠ y) (hlen : dist x y ≤ 2*h) :
    ∃ t : B.types, lookup B k (endpointKey hkd x y) = some t ∧ Realizes x y t.val.ends := by
  obtain ⟨v,hv,hr⟩ := B.represents d x y hx hy hne hlen
  let t : B.types := ⟨v,hv⟩
  have kt : key k t.val = endpointKey hkd x y := key_of_realizes hkd hr
  have found : ∃ s : B.types, key k s.val = endpointKey hkd x y := ⟨t,kt⟩
  let s := found.choose
  have eq : key k s.val = key k t.val := found.choose_spec.trans kt.symm
  have hm := hk s t fun i => congrFun (congrArg (fun z => z.2.2) eq) i
  obtain ⟨hl,hd⟩ := congruent_ends (congrArg Prod.fst eq) (congrArg (fun z => z.2.1) eq) hm
  let b := origin t.val.ends.1 * (origin s.val.ends.1)⁻¹
  obtain ⟨a,ha,he,hlen⟩ := hr
  refine ⟨s,by simp [lookup,found,s],a*b,?_,?_,?_⟩
  · rw [← translate_comp,hl]; exact ha
  · rw [← translate_comp,hd]; exact he
  · exact ((translatePoint_isometry b).dist_eq _ _).symm.trans (by rw [hl,hd]; exact hlen)

/-- The same distinguishing window recognizes coincident endpoints and recovers
joint lifts of all positive-length short cables. Identity is included as an extra
candidate in the finite separation argument, even for an empty segment catalog. -/
theorem exists_total_lookup_level :
    ∃ k, ∀ {d : ℕ} (hk : k ≤ d+1),
      (∀ x : SurfaceHost (Cube D) (d+1), lookup B k (endpointKey hk x x) = none) ∧
      ∀ x y : SurfaceHost (Cube D) (d+1), relative d x ∈ S → relative d y ∈ S →
        x ≠ y → dist x y ≤ 2*h → ∃ t : B.types,
        lookup B k (endpointKey hk x y) = some t ∧ Realizes x y t.val.ends := by
  let move : Option B.types → Cube D → gamma 1 := fun t => t.elim 1 fun u => displacement u.val
  obtain ⟨k,sep⟩ := exists_separating_level move
  refine ⟨k,fun {d} hk => ⟨?_,lookup_correct_of_separates B k (fun t u => sep (some t) (some u)) hk⟩⟩
  intro x
  have empty : ¬ ∃ s : B.types, key k s.val = endpointKey hk x x := by
    rintro ⟨s,he⟩
    have hn : normalize s.val.ends.1 = normalize s.val.ends.2 :=
      (congrArg Prod.fst he).trans (congrArg (fun z => z.2.1) he).symm
    have hd : displacement s.val = 1 := sep (some s) none fun i => by
      simpa [move,key,endpointKey] using congrFun (congrArg (fun z => z.2.2) he) i
    have hi : origin s.val.ends.1 = origin s.val.ends.2 := inv_mul_eq_one.mp hd
    have hab : s.val.ends.1 = s.val.ends.2 := by
      calc
        _ = translatePoint (origin s.val.ends.1) (normalize s.val.ends.1) := (origin_normalize _).symm
        _ = translatePoint (origin s.val.ends.2) (normalize s.val.ends.2) := by rw [hi,hn]
        _ = _ := origin_normalize _
    have hz := s.val.dist_ends
    rw [hab,dist_self] at hz
    linarith [s.val.positive]
  simp [lookup,empty]

/-- Reading just two endpoint records recovers an actual joint lift of every
active cable at every depth above the single finite distinguishing window. -/
theorem exists_lookup_level :
    ∃ k, ∀ {d : ℕ} (hk : k ≤ d+1) (x y : SurfaceHost (Cube D) (d+1)),
      relative d x ∈ S → relative d y ∈ S → x ≠ y → dist x y ≤ 2*h →
      ∃ t : B.types, lookup B k (endpointKey hk x y) = some t ∧ Realizes x y t.val.ends := by
  obtain ⟨k,hk⟩ := exists_total_lookup_level B
  exact ⟨k,fun h => (hk h).2⟩

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
