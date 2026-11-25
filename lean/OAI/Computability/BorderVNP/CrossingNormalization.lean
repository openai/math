import OAI.Computability.BorderVNP.CrossingProfiles
import OAI.Computability.BorderVNP.CrossingProfileSize

/-!
# Normalizing the existence of a shortening

Definition 3.1 provides one finite exact identity, a uniform positive saving and
one placed network for every ordered histogram sum. Even if the latter networks
are arbitrary, their number at multiplicity `j` is polynomial in `j`. One sufficiently
large `j` pays for a fresh selector on every terminal. At the new width, the explicit
profile construction realizes the additional fixed-configuration and wiring
requirements of Definition 3.1. In particular, testing existence by a paid identity
is exact in both branches of the dichotomy in §§14–15.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open Filter

variable {K : Type*} [Field K] {D m : ℕ}

/-- The finite one-copy identity and all of its uniformly shorter histogram contractions.
The witnesses here can choose any placed realization of each histogram. The normalization
theorem produces witnesses using the explicit fixed wiring in `PaidIdentity.profile`. -/
structure ProfileShortening (K : Type*) [Field K] (D m : ℕ) where
  /-- Number of terms of the starting identity. -/
  count : ℕ
  /-- One-copy summands. -/
  term : Fin count → Network D (Fin D × Bool) (fun _ => m)
  /-- Field entries at the sites of a one-copy summand. -/
  table : ∀ a, (term a).Tables K
  placed : ∀ a, (term a).PlacedAt antipodalPosition
  identity : ∀ x, antipodalTensor K D m x = ∑ a, (term a).value (table a) x
  /-- Uniform fractional saving. -/
  saving : ℝ
  saving_pos : 0 < saving
  /-- Realization of each attainable histogram on the original terminal positions. -/
  realization : ∀ j, 0 < j → ∀ p ∈ Profile.profiles count j,
    ∃ N : Network D (Fin D × Bool) (fun _ => j*m), ∃ T : N.Tables K,
      N.PlacedAt antipodalPosition ∧ N.cost ≤ (1-saving) * (2*D*m*j) ∧
      ∀ x, N.value T x = ∑ w : Fin j → Fin count with Profile.histogram w = p,
        ∏ i, (term (w i)).value (table (w i)) (Profile.externalBlock x i)

/-- The existential shortening condition, including the positive width and the lower
bound of two on the number of directions. -/
def HasProfileShortening (K : Type*) [Field K] : Prop :=
  ∃ D ≥ 2, ∃ m > 0, Nonempty (ProfileShortening K D m)

/-- The canonical histogram construction gives all the witnesses of Definition 3.1. -/
theorem PaidIdentity.profileShortening (e : PaidIdentity K D m) (hD : 0 < D) (hm : 0 < m) :
    Nonempty (ProfileShortening K D m) := by
  obtain ⟨ν, hν, hcost⟩ := e.profile_uniform_saving hD hm
  let first : Fin D × Bool := (⟨0,hD⟩,false)
  refine ⟨⟨e.count, e.net, e.table, e.placed, e.identity, ν, hν, ?_⟩⟩
  intro j _ p hp
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hp
  have hs : ∑ a, Profile.histogram w a = j := by
    simpa using (Profile.cableWidth w rfl (fun _ => 1)).symm
  exact ⟨e.profile j _, e.profileTables j _ first, e.profile_placedAt j _, hcost j _ hs,
    e.profile_value j _ first⟩

/-- A polynomial number of exact terms with the stated per-copy saving produces a
paid identity at a positive multiple of the width. This uses the rounded binary
selector cost even for terms realized by unrelated configurations. -/
theorem paidIdentity_of_polynomial_sums {A : ℕ} {ν : ℝ} (hD : 0 < D) (hm : 0 < m) (hν : 0 < ν)
    (powers : ∀ j > 0, ∃ B ≤ (j+1)^A,
      ∃ N : Fin B → Network D (Fin D × Bool) (fun _ => j*m), ∃ T : ∀ a, (N a).Tables K,
      (∀ a, (N a).PlacedAt antipodalPosition) ∧
      (∀ a, (N a).cost ≤ (1-ν)*(2*D*m*j)) ∧
      ∀ x, antipodalTensor K D (j*m) x = ∑ a, (N a).value (T a) x) :
    ∃ j > 0, Nonempty (PaidIdentity K D (j*m)) := by
  let w : ℝ := (1-ν)*(2*D*m)
  have hsave : w + 2*D*Real.logb 2 1 < 2*D*m := by
    have hpos : 0 < 2 * (D : ℝ) * m := by positivity
    simp only [Real.logb_one, mul_zero, add_zero, w]
    nlinarith only [mul_pos hν hpos]
  obtain ⟨j,hj,hsel⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (eventually_selector_strict_saving D m 1 A w (by decide) (by simpa using hsave))).exists
  obtain ⟨B,hB,N,T,hp,hc,he⟩ := powers j hj
  refine ⟨j,hj,⟨⟨B,N,T,hp,he,j*w,?_,?_⟩⟩⟩
  · intro a
    exact (hc a).trans_eq (by dsimp [w]; ring)
  · have h := hsel B (by simpa only [one_pow, mul_one] using hB)
    push_cast
    linarith only [h]

/-- The ordered histogram identities sum to a polynomial-size exact network sum.
Reindexing these profiles by a finite ordinal introduces no extra summands. -/
theorem ProfileShortening.paidAtMultiple (s : ProfileShortening K D m) (hD : 0 < D) (hm : 0 < m) :
    ∃ j > 0, Nonempty (PaidIdentity K D (j*m)) := by
  classical
  apply paidIdentity_of_polynomial_sums (A := s.count) hD hm s.saving_pos
  intro j hj
  let P := Profile.profiles s.count j
  choose N T hp hc hv using fun p : ↥P => s.realization j hj p.val p.property
  let e := (Fintype.equivFin ↥P).symm
  refine ⟨Fintype.card ↥P, ?_, N ∘ e, fun i => T (e i), fun i => hp (e i), fun i => hc (e i), ?_⟩
  · simpa only [P, Fintype.card_coe] using Profile.profile_count s.count j
  · intro x
    change antipodalTensor K D (j*m) x = ∑ i, (N (e i)).value (T (e i)) x
    rw [e.sum_comp (fun p => (N p).value (T p) x)]
    simp_rw [hv]
    rw [Finset.sum_coe_sort P (fun p => ∑ w : Fin j → Fin s.count with Profile.histogram w = p,
      ∏ i, (s.term (w i)).value (s.table (w i)) (Profile.externalBlock x i))]
    change _ = ∑ p ∈ Finset.univ.image (@Profile.histogram s.count j),
      ∑ w : Fin j → Fin s.count with Profile.histogram w = p,
        ∏ i, (s.term (w i)).value (s.table (w i)) (Profile.externalBlock x i)
    rw [Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi),
      antipodalTensor_bundle]
    simp_rw [s.identity, Fintype.prod_sum]
    rfl

/-- Existence is unchanged on replacing an arbitrary histogram shortening by a paid
identity and its canonical fixed wiring, with a possible positive rescaling of width. -/
theorem hasProfileShortening_iff_paid (K : Type*) [Field K] :
    HasProfileShortening K ↔ ∃ D ≥ 2, ∃ m > 0, Nonempty (PaidIdentity K D m) := by
  constructor
  · rintro ⟨D,hD,m,hm,⟨s⟩⟩
    obtain ⟨j,hj,h⟩ := s.paidAtMultiple (by omega) hm
    exact ⟨D,hD,j*m,Nat.mul_pos hj hm,h⟩
  · rintro ⟨D,hD,m,hm,⟨e⟩⟩
    exact ⟨D,hD,m,hm,e.profileShortening (by omega) hm⟩

end Crossing

end BorderVNP
end Computability
end OAI
