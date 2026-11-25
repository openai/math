import OAI.Computability.BorderVNP.CrossingIdentity
import OAI.Computability.BorderVNP.CrossingProfileValue

/-!
# The shortening rule at every multiplicity

The single finite identity in Lemma 3.3 generates every profile required in
Definition 3.1. All histograms share the same positive saving fraction. The
underlying site and cable sets are independent of the number of copies.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.PaidIdentity

open scoped BigOperators
variable {D m : ℕ} {K : Type*} [Field K]

private theorem terminal_ball (port : Fin D × Bool) : ‖antipodalPosition port‖ ≤ 1 := by
  rcases port with ⟨i,b⟩
  cases b <;> simp [antipodalPosition]

/-- The concrete profile wiring rule of a paid identity. The topology has
one selector spoke per physical terminal, independent of the multiplicity. -/
noncomputable def profile (e : PaidIdentity K D m) (j : ℕ) (p : Fin e.count → ℕ) :
    Network D (Fin D × Bool) (fun _ => j * m) :=
  Profile.network e.net antipodalPosition terminal_ball j p

/-- Local selector, routing, and original one-copy tables of the profile. -/
noncomputable def profileTables (e : PaidIdentity K D m) (j : ℕ) (p : Fin e.count → ℕ)
    (first : Fin D × Bool) : (e.profile j p).Tables K :=
  Profile.tables e.net antipodalPosition terminal_ball j p first e.table

/-- Every profile is a network on the same physical antipodal terminals. -/
theorem profile_placedAt (e : PaidIdentity K D m) (j : ℕ) (p : Fin e.count → ℕ) :
    (e.profile j p).PlacedAt antipodalPosition := Profile.network_placedAt e.net antipodalPosition terminal_ball j p

/-- Only the widths vary across histograms and multiplicities. -/
theorem profile_shape (e : PaidIdentity K D m) (j : ℕ) (p : Fin e.count → ℕ) :
    (e.profile j p).Site = (Unit ⊕ (Fin D × Bool) ⊕ Σ a, (e.net a).Site) ∧
    (e.profile j p).Edge = ((Fin D × Bool) ⊕ (Fin e.count × (Fin D × Bool)) ⊕ Σ a, (e.net a).Edge) :=
  ⟨rfl, rfl⟩

/-- Each profile realizes the sum over all ordered words with that histogram. -/
theorem profile_value (e : PaidIdentity K D m) (j : ℕ) (p : Fin e.count → ℕ)
    (first : Fin D × Bool) (x : Ports (fun _ : Fin D × Bool => j*m)) :
    (e.profile j p).value (e.profileTables j p first) x =
      ∑ word : Fin j → Fin e.count with Profile.histogram word = p,
        ∏ i, (e.net (word i)).value (e.table (word i)) (Profile.externalBlock x i) :=
  Profile.network_value e.net antipodalPosition terminal_ball p first e.table x

/-- Summing the profile contractions gives exactly the widened antipodal tensor. -/
theorem profile_sum (e : PaidIdentity K D m) (j : ℕ) (first : Fin D × Bool)
    (x : Ports (fun _ : Fin D × Bool => j*m)) :
    (∑ p ∈ Finset.univ.image (@Profile.histogram e.count j),
      (e.profile j p).value (e.profileTables j p first) x) = antipodalTensor K D (j*m) x := by
  classical
  simp_rw [e.profile_value]
  rw [Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi)]
  rw [antipodalTensor_bundle]
  simp_rw [e.identity, Fintype.prod_sum]
  rfl

/-- Definition 3.1's strict saving fraction is fixed before selecting either the
number of copies or a histogram. All selector and feeder cables are counted. -/
theorem profile_uniform_saving (e : PaidIdentity K D m) (hD : 0 < D) (hm : 0 < m) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ j (p : Fin e.count → ℕ), (∑ a, p a) = j →
      (e.profile j p).cost ≤ (1-ν) * (2*D*m*j) := by
  have hd : 0 < 2*(D:ℝ)*m := by positivity
  let ν := 1 - (e.cap + 2*D*(Nat.clog 2 e.count : ℝ)) / (2*D*m)
  refine ⟨ν, sub_pos.mpr ((div_lt_one hd).mpr e.strict), ?_⟩
  intro j p hp
  have h := Profile.network_cost_le e.net antipodalPosition terminal_ball e.placed j p hp e.cap e.cost_le
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat] at h
  calc
    _ ≤ j * (e.cap + (D:ℝ) * 2 * Nat.clog 2 e.count) := h
    _ = _ := by dsimp [ν]; field_simp; ring

end Crossing.PaidIdentity

end BorderVNP
end Computability
end OAI
