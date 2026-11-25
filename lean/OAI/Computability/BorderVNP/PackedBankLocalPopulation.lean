import OAI.Computability.BorderVNP.PackedBankFreshScalarBound
import OAI.Computability.BorderVNP.ShortenDenseMeasurements
import OAI.Computability.BorderVNP.ShortenEpochQuotientRecords

/-! # Local old-bin populations from the true output tile capacities

Each assigned old cable is counted at its source. The sewn layout retains
the full width there, distributed over the actual bands and hooks. The
measured old midpoint places every such source in a bounded neighborhood
of the bin's tile. This also bounds the old ordinal of an empty hook row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.SeedIntervals Shortening.CombiningStep Epoch InheritedBank
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
local notation3 "G" => (output e p bin perm positive first q).layout

/-- Every bit of the original bin is present at one of its retained source
incidences in the chosen region, including loops and cables split across bands. -/
theorem population_le_sewn_region (prior payload : (G).Site → ℕ) (test : (G).Site → Prop) (a : S)
    (hsrc : ∀ z, bin z = some a → test (.inl (p.layout.src z))) :
    count p.layout bin a ≤ localRecords G true prior payload test := by
  classical
  let sourceMass (v : p.layout.Site) := ∑ z, if bin z = some a ∧ p.layout.src z = v then p.layout.width z else 0
  have partition : (∑ v, sourceMass v) = count p.layout bin a := by
    rw [count_eq_sum]
    unfold sourceMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : bin z = some a <;> simp [h]
  let charge (v : (G).Site) := localRecords G true prior payload (· = v)
  have hsource (v : p.layout.Site) : sourceMass v ≤ if test (.inl v) then charge (.inl v) else 0 := by
    by_cases ht : test (.inl v)
    · rw [ite_eq_left ht]
      have hinc : sourceMass v ≤ incidentWidth p.layout v := by
        unfold sourceMass incidentWidth
        rw [←Finset.sum_subtype (s := Finset.univ.filter (fun z : p.layout.Edge =>
          p.layout.src z = v ∨ p.layout.dst z = v)) (p := fun z => p.layout.src z = v ∨ p.layout.dst z = v)
          (fun z => by simp) p.layout.width, Finset.sum_filter]
        apply Finset.sum_le_sum
        intro z _
        split_ifs <;> simp_all
      apply hinc.trans ((output_incidentWidth_le e p bin perm positive first q v).trans _)
      have hi := payload_incoming_le G prior payload (.inl v) (· = .inl v) rfl
      exact ((Nat.le_add_right _ _).trans_eq (incoming_eq_widths G (.inl v)).symm).trans
        ((Nat.le_add_left _ _).trans hi)
    · rw [ite_eq_right ht]
      apply Nat.le_zero.mpr
      apply Finset.sum_eq_zero
      intro z _
      split
      · next hz => exact False.elim (ht (hz.2 ▸ hsrc z hz.1))
      · rfl
  let region := Finset.univ.filter test
  have repr : (fun z => id z ∈ region) = test := by funext z; simp [region]
  have hr := localRecords_near G true prior payload id region
  rw [repr] at hr
  calc count p.layout bin a = ∑ v, sourceMass v := partition.symm
       _ ≤ ∑ v, if test (.inl v) then charge (.inl v) else 0 := Finset.sum_le_sum (fun v _ => hsource v)
       _ ≤ ∑ z : (G).Site, if test z then charge z else 0 :=
         Finset.sum_le_sum_of_injOn (fun v : p.layout.Site => (Sum.inl v : (G).Site)) Sum.inl_injective.injOn
           (fun _ _ => Finset.mem_univ _) (fun _ _ => le_rfl) (fun _ _ _ => Nat.zero_le _)
       _ = ∑ z ∈ region, localRecords G true prior payload (fun w => id w = z) := by simp only [region,Finset.sum_filter,charge,id_eq]
       _ = localRecords G true prior payload test := hr.symm

end Packing.Inherited

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Shortening Shortening.CombiningStep Shortening.SeedIntervals Shortening.StaticRows
  Epoch Packing Packing.Inherited Packing.InheritedProfile
open private nearby_tiles from OAI.Computability.BorderVNP.ShortenEpochQuotientRecords
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {I B : Type} [Fintype I] [Fintype B]

/-- The neighbor count is fixed before all depths and all measured stages.
The conclusion bounds the original, pre-clipping bin population by the
*output* tile's physical expanded cap. -/
theorem measured_population_cap (h : ℝ) : ∃ V : ℕ, ∀ {k d d' : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (hk : 0 < k) (child : Fin k → PlacedPack D P bits K I d) (s : Stage m B d' child)
    {ν u v : ℝ} (_measure : s.Measurements hk h ν u v) (q : s.Index e)
    (prior payload : s.input.layout.Site → ℕ) (M : ℕ),
    BirthTileCap e s.input s.label s.perm s.orient (0,false) q
      (fun z => productTileName d' ((s.result e q).site z)) prior payload M →
    ∀ a, count s.input.layout s.label a ≤ V*M := by
  obtain ⟨V,hV⟩ := nearby_tiles (I := I) (ρ := h)
  refine ⟨V,?_⟩
  intro k d d' P _ bits hk child s ν u v measure q prior payload M cap a
  obtain ⟨near,hcard,hnear⟩ := hV d'
  let G := (s.result e q).pack.layout
  let tile (z : G.Site) := productTileName d' ((s.result e q).site z)
  let old : G.Site → ℕ := Sum.elim prior (fun _ => 0)
  let pay : G.Site → ℕ := Sum.elim payload (fun z => bankUses e (blocks s.input.layout s.label s.perm m z.1) (q z.1).val z.2)
  have sources (c : s.input.layout.Edge) (hc : s.label c = some a) : tile (.inl (s.input.layout.src c)) ∈ near a.1 := by
    obtain ⟨_,ht,hd⟩ := measure.midpoint c a hc
    have hlen := s.placed.bin_length c a hc
    have fit := (measure.fits.1 a).2
    have close : dist (s.placed.old (s.input.layout.src c)) (measure.oldMid c) ≤ h := by
      rw [dist_comm]
      linarith only [hd,hlen,fit]
    exact ht ▸ hnear _ _ close
  have hr := population_le_sewn_region e s.input s.label s.perm s.orient (0,false) q old pay (fun z => tile z ∈ near a.1) a sources
  apply (hr.trans_eq (localRecords_near G true old pay tile (near a.1))).trans
  have bound := Finset.sum_le_sum (s := near a.1) (fun t _ => cap t)
  exact bound.trans (by simpa using Nat.mul_le_mul_right M (hcard a.1))

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
