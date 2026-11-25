import OAI.Computability.BorderVNP.ShortenAddressPartition

/-!
# Exact combining step for all seed addresses

One public profile is a tuple of attained histograms, one per seed. The
combined profile network has one physical copy of the appropriate selector
wiring at each seed; its internal wire assignments remain private.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing
open scoped BigOperators Classical

variable {D m : ℕ} {P : Type*} {bits : P → ℕ} {K : Type*} [Field K]
variable {A : Type} [Fintype A] (e : PaidIdentity K D m) (j : A → ℕ)

/-- Public counts at each seed: the histogram must be attained by a word of
the matched block length, including the unique empty word at an empty match. -/
abbrev ProfileCounts := ∀ a : A, ↥(Finset.univ.image (@Profile.histogram e.count (j a)))

omit [Fintype A] in
/-- Counts in an attained histogram sum to the number of matched blocks. -/
theorem profileCounts_total (q : ProfileCounts e j) (a : A) :
    ∑ u, (q a).val u = j a := by
  obtain ⟨word, _, hw⟩ := Finset.mem_image.mp (q a).property
  rw [← hw]
  simpa using (Profile.cableWidth word rfl (fun _ => 1)).symm

variable {p : Pack D P bits K} (t : AddressPartition p.layout A)
variable (b : ∀ a, Bundle p.layout (t.part a) (j a * m))

/-- Concrete local histogram network on the slots exposed by this seed. -/
noncomputable def seedNetwork (q : ProfileCounts e j) (a : A) :=
  (b a).expose (e.profile (j a) (q a).val)

/-- Local tables that enforce the histogram and the order of the selected old slots. -/
noncomputable def seedTables (first : Fin D × Bool) (q : ProfileCounts e j) (a : A) :
    (seedNetwork e j t b q a).Tables K :=
  (b a).exposeTables _ (e.profileTables (j a) (q a).val first)

/-- Product of all physical seed networks realizes the joint wire equality
when summed over all public profile tuples. -/
theorem sum_seedNetworks (first : Fin D × Bool) (s : Ports (p.layout.cutWidths t.selected)) :
    p.layout.cutEquality t.selected s = ∑ q : ProfileCounts e j,
      (t.parallel (seedNetwork e j t b q)).value
        (t.parallelTables (seedNetwork e j t b q) (seedTables e j t b first q)) s := by
  rw [t.equality_product]
  simp only [AddressPartition.parallel_value]
  let H := fun a => Finset.univ.image (@Profile.histogram e.count (j a))
  let val := fun a (q : ↥(H a)) =>
    (e.profile (j a) q.val).value (e.profileTables (j a) q.val first) ((b a).gather (t.inputs s a))
  have hsum (a : A) : p.layout.cutEquality (t.part a) (t.inputs s a) = ∑ q : ↥(H a), val a q := by
    rw [(b a).cutEquality_gather]
    exact (e.profile_sum (j a) first _).symm.trans (Finset.sum_coe_sort (H a) _).symm
  simp_rw [hsum, Fintype.prod_sum]
  rfl

/-- One simultaneous shortening operation. Its choices depend only on the
public tuple of histogram counts. -/
noncomputable def combineSeeds (first : Fin D × Bool) : Replacement p := by
  let ix := (Fintype.equivFin (ProfileCounts e j)).symm
  exact {
    cables := t.selected
    count := Fintype.card (ProfileCounts e j)
    profile i := t.parallel (seedNetwork e j t b (ix i))
    entry i := t.parallelTables _ (seedTables e j t b first (ix i))
    joint s := (sum_seedNetworks e j t b first s).trans (ix.sum_comp (fun q =>
      (t.parallel (seedNetwork e j t b q)).value
        (t.parallelTables _ (seedTables e j t b first q)) s)).symm }

/-- The concrete output pack indexed directly by its public histogram tuple. -/
noncomputable def seedOutput (first : Fin D × Bool) (q : ProfileCounts e j) : Pack D P bits K :=
  let G := t.parallel (seedNetwork e j t b q)
  let T := t.parallelTables (seedNetwork e j t b q) (seedTables e j t b first q)
  ⟨(p.layout.cut t.selected).sew G, (p.layout.cut t.selected).sewTables G
    (p.layout.cutTables t.selected p.table) T⟩

/-- The direct histogram indexing gives exactly the summands of the adaptive step. -/
theorem branch_eq_seedOutput (first : Fin D × Bool) (i : Fin (Fintype.card (ProfileCounts e j))) :
    (combineSeeds e j t b first).branch i =
      seedOutput e j t b first ((Fintype.equivFin (ProfileCounts e j)).symm i) := rfl

/-- The pointwise pack identity, summed over the public count tuples themselves. -/
theorem sum_seedOutputs (first : Fin D × Bool) (x : Ports bits) :
    p.tensor x = ∑ q : ProfileCounts e j, (seedOutput e j t b first q).tensor x :=
  p.layout.value_replace t.selected p.table _ _ (sum_seedNetworks e j t b first) x

/-- Independent simultaneous profile choices give an exact sum of actual
full packs, valid under every assignment to the original free connections. -/
theorem combineSeeds_exact (first : Fin D × Bool) (x : Ports bits) :
    p.tensor x = ∑ i, ((combineSeeds e j t b first).branch i).tensor x :=
  (combineSeeds e j t b first).sum_branches x

end Shortening

end BorderVNP
end Computability
end OAI
