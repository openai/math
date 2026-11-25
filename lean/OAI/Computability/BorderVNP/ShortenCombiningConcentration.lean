import OAI.Computability.BorderVNP.ShortenCombiningStep
import OAI.Computability.BorderVNP.ShortenEpochSewnConcentration

/-!
# Concentration of the sorted and sewn output

Interval subdivision preserves each bin's bit count. One chosen direction
at each seed supplies enough actual bits to pay for that seed's hooks and
new cables. The tile count below includes exactly the positive-length
charged edges in the specified midpoint tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.CombiningStep

open Crossing Epoch SeedIntervals
open scoped BigOperators Classical

variable {D m : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} {K : Type*} [Field K]
variable {A : Type} [Fintype A] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)

omit [Field K] [Fintype A] in
/-- The widths of all active interval bands at a bin sum to its original population. -/
theorem bandAddressWidth (addr : p.layout.Edge → A)
    (haddr : ∀ c a, bin c = some a → addr c = a) (a : A) :
    addressWidth (layout p.layout bin perm m).width (fun c => (bin c.1).isSome = true)
      (fun c => addr c.1) a = count p.layout bin a := by
  unfold addressWidth testedWidth
  rw [count_eq_sum]
  refine (Fintype.sum_prod_type (fun c : p.layout.Edge × Band D =>
    @ite ℕ ((bin c.1).isSome = true ∧ addr c.1 = a) (Classical.propDecidable _)
      ((layout p.layout bin perm m).width c) 0)).trans ?_
  apply Finset.sum_congr rfl
  intro c _
  have he : ((bin c).isSome = true ∧ addr c = a) ↔ bin c = some a := by
    cases hb : bin c with
    | none => simp
    | some a' => simp [haddr c a' hb]
  by_cases hc : bin c = some a
  · simpa [hc, haddr c a hc] using p.layout.sum_bands_width (label p.layout bin perm m) c
  · simp [he, hc]

omit [Field K] [Fintype A] in
/-- The first direction supplies at least one input bit per block whenever
the one-copy width is positive. -/
theorem blocks_le_donor (hm : 0 < m) (a : A) :
    blocks p.layout bin perm m a ≤ count p.layout bin (perm 0 a) := by
  have h := take_le p.layout bin perm m (perm 0 a) 0
  simp only [take, Equiv.symm_apply_apply, common] at h
  exact (Nat.le_mul_of_pos_right _ hm).trans (h.trans (Nat.div_le_self ..))

variable {I : Type*} [Fintype I] {Q : Type*} [PseudoMetricSpace Q]
variable (e : PaidIdentity K D m) (positive : p.layout.Edge → Bool)

/-- The actual sewn layout independently of its local coefficient entries. -/
noncomputable abbrev physical (q : Counts e p bin perm) :=
  sewnProfile e (blocks p.layout bin perm m) (p := pieces (m := m) p bin perm)
    (partition p.layout bin perm m) (bundle p.layout bin perm m positive) q

/-- Quotient placement of retained old sites and inserted profile sites. -/
noncomputable def Placement.postSites (g : Placement (m := m) p bin perm I Q)
    (q : Counts e p bin perm) : (physical p bin perm e positive q).Site → Q :=
  let t := partition p.layout bin perm m
  let G := seedNetwork e _ (p := pieces (m := m) p bin perm) t (bundle p.layout bin perm m positive) q
  Sum.elim g.old (t.parallelSites G (fun a v => g.project a ((g.chart a).atSite ((G a).position v))))

/-- Designated output cables, including the hooks and selectors. -/
noncomputable def postMask (q : Counts e p bin perm) : (physical p bin perm e positive q).Edge → Bool :=
  profileCharges (layout p.layout bin perm m) (partition p.layout bin perm m).selected _
    (fun c => (bin c.1).isSome)

/-- The cost used in the length estimate is on the same edges, with the same
quotient placements and charge mask used in the concentration estimate. -/
theorem result_eq_chargedLength (g : Placement (m := m) p bin perm I Q) (q : Counts e p bin perm) :
    g.result e p bin perm positive q = chargedLength (physical p bin perm e positive q)
      (g.postSites p bin perm e positive q) (postMask p bin perm e positive q) := rfl

/-- Only positive-length charged segments contribute to an output midpoint tile. -/
def Placement.inTile {T : Type*} (g : Placement (m := m) p bin perm I Q)
    (q : Counts e p bin perm) (tile : (physical p bin perm e positive q).Edge → T)
    (o : T) (c : (physical p bin perm e positive q).Edge) : Prop :=
  let N := physical p bin perm e positive q
  let place := g.postSites p bin perm e positive q
  postMask p bin perm e positive q c = true ∧
    place (N.src c) ≠ place (N.dst c) ∧ tile c = o

variable {T B : Type} [Fintype T] [Fintype B]

/-- The second line of (6.3) for the concrete sorted-interval output, using
the measured support of retained midpoints, hooks and new profile segments.
All population and donor-width estimates come from the actual pool allocation. -/
theorem normalized_concentration (p : Pack D P bits K) (bin : p.layout.Edge → Option (T × B))
    (perm : Fin D → Equiv.Perm (T × B)) (e : PaidIdentity K D m) (hm : 0 < m)
    (positive : p.layout.Edge → Bool) (g : Placement (m := m) p bin perm I Q)
    (q : Counts e p bin perm) (tile : (physical p bin perm e positive q).Edge → T)
    (addr : p.layout.Edge → T × B) (haddr : ∀ c a, bin c = some a → addr c = a)
    (near : T → Finset (T × B))
    (hretain : ∀ o (c : {c : (layout p.layout bin perm m).Edge // c ∉ (partition p.layout bin perm m).selected}),
      g.inTile p bin perm e positive q tile o (.inr (.inl c)) → addr c.val.1 ∈ near o)
    (hhook : ∀ o a k, g.inTile p bin perm e positive q tile o
      (.inl ((partition p.layout bin perm m).includePort a k)) → perm 0 a ∈ near o)
    (hnew : ∀ o a x, g.inTile p bin perm e positive q tile o (.inr (.inr ⟨a,x⟩)) → perm 0 a ∈ near o)
    (fanIn fanOut : ℕ) (hIn : ∀ o, (near o).card ≤ fanIn)
    (hOut : ∀ a, (Finset.univ.filter fun o => a ∈ near o).card ≤ fanOut)
    (mean : T × B → ℝ) {copies W err : ℝ} (hk : 0 < copies)
    (hmean : Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy mean) ≤ W)
    (hdev : Real.sqrt (Fintype.card T) *
      Real.sqrt (binEnergy fun a => count p.layout bin a / copies - mean a) ≤ err) :
    Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy (fun o =>
      testedWidth (physical p bin perm e positive q).width (g.inTile p bin perm e positive q tile o) / copies)) ≤
      ((1 + profileWidthBound e : ℕ) : ℝ) * Real.sqrt ((fanIn : ℝ) * fanOut) * (W + err) := by
  let n := layout p.layout bin perm m
  let active := fun c : n.Edge => (bin c.1).isSome = true
  let label := fun c : n.Edge => addr c.1
  have hcount (a) : addressWidth (pieces (m := m) p bin perm).layout.width active label a = count p.layout bin a :=
    bandAddressWidth (m := m) p bin perm addr haddr a
  apply sewnProfile_concentration e _ (p := pieces (m := m) p bin perm)
    (partition p.layout bin perm m) (bundle p.layout bin perm m positive) q active label
    (perm 0) near (g.inTile p bin perm e positive q tile)
    (fun o c hc => ⟨hc.1, hretain o c hc⟩) hhook hnew _ fanIn fanOut hIn hOut mean hk hmean
  · simpa only [hcount] using hdev
  · intro a; rw [hcount]; exact blocks_le_donor p bin perm hm a

end Shortening.CombiningStep

end BorderVNP
end Computability
end OAI
