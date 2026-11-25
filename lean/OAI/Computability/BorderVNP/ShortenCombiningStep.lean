import OAI.Computability.BorderVNP.ShortenAddressQuotient
import OAI.Computability.BorderVNP.ShortenSeedIntervalsBundles
import OAI.Computability.BorderVNP.ShortenEpochStep

/-!
# The exact combining operation and its length estimate

Starting with the union of the moved input packs, sort and split its charged
cables into pools, insert all physical histogram networks at once, and sum
over the public profile tuples. The resulting sewn networks satisfy the
first line of (6.3) when the finite motion estimates hold. All old distances
are measured in the quotient.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.CombiningStep

open Crossing Epoch SeedIntervals
open scoped BigOperators Classical

variable {D m : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} {K : Type*} [Field K]
variable {A : Type} [Fintype A] (e : PaidIdentity K D m) (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
variable (positive : p.layout.Edge → Bool)

/-- The exact refinement into consecutive intervals, before inserting profiles. -/
noncomputable def pieces : Pack D P bits K :=
  ⟨layout p.layout bin perm m, p.layout.bandTables (label p.layout bin perm m) p.table⟩

/-- Public count tuple for the actual matched multiplicities. -/
abbrev Counts := ProfileCounts e (blocks p.layout bin perm m)

/-- Physical output of the combining step indexed by the profile tuple. -/
noncomputable def output (first : Fin D × Bool) (q : Counts e p bin perm) : Pack D P bits K :=
  seedOutput e (blocks p.layout bin perm m) (p := pieces (m := m) p bin perm)
    (partition p.layout bin perm m) (bundle p.layout bin perm m positive) first q

/-- Subdivision and all profile insertions together preserve the full pack tensor. -/
theorem exact_sum (first : Fin D × Bool) (x : Ports bits) :
    p.tensor x = ∑ q : Counts e p bin perm, (output e p bin perm positive first q).tensor x := by
  refine (p.layout.value_bands (label p.layout bin perm m) p.table x).symm.trans ?_
  exact sum_seedOutputs e _ (p := pieces (m := m) p bin perm)
    (partition p.layout bin perm m) (bundle p.layout bin perm m positive) first x

/-- Continue an adaptive profile transcript after the deterministic interval split. -/
noncomputable def history (first : Fin D × Bool) (next : ∀ q : Counts e p bin perm,
    History (output e p bin perm positive first q)) : History p :=
  History.refinePack (q := pieces (m := m) p bin perm)
    (fun x => (p.layout.value_bands (label p.layout bin perm m) p.table x).symm) <|
    .step (combineSeeds e _ (p := pieces (m := m) p bin perm) (partition p.layout bin perm m)
      (bundle p.layout bin perm m positive) first) (fun i => next ((Fintype.equivFin _).symm i))

variable (I : Type*) [Fintype I] (Q : Type*) [PseudoMetricSpace Q]

/-- Public placements of the moved inputs and of the canonical seed crossings.
Only the selected slots of a single seed have to be lifted together. -/
structure Placement where
  /-- Actual quotient sites of all input vertices. -/
  old : p.layout.Site → Q
  /-- A tangent chart for each matched crossing. -/
  chart : A → SeedChart I D
  /-- Projection of each lifted neighborhood back into the quotient host. -/
  project : A → HyperbolicHost I → Q
  /-- Endpoint lifts in this seed's neighborhood. -/
  lift : ∀ a, (layout p.layout bin perm m).CutPorts ((partition p.layout bin perm m).part a) →
    HyperbolicHost I
  /-- Projecting a cable never increases its length. -/
  nonexpanding : ∀ a u v, dist (project a u) (project a v) ≤ dist u v
  /-- Each local lift projects to its own old slot at its actual site. -/
  projects : ∀ a u, project a (lift a u) =
    oldEndpoint (layout p.layout bin perm m) ((partition p.layout bin perm m).part a) old u
  /-- Input bin addresses record the actual common segment length. -/
  bin_length : ∀ c a, bin c = some a → dist (old (p.layout.src c)) (old (p.layout.dst c)) = 2*(chart a).radius
  /-- Direction permutations do not change the length coordinate. -/
  invariant : ∀ i a, (chart (perm i a)).radius = (chart a).radius

variable {I Q}

/-- The quotient charged length of the combined pack before shortening. -/
noncomputable def Placement.input (g : Placement (m := m) p bin perm I Q) : ℝ :=
  chargedLength p.layout g.old (fun c => (bin c).isSome)

/-- The actual quotient charged length of the output associated with the specified counts. -/
noncomputable def Placement.result (g : Placement (m := m) p bin perm I Q) (q : Counts e p bin perm) : ℝ :=
  combinedQuotientLength e _ (pieces (m := m) p bin perm) (partition p.layout bin perm m)
    (bundle p.layout bin perm m positive) g.old (fun c => (bin c.1).isSome) g.project g.chart q

/-- Radius and endpoint tolerance in the common tangent charts. -/
def Placement.fits (g : Placement (m := m) p bin perm I Q) (h ν : ℝ) : Prop :=
  (∀ a, (g.chart a).radius ∈ Set.Icc (0 : ℝ) h) ∧
  ∀ a u, dist (g.lift a u) ((g.chart a).atTerminal ((bundle p.layout bin perm m positive a).terminal u)) ≤
    ν/4 * (g.chart a).radius

/-- Every actual output at a combining step obeys the first inequality of
(6.3). The matched-length saving, pool rounding, preservation of all tensors,
and quotient projection have all been accounted for on the concrete networks.
The two motion hypotheses are the mean coverage and the deviation in (6.2). -/
theorem normalized_length (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ h : ℝ, 0 < h ∧ ∀ {Q : Type*} [PseudoMetricSpace Q] {P : Type*} {bits : P → ℕ}
      (p : Pack D P bits K) {T B : Type} [Fintype T] [Fintype B]
      (bin : p.layout.Edge → Option (T × B)) (perm : Fin D → Equiv.Perm (T × B))
      (positive : p.layout.Edge → Bool) (g : Placement (m := m) p bin perm I Q),
      g.fits p bin perm positive h ν → ∀ copies : ℝ, 0 < copies →
      ∀ (mean : T × B → ℝ) (err : ℝ),
      (g.input p bin perm / copies) / 2 ≤ matchedLength perm (fun a => 2*(g.chart a).radius) mean →
      Real.sqrt (Fintype.card T) *
        Real.sqrt (binEnergy (fun a => (count p.layout bin a : ℝ) / copies - mean a)) ≤ err →
      ∀ q : Counts e p bin perm, g.result e p bin perm positive q / copies ≤
        (1 - (ν/2)/2) * (g.input p bin perm / copies) +
        (ν/2) * ((D : ℝ) * ((2*h) * (Real.sqrt (Fintype.card B) * err))) +
        (ν/2) * ((∑ a, (2*(g.chart a).radius) * (D*m : ℕ)) / copies) := by
  obtain ⟨ν,hν,h,hh,hsave⟩ := quotient_combining_saving (I := I) e
    (Nat.pos_of_ne_zero (NeZero.ne D)) hm
  refine ⟨ν,hν,h,hh,?_⟩
  intro Q _ P bits p T B _ _ bin perm positive g fits copies hk mean err hmean hdev q
  let t := partition p.layout bin perm m
  let b := bundle p.layout bin perm m positive
  let l := fun a : T × B => 2*(g.chart a).radius
  have hl (a : T × B) : 0 ≤ l a ∧ l a ≤ 2*h :=
    ⟨mul_nonneg (by norm_num) (fits.1 a).1, mul_le_mul_of_nonneg_left (fits.1 a).2 (by norm_num)⟩
  have hinv (i : Fin D) (a) : l (perm i a) = l a := by dsimp [l]; rw [g.invariant i a]
  have charged (a) (c) (hc : c ∈ t.part a) : (bin c.1).isSome = true := by
    have he := bin_selected p.layout bin perm m (a := a) ⟨c,hc⟩
    rw [he]; rfl
  have lengths (a) (c : ↥(t.part a)) : dist (g.old (p.layout.src c.val.1)) (g.old (p.layout.dst c.val.1)) =
      2*(g.chart a).radius := (g.bin_length _ _ (bin_selected p.layout bin perm m c)).trans (hinv _ _)
  have raw := hsave (pieces (m := m) p bin perm) t _ b g.old (fun c => (bin c.1).isSome)
    g.project g.chart g.lift g.nonexpanding g.projects fits.1 charged lengths fits.2 q
  have hsel := (t.selectedLength_sum g.old).symm.trans
    (SeedIntervals.selectedLength_eq p.layout bin perm m g.old l g.bin_length hinv)
  have hraw : g.result e p bin perm positive q ≤ g.input p bin perm - (ν/2) *
      (∑ a, l a * pooledBits m (fun d => count p.layout bin (perm d a))) := by
    exact raw.trans_eq (congrArg₂ (fun x y : ℝ => x - (ν/2)*y)
      (p.layout.chargedLength_bands (label p.layout bin perm m) g.old (fun c => (bin c).isSome)) hsel)
  have hdiv := div_le_div_of_nonneg_right hraw hk.le
  rw [sub_div, mul_div_assoc] at hdiv
  simpa only [Fintype.card_fin] using normalized_length_saving perm l hl (by positivity) hinv
    (count p.layout bin) mean hk (show 0 ≤ ν/2 by positivity) hm hmean hdev hdiv

end Shortening.CombiningStep

end BorderVNP
end Computability
end OAI
