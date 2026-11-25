import OAI.Computability.BorderVNP.ShortenEpochQuotientRecords
import OAI.Computability.BorderVNP.ShortenPreparedMidpoints
import OAI.Computability.BorderVNP.ShortenRetainedLoad

/-!
# Retained records of a chosen shortening step

The prior records and private payload are attached to the actual sites of the
histogram-selected output. The sewing bound uses all records of the moved input,
including both ends of uncharged cables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PlacedStep

open Crossing Cover Epoch SeedIntervals CombiningStep Packing
open scoped Classical

variable {D m d d' k : ℕ} [NeZero D] {K : Type*} [Field K] {I B P : Type}
    [Fintype I] [Fintype B] [Fintype P] {bits : P → ℕ}
    {child : Fin k → PlacedPack D P bits K I d} (s : PlacedStep m B d' child)
    (e : PaidIdentity K D m) (q : s.Index e)

/-- Prior records on retained input sites of this particular output histogram. -/
noncomputable def resultPrior (prior : ∀ i, (child i).pack.layout.Site → ℕ) :
    (s.result e q).pack.layout.Site → ℕ :=
  let p := parallelPacks fun i => (child i).pack
  sewnPrior e (blocks p.layout s.bin s.perm m) (p := pieces (m := m) p s.bin s.perm)
    (partition p.layout s.bin s.perm m) (bundle p.layout s.bin s.perm m s.positive) q
    (fun v => prior v.1 v.2)

/-- Retained private data and the new term-table uses in this output histogram. -/
noncomputable def resultPayload (payload : ∀ i, (child i).pack.layout.Site → ℕ) :
    (s.result e q).pack.layout.Site → ℕ :=
  let p := parallelPacks fun i => (child i).pack
  sewnPayload e (blocks p.layout s.bin s.perm m) (p := pieces (m := m) p s.bin s.perm)
    (partition p.layout s.bin s.perm m) (bundle p.layout s.bin s.perm m s.positive) q
    (fun v => payload v.1 v.2)

/-- Output cost in the actual tile containing each site, in descriptor or expanded mode. -/
noncomputable def resultLocalRecords (expanded : Bool)
    (prior payload : ∀ i, (child i).pack.layout.Site → ℕ) (o : I → Deck (d'+1)) : ℕ :=
  localRecords (s.result e q).pack.layout expanded (s.resultPrior e q prior) (s.resultPayload e q payload)
    (fun v => productTileName d' ((s.result e q).site v) = o)

/-- A fixed sewing constant controls the records of every chosen profile once the
tile cap on the moved disjoint union is known. The midpoint and center conditions
are exactly those satisfied by the prepared-bin placements. -/
theorem placed_result_localRecords (hm : 0 < m) (h ν : ℝ) (hh : 0 ≤ h) (hν : 0 ≤ ν) :
    ∃ C : ℕ, ∀ {d d' k : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
      (child : Fin k → PlacedPack D P bits K I d) (s : PlacedStep m B d' child),
      s.placed.fits _ s.bin s.perm s.positive h ν →
      ∀ oldMid : (parallelPacks fun i => (child i).pack).layout.Edge → SurfaceHost I (d'+1),
      (∀ c a, s.bin c = some a → a.1 = productTileName d' (oldMid c) ∧
        dist (oldMid c) (s.placed.old ((parallelPacks fun i => (child i).pack).layout.src c)) ≤
          dist (s.placed.old ((parallelPacks fun i => (child i).pack).layout.src c))
            (s.placed.old ((parallelPacks fun i => (child i).pack).layout.dst c)) / 2) →
      (∀ a, (s.perm 0 a).1 = productTileName d' (s.placed.project a (s.placed.chart a).center)) →
      ∀ (q : s.Index e) (expanded : Bool) (prior payload : ∀ i, (child i).pack.layout.Site → ℕ) (M : ℕ),
      (∀ o, localRecords (parallelPacks fun i => (child i).pack).layout expanded
        (fun v => prior v.1 v.2) (fun v => payload v.1 v.2) (fun v => productTileName d' (s.placed.old v) = o) ≤ M) →
      ∀ o, 1 + s.resultLocalRecords e q expanded prior payload o ≤ C * (1+M) := by
  obtain ⟨C,cap⟩ := physical_quotient_record_cap (I := I) (B := B) e hm h ν hh hν
  refine ⟨C,?_⟩
  intro d d' k P _ bits child s fits mid hmid hctr q ex prior payload M hmoved o
  exact cap d' _ s.bin s.perm s.positive s.placed fits mid hmid hctr q ex _ _ M hmoved o

end Shortening.PlacedStep

namespace Shortening.PreparedBins

open Crossing Epoch Cover Cover.Frame Hecke Framed PackMotions CombiningStep Packing
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K]
    {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
    (e : PaidIdentity K D m)

/-- Prepared labels and the chosen whole-pack samples discharge the midpoint and
center hypotheses for the record cap of every actual output histogram. -/
theorem placed_result_localRecords (hm : 0 < m) {ν : ℝ} (hh : 0 ≤ h) (hν : 0 ≤ ν) :
    ∃ C : ℕ, ∀ {d n k : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
      (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n)),
      let input := fun i => (child i).pack
      let active := fun i => (child i).active
      let sites := childSites child
      ∀ (L : Labels B input active sites) (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)
        (g : Placement (m := m) (parallelPacks input) (jointBin input (B.tag input active L.kind L.lift) ω)
          (CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart) (Cube D) (SurfaceHost (Cube D) (d+1))),
      g.old = movedOld input ω sites →
      g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart →
      g.project = (fun a => tileProject a.1) →
      g.fits _ _ _ (fun _ => true) h ν →
      let step := B.placedStep child L ω g
      ∀ (q : step.Index e) (expanded : Bool) (prior payload : ∀ i, (child i).pack.layout.Site → ℕ) (M : ℕ),
      (∀ o, localRecords (parallelPacks input).layout expanded (fun v => prior v.1 v.2)
        (fun v => payload v.1 v.2) (fun v => productTileName d (movedOld input ω sites v) = o) ≤ M) →
      ∀ o, 1 + step.resultLocalRecords e q expanded prior payload o ≤ C * (1+M) := by
  obtain ⟨C,cap⟩ := PlacedStep.placed_result_localRecords (I := Cube D) (B := B.Bin) e hm h ν hh hν
  refine ⟨C,?_⟩
  intro d n k P _ bits child input active sites L ω g hold hchart hproject fits step q ex prior payload M hload o
  obtain ⟨mid,addr,hmid,hctr⟩ := B.physical_midpoints input active sites L ω g hold hchart hproject
  apply cap child step fits mid (fun c a hc => (hmid c a hc).2) hctr q ex prior payload M _ o
  intro t
  change localRecords (parallelPacks input).layout ex _ _ (fun v => productTileName d (g.old v) = t) ≤ M
  rw [hold]
  exact hload t

/-- The records of the actual chosen profile are bounded directly in terms of
the largest input tile load. The constant is fixed before the cover depth, the
fan-in, the input packs and all the sampled motions and histograms. -/
theorem result_localRecords_of_children (n : ℕ) (hm : 0 < m) {ν : ℝ} (hh : 0 ≤ h) (hν : 0 ≤ ν) :
    ∃ C : ℕ, ∀ d {k : ℕ} [NeZero k] {P : Type} [Fintype P] {bits : P → ℕ}
      (child : Fin k → PlacedPack D P bits K (Cube D) ((d+1)+2*n)),
      let input := fun i => (child i).pack
      let active := fun i => (child i).active
      let sites := childSites child
      ∀ (L : Labels B input active sites) (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+2) n)
        (g : Placement (m := m) (parallelPacks input) (jointBin input (B.tag input active L.kind L.lift) ω)
          (CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart) (Cube D) (SurfaceHost (Cube D) (d+2))),
      g.old = movedOld input ω sites →
      g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart →
      g.project = (fun a => tileProject a.1) →
      g.fits _ _ _ (fun _ => true) h ν →
      let step := B.placedStep child L ω g
      ∀ (q : step.Index e) (expanded : Bool) (prior payload : ∀ i, (child i).pack.layout.Site → ℕ) (M : ℕ),
      (∀ i t, localRecords (child i).pack.layout expanded (prior i) (payload i)
        (fun v => productTileName ((d+1)+2*n) ((child i).site v) = t) ≤ M) →
      ∀ o, 1 + step.resultLocalRecords e q expanded prior payload o ≤ C * k * (1+M) := by
  obtain ⟨C,cap⟩ := B.placed_result_localRecords e hm hh hν
  obtain ⟨N,move⟩ := moved_children_localRecords D n
  refine ⟨C*(1+N),?_⟩
  intro d k _ P _ bits child input active sites L ω g hold hchart hproject fits step q ex prior payload M hin o
  have moved := move d child ω prior payload ex M hin
  have bound := cap child L ω g hold hchart hproject fits q ex prior payload (N*k*M) moved o
  have hk : 1 ≤ k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hbase : 1 ≤ (1+N)*k := by simpa using Nat.mul_le_mul (show 1 ≤ 1+N by omega) hk
  have hinc : N*k ≤ (1+N)*k := Nat.mul_le_mul_right k (by omega)
  calc
    _ ≤ C * (1+N*k*M) := bound
    _ ≤ C * ((1+N)*k + (1+N)*k*M) :=
      Nat.mul_le_mul_left C (Nat.add_le_add hbase (Nat.mul_le_mul_right M hinc))
    _ = _ := by ring

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
