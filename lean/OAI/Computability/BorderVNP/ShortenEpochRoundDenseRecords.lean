import OAI.Computability.BorderVNP.ShortenDenseMeasurements
import OAI.Computability.BorderVNP.ShortenDenseFitted
import OAI.Computability.BorderVNP.ShortenRetainedLoadStep

/-!
# Per-tile records of the publicly sorted dense physical step

The stable sorting of the merged real cable list preserves every moved
vertex record and both incident endpoint records. The dense midpoint
measurements feed the quotient sewing estimate on the selected dense
partition. The output records below are consequently those installed
on that same sorted histogram.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Stage

open BorderVNP.Cover BorderVNP.Crossing BorderVNP.Shortening BorderVNP.Epoch BorderVNP.Shortening.SeedIntervals
open BorderVNP.Shortening.CombiningStep BorderVNP.Packing
open scoped Classical

variable {D m k d d' : ℕ} [NeZero D] {K : Type*} [Field K] {I B P : Type}
    [Fintype I] [Fintype B] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    (s : Stage m B d' child) (e : PaidIdentity K D m) (q : s.Index e)

/-- Prior record counts installed on the dense histogram's retained and new boxes. -/
noncomputable def resultPrior (prior : ∀ i, (child i).pack.layout.Site → ℕ) :
    (s.result e q).pack.layout.Site → ℕ :=
  sewnPrior e s.matched (p := pieces (m := m) s.input s.label s.perm)
    (partition s.input.layout s.label s.perm m) (bundle s.input.layout s.label s.perm m s.orient) q
    (fun v => prior v.1 v.2)

/-- Retained private data and term-table uses for the actual selected dense histogram. -/
noncomputable def resultPayload (payload : ∀ i, (child i).pack.layout.Site → ℕ) :
    (s.result e q).pack.layout.Site → ℕ :=
  sewnPayload e s.matched (p := pieces (m := m) s.input s.label s.perm)
    (partition s.input.layout s.label s.perm m) (bundle s.input.layout s.label s.perm m s.orient) q
    (fun v => payload v.1 v.2)

/-- The dense physical output's actual public or expanded records at a product tile. -/
noncomputable def resultLocalRecords [Fintype P] (expanded : Bool)
    (prior payload : ∀ i, (child i).pack.layout.Site → ℕ) (o : I → Deck (d'+1)) :=
  localRecords (s.result e q).pack.layout expanded (s.resultPrior e q prior) (s.resultPayload e q payload)
    (fun v => productTileName d' ((s.result e q).site v) = o)

/-- The uniform record-factor contract for the public-order normalized physical step. -/
def RecordFactor (C : ℕ) : Prop :=
  ∀ [Fintype P] (q : s.Index e) (ex : Bool) (prior payload : ∀ i, (child i).pack.layout.Site → ℕ) (M : ℕ),
    (∀ i t, localRecords (child i).pack.layout ex (prior i) (payload i)
      (fun v => productTileName d ((child i).site v) = t) ≤ M) →
    ∀ o, 1+s.resultLocalRecords e q ex prior payload o ≤ C*k*(1+M)

end PackedHistoryCircuit.Normalized.Stage

namespace Shortening.PreparedBins

open BorderVNP.Cover BorderVNP.Cover.Frame BorderVNP.Crossing BorderVNP.Epoch BorderVNP.Hecke
open BorderVNP.Packing Framed PackMotions CombiningStep BorderVNP.PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (e : PaidIdentity K D m)

/-- For all sufficiently deep outputs, any physically measured stable-order step with the
chosen whole-pack motion satisfies the record certificate on its own installed histograms.
One factor works for all child layouts, row injections, fan-ins and original bit widths. -/
theorem dense_result_localRecords (n : ℕ) (hm : 0 < m) {ν : ℝ} (hh : 0 ≤ h) (hν : 0 ≤ ν) :
    ∃ C : ℕ, ∀ (d : ℕ), 0 < d → ∀ {k : ℕ} (hk : 0 < k) {P : Type} {bits : P → ℕ}
      (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n))
      (s : Stage m B.Bin d child)
      (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n),
      s.placed.old = movedOld (fun i => (child i).pack) ω (childSites child) →
      ∀ {u v : ℝ}, Stage.Measurements s hk h ν u v → s.RecordFactor e C := by
  obtain ⟨C,cap⟩ := physical_quotient_record_cap (I := Cube D) (B := B.Bin) e hm h ν hh hν
  obtain ⟨N,move⟩ := moved_children_localRecords D n
  refine ⟨C*(1+N),?_⟩
  intro d hd k hk P bits child s ω hold u v measured
  cases d with
  | zero => omega
  | succ d =>
    intro _ q ex prior payload M oldCap o
    have moved := move d child ω prior payload ex M oldCap
    have dense (t : Cube D → Deck (d+2)) : localRecords s.input.layout ex
        (fun v => prior v.1 v.2) (fun v => payload v.1 v.2)
        (fun v => productTileName (d+1) (s.placed.old v) = t) ≤ N*k*M := by
      apply (Names.localRecords_denseLayout (raw child).layout s.slot ex (fun v => prior v.1 v.2)
        (fun v => payload v.1 v.2) (fun v => productTileName (d+1) (s.placed.old v) = t)).le.trans
      rw [hold]
      exact moved t
    have out := cap (d+1) s.input s.label s.perm s.orient s.placed measured.fits measured.oldMid
      (fun c a hc => (measured.midpoint c a hc).2) measured.center q ex
      (fun v => prior v.1 v.2) (fun v => payload v.1 v.2) (N*k*M) dense o
    have hbase : 1 ≤ (1+N)*k := by simpa using Nat.mul_le_mul (show 1 ≤ 1+N by omega) hk
    have hinc : N*k ≤ (1+N)*k := Nat.mul_le_mul_right k (by omega)
    calc
      _ ≤ C*(1+N*k*M) := out
      _ ≤ C*((1+N)*k+(1+N)*k*M) := Nat.mul_le_mul_left C (Nat.add_le_add hbase (Nat.mul_le_mul_right M hinc))
      _ = _ := by ring

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
