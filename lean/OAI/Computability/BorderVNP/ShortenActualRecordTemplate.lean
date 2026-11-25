import OAI.Computability.BorderVNP.ShortenActualTemplate
import OAI.Computability.BorderVNP.ShortenStageRecords

/-!
# Actual measured stage preparations retaining the record certificate

The selected physical child labels, Hecke samples, canonical charts and
histogram network are shared by the length, concentration and record proofs.
Thus the same finite templates suffice for every tile depth, every positive
fan-in and every choice of input tables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Epoch Cover Cover.Frame Framed Adaptive CombiningStep
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

set_option maxHeartbeats 900000 in
/-- A prepared bin system supplies a jointly measured stage and a uniform
physical record factor. The source labels and motion of a child tuple are
chosen once for all histogram branches and all site payloads. -/
theorem PreparedBins.stageTemplate_records {S : Finset (HyperbolicHost (Cube D))} {h H ν θ η : ℝ}
    (B : PreparedBins D S h η) (hm : 0 < m) (hh : 0 ≤ h) (hH : h ≤ H) (ht : 0 ≤ θ)
    (hθ : θ ≤ ν) (hsafe : θ ≤ 4) (hη : η ≤ θ/4) :
    ∃ t : StageTemplate e (Cube D) h H ν S, ∃ C : ℕ, t.HasRecordFactor C := by
  obtain ⟨n,l,u,v,hu,hv,run⟩ := (B.eventually_measured (K := K) hh hη).exists
  obtain ⟨C,records⟩ := B.result_localRecords_of_children e n hm hh ht
  have joint (d : ℕ) (hd : max 1 l ≤ d) {k : ℕ} (hk : 0 < k) {P : Type} {bits : P → ℕ}
      (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n))
      (prep : ∀ i, Catalog.PlacedAt S h (child i)) :
      ∃ s : PlacedStep m B.Bin d child, Nonempty (PlacedStep.Measurements s hk H ν u v) ∧
        s.RecordFactor e C ∧ ∀ q : s.Index e, Catalog.PlacedAt (B.successorSites n e) h (s.result e q) := by
    cases d with
    | zero => omega
    | succ d =>
      let : NeZero k := ⟨Nat.ne_of_gt hk⟩
      obtain ⟨L,ω,g,hold,hchart,hproject,⟨measure⟩⟩ := run (d+1) ((le_max_right ..).trans hd) (m := m) hk child
        (fun i => (prep i).sites) (fun i => (prep i).short) (fun i => (prep i).midpoint)
      let s := B.placedStep child L ω g
      have wide : Nonempty (PlacedStep.Measurements s hk H ν u v) :=
        ⟨{measure with fits := s.placed.fits_mono _ s.bin s.perm s.positive hH hθ measure.fits}⟩
      refine ⟨s,wide,?_,?_⟩
      · intro fp
        exact records d child L ω g hold hchart hproject measure.fits
      · intro q
        obtain ⟨sites,cap⟩ := B.result_catalog child L ω g e (fun i => (prep i).sites)
          hold hchart hproject hsafe measure.fits q
        exact Catalog.PlacedAt.result e s q _ _ sites cap
  let t : StageTemplate e (Cube D) h H ν S := {
    Bin := B.Bin
    nextSites := B.successorSites n e
    word := n
    floor := max 1 l
    meanFactor := u
    motionFactor := v
    nonneg := ⟨hu,hv⟩
    run := fun d hd {_} hk {_ _} child prep => (joint d hd hk child prep).imp fun _ hs => ⟨hs.1,hs.2.2⟩ }
  exact ⟨t,C,joint⟩

/-- The common short scale works for every subsequent finite catalog, with
both measured rows and all physical records certified on one selected operation. -/
theorem exists_record_templates {H ν : ℝ} (hm : 0 < m) (hH : 0 < H) (hν : 0 < ν) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/8 ∧ ∀ S : Finset (HyperbolicHost (Cube D)),
      ∃ t : StageTemplate e (Cube D) h H ν S, ∃ C : ℕ, t.HasRecordFactor C := by
  let θ := min ν 1
  have ht : 0 < θ := lt_min hν zero_lt_one
  let η := θ/4
  obtain ⟨h₀,hp,charts⟩ := exists_preparedBins (D := D) (show 0 < η from div_pos ht (by norm_num))
  let h := min (min H h₀) (1/8)
  have hh : 0 < h := lt_min (lt_min hH hp) (by norm_num)
  have small : h ≤ min H h₀ := min_le_left ..
  refine ⟨h,hh,min_le_right ..,?_⟩
  intro S
  obtain ⟨B⟩ := charts h ⟨hh,small.trans (min_le_right ..)⟩ S
  exact B.stageTemplate_records e hm hh.le (small.trans (min_le_left ..)) ht.le (min_le_left ..)
    ((min_le_right ν 1).trans (by norm_num)) le_rfl

/-- The entire relative site sequence and all its record constants are
chosen from the original catalog and finite number of rounds before
the fan-in, depth and physical leaf tuple. -/
theorem exists_record_path {H ν : ℝ} (hm : 0 < m) (hH : 0 < H) (hν : 0 < ν) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/8 ∧ ∀ (b : ℕ) (initial : Finset (HyperbolicHost (Cube D))),
      ∃ path : StagePath b e (Cube D) h H ν, path.catalog 0 = initial ∧
      ∃ C : Fin b → ℕ, ∀ i, (path.pattern i).HasRecordFactor (C i) := by
  obtain ⟨h,hh,hshort,prep⟩ := exists_record_templates e hm hH hν
  refine ⟨h,hh,hshort,?_⟩
  intro b initial
  obtain ⟨path,hpath,hcert⟩ := exists_stage_path_with (e := e) b initial
    (fun _ t => ∃ C : ℕ, t.HasRecordFactor C) prep
  choose C hC using hcert
  exact ⟨path,hpath,C,hC⟩

end Shortening

end BorderVNP
end Computability
end OAI
