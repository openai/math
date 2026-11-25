import OAI.Geometry.Hirsch.ProbeStability
import OAI.Geometry.Hirsch.Reduction

noncomputable section

open Set Filter
open scoped Topology

namespace OAI.Geometry.Hirsch

abbrev Package.adjust (pkg : Package) (delta : pkg.Row → ℝ) : Package :=
  { pkg with block := { pkg.block with offset := pkg.block.offset + delta } }

theorem Package.adjust_rhs (pkg : Package) (delta : pkg.Row → ℝ) (time : ℝ) :
    ((pkg.adjust delta).block.slice time).rhs = (pkg.block.slice time).rhs + delta := by
  funext row
  simp [Blocking.slice, add_assoc]

abbrev Coloring.adjust {pkg client buckets} (paint : Coloring pkg client buckets)
    (delta : pkg.Row → ℝ) : Coloring (pkg.adjust delta) client buckets :=
  ⟨paint.color, paint.covered, paint.ordinary⟩

structure Samples (client : Program) {count : ℕ} (episodes : Episodes count) (buckets labels : ℕ) where
  pkg : Package
  paint : Coloring pkg client buckets
  time : Fin count → Fin buckets → ℝ
  interior : ∀ idx bucket, time idx bucket ∈ Ioo (episodes.left idx) (episodes.right idx)
  eps : ℝ
  positive : 0 < eps
  probe : ∀ delta : pkg.Row → ℝ, (∀ row, 0 ≤ delta row ∧ delta row < eps) →
    ∀ idx bucket, paint.VertexTest bucket ((pkg.block.slice (time idx bucket)).rhs + paint.vary true delta)
  anchor : ∀ idx pt, pt = episodes.left idx ∨ pt = episodes.right idx →
    paint.Anchor pt (2 * eps) (2 * labels * Fintype.card client.Coord)
  groupBound : ∀ bucket coord, (paint.group bucket coord).ncard ≤ 2 * labels
  spanBound : ∀ bucket (coords : Set client.Coord) (pick : client.Coord → pkg.Row),
    (∀ coord ∈ coords, pick coord ∈ paint.group bucket coord) →
      (pkg.prog.closure (⋃ coord ∈ coords, pkg.block.support (pick coord))).ncard ≤
        5 * (client.closure coords).ncard

theorem Coloring.anchor_adjust {pkg client buckets} (paint : Coloring pkg client buckets)
    {time eps tol : ℝ} {bound : ℕ} (ha : paint.Anchor time (2 * eps) bound)
    (delta : pkg.Row → ℝ) (hd : ∀ row, |delta row| < eps) (ht : tol ≤ eps) :
    (paint.adjust delta).Anchor time tol bound := by
  intro vec hv
  have he : ∀ row, (pkg.adjust delta).block.slack row (time, vec) =
      pkg.block.slack row (time, vec) - delta row := by
    intro row
    simp only [Blocking.slack, Package.adjust, Pi.add_apply]
    ring
  have hl : ∀ row, -(2 * eps) < pkg.block.slack row (time, vec) := by
    intro row
    linarith [hv row, he row, (abs_lt.mp (hd row)).1]
  apply le_trans _ (ha vec hl)
  refine ncard_le_ncard ?_ (toFinite _)
  rintro bucket ⟨coord, row, hr, hh⟩
  refine ⟨coord, row, ?_, hh⟩
  change (pkg.adjust delta).block.slack row (time, vec) < tol at hr
  change pkg.block.slack row (time, vec) < 2 * eps
  linarith [he row, (abs_lt.mp (hd row)).2]

theorem Coloring.band {pkg client buckets} (paint : Coloring pkg client buckets)
    {time left right : ℝ} (ht : time ∈ Ioo left right) (bucket : Fin buckets)
    (hg : paint.Good bucket (pkg.block.slice time).rhs) :
    ∃ ph : Phases, left < ph.bandLeft ∧ ph.bandRight < right ∧ ∃ tol > 0,
      ∀ pt ∈ Icc ph.bandLeft ph.bandRight, paint.Probe bucket pt tol := by
  let rhs := fun pt => (pkg.block.slice pt).rhs
  have hc : Continuous rhs := continuous_pi fun row => by unfold rhs Blocking.slice; fun_prop
  obtain ⟨radius, hr, hh⟩ := Metric.mem_nhds_iff.mp ((paint.open_good bucket).mem_nhds hg)
  have he : ∀ᶠ pt in 𝓝 time, pt ∈ Ioo left right ∧ dist (rhs pt) (rhs time) < radius/2 :=
    Eventually.and (isOpen_Ioo.mem_nhds ht)
      (hc.continuousAt.eventually (Metric.ball_mem_nhds _ (half_pos hr)))
  obtain ⟨width, hw, hnear⟩ := Metric.eventually_nhds_iff.mp he
  let ph : Phases := ⟨time - width/2, time - width/4, time + width/4, time + width/2,
    by linarith, by linarith, by linarith⟩
  have hband : ∀ pt ∈ Icc ph.bandLeft ph.bandRight,
      pt ∈ Ioo left right ∧ dist (rhs pt) (rhs time) < radius/2 := by
    rintro pt ⟨hl, hu⟩
    apply hnear
    rw [Real.dist_eq, abs_lt]
    dsimp [ph] at hl hu
    constructor <;> linarith
  have hle := ((ph.early.trans ph.ordered).trans ph.late).le
  refine ⟨ph, (hband _ (left_mem_Icc.mpr hle)).1.1, (hband _ (right_mem_Icc.mpr hle)).1.2,
    radius/2, half_pos hr, fun pt hp => paint.probe_of_good (fun other ho => ?_)⟩
  apply hh
  have hd : dist other (rhs pt) < radius/2 := (dist_pi_lt_iff (half_pos hr)).mpr
    (fun row => by rw [Real.dist_eq]; exact ho row)
  change dist other (rhs time) < radius
  linarith [dist_triangle other (rhs pt) (rhs time), (hband pt hp).2]

theorem Samples.schedule {client count buckets labels} {ep : Episodes count}
    (samples : Samples client ep buckets labels) {bank size rows span}
    (hf : samples.pkg.Fits bank size rows span) :
    ∃ sch : Schedule client ep buckets labels, sch.pkg.Fits bank size rows span := by
  let base := fun pair : Fin count × Fin buckets => (samples.pkg.block.slice (samples.time pair.1 pair.2)).rhs
  obtain ⟨delta, hd, hg⟩ := samples.paint.perturb_probes base Prod.snd samples.positive
    (fun delta hh pair => samples.probe delta hh pair.1 pair.2)
  let paint := samples.paint.adjust delta
  have hgood : ∀ idx bucket, paint.Good bucket
      ((samples.pkg.adjust delta).block.slice (samples.time idx bucket)).rhs := by
    intro idx bucket
    rw [Package.adjust_rhs]
    exact hg (idx, bucket)
  choose ph hl hu tol ht hp using fun idx bucket =>
    paint.band (samples.interior idx bucket) bucket (hgood idx bucket)
  let bounds : Option (Fin count × Fin buckets) → ℝ := fun opt =>
    opt.elim samples.eps (fun pair => tol pair.1 pair.2)
  have hpos : 0 < least bounds := by
    obtain ⟨_ | pair, he⟩ := least_attained bounds
    · exact he.symm ▸ samples.positive
    · exact he.symm ▸ ht pair.1 pair.2
  let sch : Schedule client ep buckets labels := {
    pkg := samples.pkg.adjust delta, paint := paint, phase := ph,
    contained := fun idx bucket => ⟨hl idx bucket, hu idx bucket⟩,
    tol := least bounds, positive := hpos,
    probe := fun idx bucket time hh usable rhs hr => hp idx bucket time hh usable rhs
      (fun row => (hr row).trans_le (least_le bounds (some (idx, bucket)))),
    anchor := fun idx time hh => samples.paint.anchor_adjust (samples.anchor idx time hh) delta hd
      (least_le bounds none),
    groupBound := samples.groupBound, spanBound := samples.spanBound }
  exact ⟨sch, hf⟩

end OAI.Geometry.Hirsch
