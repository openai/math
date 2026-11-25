import OAI.Geometry.Hirsch.Floors

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

structure Assembly (clock res : Package) {count buckets labels : ℕ} {ep : Episodes count}
    (sch : Schedule res.prog ep buckets labels) (windows : ℕ) [NeZero count] where
  floors : Floors ep sch.phase
  cap : ℝ
  cap_ge : 1 ≤ cap
  bounded : ∀ bucket side time, time ∈ Icc (0 : ℝ) 1 → floors.value bucket side time ≤ cap
  upper : ∀ side, Overlay clock windows (some side) cap
  lower : Overlay res windows none cap
  rho : ℝ
  tuneUpper : ∀ side, Tuned (upper side).block cap rho
  tuneLower : Tuned lower.block cap rho

namespace Assembly

variable {clock res : Package} {count buckets labels windows : ℕ} [NeZero count]
  {ep : Episodes count} {sch : Schedule res.prog ep buckets labels}

theorem exists_assembly (clock res : Package) (sch : Schedule res.prog ep buckets labels)
    (hw : 0 < windows) : Nonempty (Assembly clock res sch windows) := by
  obtain ⟨floors⟩ := Floors.exists_floors ep sch.phase
  obtain ⟨cap, hc, hb⟩ := floors.upper
  let upper := fun side => Overlay.make clock hw (some side) cap
  let lower := Overlay.make res hw none cap
  choose eps he ht using fun side => tune (upper side).unit cap
  obtain ⟨delta, hd, hl⟩ := tune lower.unit cap
  let rho := min delta (min (eps false) (eps true))
  have hp : 0 < rho := lt_min hd (lt_min (he _) (he _))
  exact ⟨⟨floors, cap, hc, hb, upper, lower, rho, fun side => ht side _ hp (by
    cases side <;> simp [rho]), hl _ hp (min_le_left ..)⟩⟩

variable (asm : Assembly clock res sch windows)

abbrev cp : Coupler clock.prog.Coord (Overlay.Rows clock windows) res.prog.Coord (Overlay.Rows res windows) :=
  ⟨fun side => (asm.upper side).block, asm.lower.block, asm.cap, asm.cap_ge, asm.rho,
    asm.tuneUpper, asm.tuneLower⟩

def scale := (asm.cp.slack_bound.choose + 1) / sch.tol

abbrev machine : Machine where
  sched := sch.pkg
  clock := clock
  client := res.prog
  buckets := buckets
  paint := sch.paint
  ClockRow := Overlay.Rows clock windows
  ResRow := Overlay.Rows res windows
  cp := asm.cp
  Piece := Fin count × Bool
  slope bucket side pos := asm.floors.piece bucket side pos 1 - asm.floors.piece bucket side pos 0
  offset bucket side pos := asm.floors.piece bucket side pos 0
  scale := asm.scale
  positive := div_pos (by linarith [asm.cp.slack_bound.choose_spec.1]) sch.positive

theorem floor_eq (bucket side time) : asm.machine.floor bucket side time = asm.floors.value bucket side time := by
  unfold Machine.floor Floors.value
  congr 1
  funext pos
  exact asm.floors.affine ..

theorem floor_bounds : asm.machine.Floors := by
  intro bucket side time ht
  rw [asm.floor_eq]
  exact ⟨asm.floors.lower .., asm.bounded _ _ _ ht⟩

theorem controlled : asm.machine.Controlled sch.tol := by
  apply asm.machine.controlled sch.positive _ asm.floor_bounds asm.cp.slack_bound.choose_spec.2
  change _ < asm.scale * sch.tol
  rw [scale, div_mul_cancel₀ _ sch.positive.ne']
  linarith

variable (idx : Fin count) (bucket : Fin buckets)

def phase (side : Bool) : Set ℝ :=
  if side then Icc (sch.phase idx bucket).lateStart (ep.right idx)
  else Icc (ep.left idx) (sch.phase idx bucket).earlyEnd

omit [NeZero count] in
theorem phase_sub (side : Bool) :
    phase (sch := sch) idx bucket side ⊆ Icc (ep.left idx) (ep.right idx) := by
  obtain ⟨hl, hr⟩ := sch.contained idx bucket
  have he := (sch.phase idx bucket).early
  have ho := (sch.phase idx bucket).ordered
  have hh := (sch.phase idx bucket).late
  cases side <;> simp only [phase, Bool.false_eq_true, ↓reduceIte] <;>
    apply Icc_subset_Icc <;> linarith

theorem phase_value (side : Bool) {time : ℝ} (ht : time ∈ phase (sch := sch) idx bucket side) :
    asm.machine.phaseValue bucket time = if side then 1 else 0 := by
  have hm := phase_sub idx bucket side ht
  rw [Machine.phaseValue, floor_eq, floor_eq, asm.floors.on_episode idx _ _ hm,
    asm.floors.on_episode idx _ _ hm]
  cases side
  · rw [max_eq_left ((sch.phase idx bucket).ramp_early ht.2 false),
      max_eq_left ((sch.phase idx bucket).ramp_early ht.2 true)]
    simp
  · rw [max_eq_right ((sch.phase idx bucket).ramp_late ht.1 false),
      max_eq_right ((sch.phase idx bucket).ramp_late ht.1 true)]
    simp [Phases.ramp]

variable {limit cost : ℕ}

theorem upper_transfer (side : Bool) (large : clock.prog.Large limit)
    (bound : CrossingBound (clock.region limit) 0 1 (2 * cost + 1)) (pos : Fin windows) :
    Transfer (asm.machine.region limit) (asm.machine.reading bucket) (phase (sch := sch) idx bucket side)
      (Windows.start pos) (Windows.stop pos) cost := by
  have aux : ∀ pt ∈ asm.machine.region limit, pt.1 ∈ phase (sch := sch) idx bucket side →
      asm.machine.reading bucket pt ∈ Icc (1/4) (3/4) →
      |asm.machine.reading bucket pt| ≤ asm.cap ∧ asm.machine.Active pt bucket ∧
      asm.machine.clockImage bucket side pt ∈ (asm.upper side).block.admissible clock.prog.viable limit := by
    intro pt hp ht hr
    have hx := Icc_subset_Icc (ep.positive idx).le (ep.interior idx).le (phase_sub idx bucket side ht)
    have hf := asm.machine.free_of_phase asm.floor_bounds hp.1 hx hr (asm.phase_value idx bucket side ht)
    exact ⟨asm.machine.time_bound asm.floor_bounds hp.1 hx _, asm.machine.clock_transfer large hp hf⟩
  apply (asm.upper side).transfer _ (asm.machine.continuous_reading bucket)
    (asm.machine.clockImage bucket side) (fun _ => rfl) _ _ bound pos
  · intro pt hp ht hr
    obtain ⟨hv, _, hh⟩ := aux pt hp ht hr
    exact ⟨hv, hh⟩
  · intro first hf last hl hm ht hr
    exact asm.machine.clock_mid hf.1 hl.1 (aux _ hm ht hr).2.1 side

theorem lower_transfer (large : res.prog.Large limit)
    (bound : CrossingBound (res.region limit) 0 1 (2 * cost + 1)) (pos : Fin windows) :
    Transfer (asm.machine.region limit) (asm.machine.reading bucket)
      (Icc (sch.phase idx bucket).bandLeft (sch.phase idx bucket).bandRight)
      (Windows.start pos) (Windows.stop pos) cost := by
  have aux : ∀ pt ∈ asm.machine.region limit,
      pt.1 ∈ Icc (sch.phase idx bucket).bandLeft (sch.phase idx bucket).bandRight →
      |asm.machine.reading bucket pt| ≤ asm.cap ∧ asm.machine.Active pt bucket ∧
      asm.machine.resource bucket pt ∈ asm.lower.block.admissible res.prog.viable limit := by
    intro pt hp ht
    have hc := sch.contained idx bucket
    have hx := Icc_subset_Icc ((ep.positive idx).trans hc.1).le (hc.2.trans (ep.interior idx)).le ht
    exact ⟨asm.machine.time_bound asm.floor_bounds hp.1 hx _,
      asm.machine.resource_transfer sch.positive asm.controlled large hp hx (sch.probe idx bucket _ ht)⟩
  apply asm.lower.transfer _ (asm.machine.continuous_reading bucket)
    (asm.machine.resource bucket) (fun _ => rfl) _ _ bound pos
  · intro pt hp ht _
    obtain ⟨hv, _, hh⟩ := aux pt hp ht
    exact ⟨hv, hh⟩
  · intro first hf last hl hm ht _
    exact asm.machine.resource_mid hf.1 hl.1 (aux _ hm ht).2.1

theorem active_bound {pt : asm.machine.Point} (hp : pt ∈ asm.machine.region limit)
    (ht : pt.1 = ep.left idx ∨ pt.1 = ep.right idx) :
    {bucket | asm.machine.Active pt bucket}.ncard ≤ 2 * labels * res.size := by
  have hx : pt.1 ∈ Icc (0 : ℝ) 1 := by
    have := ep.positive idx
    have := ep.width idx
    have := ep.interior idx
    rcases ht with hh | hh <;> constructor <;> linarith
  obtain ⟨hf, hs⟩ := asm.controlled pt hp.1 hx
  apply le_trans _ (sch.anchor idx _ ht (asm.machine.schedPt pt).2 hf)
  refine ncard_le_ncard ?_ (toFinite _)
  intro bucket ha
  obtain ⟨coord, row, hr, he⟩ := asm.machine.active_iff.mp ha
  exact ⟨coord, row, hs row hr, he⟩

theorem anchors (large : clock.prog.Large limit) (hb : 4 * labels * res.size < buckets)
    {first last : asm.machine.Point} (hf : first ∈ asm.machine.region limit)
    (hl : last ∈ asm.machine.region limit) (ht : first.1 = ep.left idx) (hu : last.1 = ep.right idx) :
    ∃ bucket, ∀ pos : Fin windows, Spans (asm.machine.reading bucket first)
      (asm.machine.reading bucket last) (Windows.start pos) (Windows.stop pos) := by
  let active := fun pt => {bucket | asm.machine.Active pt bucket}
  have hn : active first ∪ active last ≠ univ := by
    intro he
    have hh := (ncard_union_le (active first) (active last)).trans
      (Nat.add_le_add (asm.active_bound idx hf (Or.inl ht)) (asm.active_bound idx hl (Or.inr hu)))
    rw [he] at hh
    change (univ : Set (Fin buckets)).ncard ≤ _ at hh
    simp only [ncard_univ, Nat.card_fin] at hh
    nlinarith
  obtain ⟨bucket, hbucket⟩ := (ne_univ_iff_exists_notMem _).mp hn
  have hleft := (sch.contained idx bucket).1.trans (sch.phase idx bucket).early
  have hright := (sch.phase idx bucket).late.trans (sch.contained idx bucket).2
  have he := asm.phase_value idx bucket false (time := first.1) (by rw [ht]; exact ⟨le_rfl, hleft.le⟩)
  have he' := asm.phase_value idx bucket true (time := last.1) (by rw [hu]; exact ⟨hright.le, le_rfl⟩)
  have hl' := asm.machine.inactive_reading asm.floor_bounds large hf
    (by rw [ht]; exact ⟨(ep.positive idx).le, ((ep.width idx).trans (ep.interior idx)).le⟩)
    (fun hh => hbucket (Or.inl hh))
  have hr' := asm.machine.inactive_reading asm.floor_bounds large hl
    (by rw [hu]; exact ⟨((ep.positive idx).trans (ep.width idx)).le, (ep.interior idx).le⟩)
    (fun hh => hbucket (Or.inr hh))
  rw [he, abs_le] at hl'
  rw [he', abs_le] at hr'
  simp only [Bool.false_eq_true, ↓reduceIte] at hl' hr'
  refine ⟨bucket, fun pos => ⟨(min_le_left _ _).trans ?_, le_trans ?_ (le_max_right _ _)⟩⟩
  · linarith [Windows.start_gt pos, hl'.2]
  · linarith [Windows.stop_lt pos, hr'.1]

def driver (hc : clock.prog.Large limit) (hr : res.prog.Large limit)
    (hb : 4 * labels * res.size < buckets)
    (bc : CrossingBound (clock.region limit) 0 1 (2 * cost + 1))
    (br : CrossingBound (res.region limit) 0 1 (2 * cost + 1)) :
    Driver (asm.machine.region limit) (ep.left idx) (ep.right idx) buckets windows cost where
  phase := sch.phase idx
  contained := sch.contained idx
  read := asm.machine.reading
  continuous := asm.machine.continuous_reading
  work := Windows.work asm.lower.countPos
  anchors _ hf _ hl ht hu := asm.anchors idx hc hb hf hl ht hu
  early bucket pos := asm.upper_transfer idx bucket false hc bc pos
  late bucket pos := asm.upper_transfer idx bucket true hc bc pos
  band bucket pos := asm.lower_transfer idx bucket hr br pos

end Assembly
end OAI.Geometry.Hirsch
