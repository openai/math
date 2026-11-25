import OAI.Geometry.Hirsch.ResourceTransfer

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch.Machine

variable (mach : Machine) {pt : mach.Point} {bucket : mach.Bucket} {side : Bool} {limit : ℕ}

def Free (pt : mach.Point) (bucket : mach.Bucket) (side : Bool) : Prop :=
  ∀ idx, mach.floor bucket side pt.1 < mach.clocks bucket pt.2 side idx

theorem clock_variation (hp : pt ∈ mach.block.system.body) (free : mach.Free pt bucket side)
    {dir : Vec mach.clock.prog.Coord}
    (hd : mach.Active pt bucket → dir ∈ ((mach.cp.clock side).slice 0).directions
      ((mach.cp.clock side).system.active (mach.clockImage bucket side pt))) :
    mach.embed (some (bucket, side)) dir ∈ (mach.block.slice 0).directions (mach.block.system.active pt) := by
  apply (System.mem_directions _).mpr
  rintro (row | ⟨other, tag, piece, idx⟩ | act) hr
  · change mach.sched.block.coeff row.val (mach.proj none (mach.embed (some (bucket, side)) dir)) = 0
    rw [show mach.proj none (mach.embed (some (bucket, side)) dir) = 0 from
      Package.project_embed_ne _ (by simp) _, map_zero]
  · have hn : some (other, tag) ≠ some (bucket, side) := by
      intro he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
      have hz := (mach.block.tight pt _).mp hr
      change mach.clocks other pt.2 tag idx - (mach.slope other tag piece * pt.1 +
        mach.offset other tag piece) = 0 at hz
      exact (free idx).not_ge ((sub_eq_zero.mp hz).le.trans
        (le_peak (fun pos => mach.slope other tag pos * pt.1 + mach.offset other tag pos) piece))
    exact congrFun (Package.project_embed_ne mach.parts hn dir) idx
  · change mach.normal act (mach.embed (some (bucket, side)) dir) = 0
    rw [normal_clock]
    split
    · rename_i he
      cases hh : act.2.1.side side with
      | none => simp
      | some row =>
        have ha := (mach.of_tight hp hr).1.1 side
        rw [hh, he, mach.cp.clock_tight] at ha
        have hz := (System.mem_directions _).mp (hd ⟨act, hr, he⟩) row ha
        exact mul_eq_zero_of_right _ hz
    · rfl

theorem clock_transfer (large : mach.clock.prog.Large limit) (hp : pt ∈ mach.region limit)
    (free : mach.Free pt bucket side) :
    mach.Active pt bucket ∧ mach.clockImage bucket side pt ∈
      (mach.cp.clock side).admissible mach.clock.prog.viable limit := by
  obtain ⟨hf, usable, hv, hs, hd⟩ := hp
  let slot := some (bucket, side)
  let part := mach.insertCoord slot ⁻¹' usable
  let big := mach.block.nullspace (mach.block.system.active pt) usable
  have hact : mach.Active pt bucket := by
    by_contra hn
    have hh : finrank ℝ (supported part) ≤ finrank ℝ big :=
      mach.dim_embed (slot := slot) (fun dir hdir =>
        ⟨mach.embed_supported hdir, mach.clock_variation hf free (fun ha => (hn ha).elim)⟩)
    rw [finrank_supported] at hh
    exact (large part (hv slot)).not_ge (hh.trans hd)
  refine ⟨hact, (mach.cp.clockTune side).image_feasible _ _, part, hv slot, ?_, ?_⟩
  · intro row hr idx hi
    obtain ⟨act, ht, he⟩ := hact
    have ha := (mach.of_tight hf ht).1
    subst bucket
    obtain ⟨tr, htr, hside⟩ := mach.cp.active_of_clock ⟨act.2.1, ha⟩ hr
    obtain ⟨pick, ht'⟩ := mach.tight_of_active hf htr
    exact hs _ ht' ((mach.support_clock _ _ _ _).mpr ⟨rfl, row, hside, hi⟩)
  · apply le_trans _ hd
    exact mach.dim_embed (slot := slot) (fun dir hdir =>
      ⟨mach.embed_supported hdir.1, mach.clock_variation hf free (fun _ => hdir.2)⟩)

theorem time_bound (floors : mach.Floors) (hp : pt ∈ mach.block.system.body)
    (hx : pt.1 ∈ Icc (0 : ℝ) 1) (bucket : mach.Bucket) : |mach.reading bucket pt| ≤ mach.cp.cap :=
  mach.cp.time_bound (fun side idx => (floors bucket side _ hx).1.trans (mach.floor_le hp _ _ idx))

theorem lower (floors : mach.Floors) (hp : pt ∈ mach.block.system.body)
    (hx : pt.1 ∈ Icc (0 : ℝ) 1) (bucket : mach.Bucket) (side : Bool) :
    mach.floor bucket side pt.1 - 1/32 ≤ mach.cp.read (mach.clocks bucket pt.2) side :=
  (mach.cp.clockTune side).lower (mach.time_bound floors hp hx bucket)
    (mach.floor_le hp bucket side) (floors bucket side _ hx).2

theorem upper (floors : mach.Floors) (hp : pt ∈ mach.block.system.body)
    (hx : pt.1 ∈ Icc (0 : ℝ) 1) (hn : ¬mach.Free pt bucket side) :
    mach.cp.read (mach.clocks bucket pt.2) side ≤ mach.floor bucket side pt.1 + 1/32 := by
  unfold Free at hn
  push Not at hn
  obtain ⟨idx, hh⟩ := hn
  exact (mach.cp.clockTune side).upper_of_attained (mach.time_bound floors hp hx bucket)
    ⟨idx, le_antisymm hh (mach.floor_le hp _ _ _)⟩

def phaseValue (bucket : mach.Bucket) (time : ℝ) :=
  mach.floor bucket false time - mach.floor bucket true time

theorem inactive_reading (floors : mach.Floors) (large : mach.clock.prog.Large limit)
    (hp : pt ∈ mach.region limit) (hx : pt.1 ∈ Icc (0 : ℝ) 1) (hn : ¬mach.Active pt bucket) :
    |mach.reading bucket pt - mach.phaseValue bucket pt.1| ≤ 1/16 := by
  have hl := mach.lower floors hp.1 hx bucket
  have hu := fun side => mach.upper floors hp.1 hx
    (show ¬mach.Free pt bucket side from fun hh => hn (mach.clock_transfer large hp hh).1)
  rw [reading, mach.cp.time_eq, phaseValue, abs_le]
  constructor <;> linarith [hl true, hl false, hu true, hu false]

theorem free_of_phase (floors : mach.Floors) (hp : pt ∈ mach.block.system.body)
    (hx : pt.1 ∈ Icc (0 : ℝ) 1) (hr : mach.reading bucket pt ∈ Icc (1/4) (3/4))
    (he : mach.phaseValue bucket pt.1 = if side then 1 else 0) : mach.Free pt bucket side := by
  by_contra hn
  have hl := mach.lower floors hp hx bucket (!side)
  have hu := mach.upper floors hp hx hn
  rw [reading, mach.cp.time_eq] at hr
  cases side <;> simp [phaseValue] at he hl <;> linarith [hr.1, hr.2]

end OAI.Geometry.Hirsch.Machine
