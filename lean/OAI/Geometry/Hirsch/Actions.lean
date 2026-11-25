import OAI.Geometry.Hirsch.Machine

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Machine

variable (mach : Machine) (pt : mach.Point)

def reading (bucket : mach.Bucket) (pt : mach.Point) := mach.cp.time (mach.clocks bucket pt.2)

def resource (bucket : mach.Bucket) (pt : mach.Point) :=
  mach.cp.resPt (mach.clocks bucket pt.2) (mach.minimum bucket pt)

def clockImage (bucket : mach.Bucket) (side : Bool) (pt : mach.Point) :=
  mach.cp.clockPt (mach.clocks bucket pt.2) side

def Tight (act : mach.Action) := Sum.inr (.inr act) ∈ mach.block.system.active pt

def Active (bucket : mach.Bucket) := ∃ act, mach.Tight pt act ∧ act.1 = bucket

def selected : Set mach.sched.Row :=
  {row | (mach.paint.color row = none ∧ mach.sched.block.slack row (mach.schedPt pt) = 0) ∨
    ∃ act, mach.Tight pt act ∧ ∃ idx ∈ mach.cp.res.support act.2.1.2.2, mach.chosen act idx = row}

theorem continuous_reading (bucket : mach.Bucket) : Continuous (mach.reading bucket) :=
  mach.cp.continuous_time.comp ((mach.clocks bucket).continuous_of_finiteDimensional.comp continuous_snd)

theorem min_le_chosen (act : mach.Action) : mach.minimum act.1 pt ≤ mach.chosenVec act pt :=
  fun idx => mul_le_mul_of_nonneg_left (mach.paint.minimum_le _ _ (mach.chosen_group act idx))
    mach.positive.le

theorem tight_iff (act : mach.Action) :
    mach.Tight pt act ↔ mach.cp.combined act.2.1 (mach.clocks act.1 pt.2) (mach.chosenVec act pt) = 0 := by
  rw [Tight, Blocking.tight, slack_eq]

theorem minimizing_action (bucket : mach.Bucket) (tr : mach.Trip) :
    ∃ pick : mach.Picks bucket tr,
      mach.block.slack (.inr (.inr ⟨bucket, tr, pick⟩)) pt =
        mach.cp.combined tr (mach.clocks bucket pt.2) (mach.minimum bucket pt) := by
  obtain ⟨pick, hp⟩ := mach.paint.minimizing bucket (mach.cp.res.support tr.2.2) (mach.schedPt pt)
  refine ⟨pick, ?_⟩
  rw [slack_eq]
  unfold Coupler.combined
  have hh : mach.cp.res.coeff tr.2.2 (mach.chosenVec ⟨bucket, tr, pick⟩ pt) =
      mach.cp.res.coeff tr.2.2 (mach.minimum bucket pt) := by
    apply mach.cp.res.local_eq
    intro idx hi
    exact congrArg (mach.scale * ·) (hp idx hi)
  dsimp only
  rw [hh]

variable {pt}

theorem feasible_resource (hp : pt ∈ mach.block.system.body) (bucket : mach.Bucket) :
    mach.resource bucket pt ∈ mach.cp.res.system.body := by
  apply mach.cp.feasible_of_combined
  intro tr
  obtain ⟨pick, he⟩ := mach.minimizing_action pt bucket tr
  rw [← he]
  exact (mach.block.feasible pt).mp hp _

theorem floor_le (hp : pt ∈ mach.block.system.body) (bucket : mach.Bucket) (side : Bool)
    (idx : mach.clock.prog.Coord) : mach.floor bucket side pt.1 ≤ mach.clocks bucket pt.2 side idx := by
  obtain ⟨piece, he⟩ := peak_attained (fun piece => mach.slope bucket side piece * pt.1 +
    mach.offset bucket side piece)
  unfold floor
  rw [he]
  exact (mach.block.mem_slice pt).mpr hp (.inr (.inl (bucket, side, piece, idx)))

theorem of_tight (hp : pt ∈ mach.block.system.body) {act : mach.Action} (ht : mach.Tight pt act) :
    mach.cp.Active act.2.1 (mach.clocks act.1 pt.2) (mach.minimum act.1 pt) ∧
      EqOn (mach.minimum act.1 pt) (mach.chosenVec act pt) (mach.cp.res.support act.2.1.2.2) := by
  have hf := mach.feasible_resource hp act.1
  have hh := mach.cp.nonneg act.2.1 hf
  have hz := (mach.tight_iff pt act).mp ht
  have hm := mach.min_le_chosen pt act
  have hle := mach.cp.res.monotone act.2.1.2.2 hm
  have he : mach.cp.res.coeff act.2.1.2.2 (mach.minimum act.1 pt) =
      mach.cp.res.coeff act.2.1.2.2 (mach.chosenVec act pt) := by
    unfold Coupler.combined at hh hz
    linarith
  refine ⟨(mach.cp.zero_iff _ hf).mp ?_, mach.cp.res.eqOn_of_coeff_eq _ hm he⟩
  unfold Coupler.combined
  rw [he]
  exact hz

theorem tight_of_active (hp : pt ∈ mach.block.system.body) {bucket : mach.Bucket} {tr : mach.Trip}
    (ha : mach.cp.Active tr (mach.clocks bucket pt.2) (mach.minimum bucket pt)) :
    ∃ pick, mach.Tight pt ⟨bucket, tr, pick⟩ := by
  obtain ⟨pick, he⟩ := mach.minimizing_action pt bucket tr
  exact ⟨pick, (mach.block.tight _ _).mpr (he.trans ((mach.cp.zero_iff _ (mach.feasible_resource hp _)).mpr ha))⟩

theorem resource_selected (hp : pt ∈ mach.block.system.body) {bucket : mach.Bucket} {row}
    (hr : row ∈ mach.cp.res.system.active (mach.resource bucket pt)) :
    mach.cp.res.support row ⊆ mach.paint.represented bucket (mach.selected pt) := by
  obtain ⟨tr, ha, rfl⟩ := mach.cp.active_of_resource hr
  obtain ⟨pick, ht⟩ := mach.tight_of_active hp ha
  intro idx hi
  exact ⟨_, Or.inr ⟨_, ht, idx, hi, rfl⟩, mach.chosen_group ⟨bucket, tr, pick⟩ idx⟩

theorem active_iff {bucket : mach.Bucket} :
    mach.Active pt bucket ↔ bucket ∈ mach.paint.touched (mach.selected pt) := by
  constructor
  · rintro ⟨act, ht, rfl⟩
    obtain ⟨idx, hi⟩ := mach.cp.res.support_nonempty act.2.1.2.2
    exact ⟨idx, _, Or.inr ⟨act, ht, idx, hi, rfl⟩, mach.chosen_group act idx⟩
  · rintro ⟨idx, row, (⟨hn, _⟩ | ⟨act, ht, coord, _, rfl⟩), hr⟩
    · simp [Coloring.group, hn] at hr
    · exact ⟨act, ht, congrArg Prod.fst (Option.some.inj ((mach.chosen_group act coord).symm.trans hr))⟩

def Controlled (tol : ℝ) : Prop :=
  ∀ pt ∈ mach.block.system.body, pt.1 ∈ Icc (0 : ℝ) 1 →
    (∀ row, -tol < mach.sched.block.slack row (mach.schedPt pt)) ∧
      ∀ row ∈ mach.selected pt, mach.sched.block.slack row (mach.schedPt pt) < tol

def Floors : Prop := ∀ bucket side time, time ∈ Icc (0 : ℝ) 1 →
  mach.floor bucket side time ∈ Icc 1 mach.cp.cap

theorem controlled {bound tol : ℝ} (ht : 0 < tol) (hs : bound < mach.scale * tol)
    (hf : mach.Floors)
    (hb : ∀ vec slacks, (∀ side idx, 1 ≤ vec side idx) →
      mach.cp.resPt vec slacks ∈ mach.cp.res.system.body →
      (∀ idx, -bound ≤ slacks idx) ∧ ∀ row ∈ mach.cp.res.system.active (mach.cp.resPt vec slacks),
        ∀ idx ∈ mach.cp.res.support row, slacks idx ≤ bound) : mach.Controlled tol := by
  intro pt hp hx
  have hh := fun bucket => hb _ _ (fun side idx =>
    (hf bucket side _ hx).1.trans (mach.floor_le hp bucket side idx)) (mach.feasible_resource hp bucket)
  constructor
  · intro row
    cases he : mach.paint.color row with
    | none =>
      exact (neg_neg_of_pos ht).trans_le ((mach.block.feasible pt).mp hp (.inl ⟨row, he⟩))
    | some pair =>
      obtain ⟨bucket, idx⟩ := pair
      have hmin := (hh bucket).1 idx
      change -bound ≤ mach.scale * mach.paint.minimum bucket (mach.schedPt pt) idx at hmin
      apply lt_of_lt_of_le _ (mach.paint.minimum_le bucket _ he)
      apply lt_of_mul_lt_mul_left _ mach.positive.le
      linarith
  · rintro row (⟨_, he⟩ | ⟨act, ha, idx, hi, rfl⟩)
    · rwa [he]
    · obtain ⟨ha', he⟩ := mach.of_tight hp ha
      have hu := ((hh act.1).2 _ ha'.2 idx hi).trans_lt hs
      rw [he hi] at hu
      exact lt_of_mul_lt_mul_left hu mach.positive.le

end OAI.Geometry.Hirsch.Machine
