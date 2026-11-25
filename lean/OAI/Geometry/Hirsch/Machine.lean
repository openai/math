import OAI.Geometry.Hirsch.RedSlacks

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

structure Machine where
  sched : Package
  clock : Package
  client : Program
  buckets : ℕ
  paint : Coloring sched client buckets
  ClockRow : Type
  ResRow : Type
  [clockFinite : Fintype ClockRow]
  [resFinite : Fintype ResRow]
  cp : Coupler clock.prog.Coord ClockRow client.Coord ResRow
  Piece : Type
  [pieceFinite : Fintype Piece]
  [pieceNonempty : Nonempty Piece]
  slope : Fin buckets → Bool → Piece → ℝ
  offset : Fin buckets → Bool → Piece → ℝ
  scale : ℝ
  positive : 0 < scale

attribute [instance] Machine.clockFinite Machine.resFinite Machine.pieceFinite Machine.pieceNonempty

namespace Machine

variable (mach : Machine)

abbrev Bucket := Fin mach.buckets
abbrev Slot := Option (mach.Bucket × Bool)
abbrev parts (slot : mach.Slot) : Package := Option.rec mach.sched (fun _ => mach.clock) slot
abbrev prog := Program.join fun slot => (mach.parts slot).prog
abbrev Coord := Package.Coords mach.parts
abbrev Point := Timed mach.Coord
abbrev Trip := Triple mach.ClockRow mach.ResRow
abbrev Picks (bucket : mach.Bucket) (tr : mach.Trip) :=
  mach.paint.Pick bucket (mach.cp.res.support tr.2.2)
abbrev Action := Σ bucket, Σ tr, mach.Picks bucket tr
abbrev Ordinary := {row : mach.sched.Row // mach.paint.color row = none}
abbrev FloorRow := mach.Bucket × Bool × mach.Piece × mach.clock.prog.Coord
abbrev Row := mach.Ordinary ⊕ mach.FloorRow ⊕ mach.Action

def schedPt : mach.Point →ₗ[ℝ] Timed mach.sched.prog.Coord :=
  Package.projectPoint mach.parts none

def clocks (bucket : mach.Bucket) : Vec mach.Coord →ₗ[ℝ] Coupler.Clocks mach.clock.prog.Coord :=
  LinearMap.pi fun side => Package.project mach.parts (some (bucket, side))

def minimum (bucket : mach.Bucket) (pt : mach.Point) : Vec mach.client.Coord :=
  mach.scale • mach.paint.minimum bucket (mach.schedPt pt)

def floor (bucket : mach.Bucket) (side : Bool) (time : ℝ) :=
  peak (fun piece => mach.slope bucket side piece * time + mach.offset bucket side piece)

def chosen (act : mach.Action) (idx : mach.client.Coord) : mach.sched.Row :=
  mach.paint.picked act.1 act.2.2 idx

theorem chosen_group (act : mach.Action) (idx : mach.client.Coord) :
    mach.chosen act idx ∈ mach.paint.group act.1 idx := (mach.paint.picked _ _ _).property

def chosenVec (act : mach.Action) (pt : mach.Point) : Vec mach.client.Coord :=
  fun idx => mach.scale * mach.sched.block.slack (mach.chosen act idx) (mach.schedPt pt)

def chosenMap (act : mach.Action) : Vec mach.Coord →ₗ[ℝ] Vec mach.client.Coord :=
  LinearMap.pi fun idx => (Package.combined mach.parts).coeff ⟨none, mach.chosen act idx⟩

def clockMap (act : mach.Action) (side : Bool) : Vec mach.Coord →ₗ[ℝ] ℝ :=
  (act.2.1.side side).elim 0 fun row =>
    ((mach.cp.clock side).coeff row).comp (Package.project mach.parts (some (act.1, side)))

def normal (act : mach.Action) : Vec mach.Coord →ₗ[ℝ] ℝ :=
  mach.cp.multiplier act.2.1 false • mach.clockMap act false +
    mach.cp.multiplier act.2.1 true • mach.clockMap act true +
    mach.scale • (mach.cp.res.coeff act.2.1.2.2).comp (mach.chosenMap act)

def actSlope (act : mach.Action) :=
  mach.scale * mach.cp.res.coeff act.2.1.2.2 (mach.sched.block.slope ∘ mach.chosen act)

def actOffset (act : mach.Action) :=
  mach.scale * mach.cp.res.coeff act.2.1.2.2 (mach.sched.block.offset ∘ mach.chosen act) -
    mach.cp.combined act.2.1 0 0

theorem clockMap_mono (act : mach.Action) (side : Bool) : Monotone (mach.clockMap act side) := by
  unfold clockMap
  cases act.2.1.side side with
  | none => exact monotone_const
  | some row => exact fun _ _ hh => (mach.cp.clock side).monotone row (fun _ => hh _)

theorem chosenMap_mono (act : mach.Action) : Monotone (mach.chosenMap act) :=
  fun _ _ hh _ => (Package.combined mach.parts).monotone _ hh

theorem normal_mono (act : mach.Action) : Monotone (mach.normal act) := by
  intro first last hh
  have hc := fun side => mul_le_mul_of_nonneg_left (mach.clockMap_mono act side hh)
    (mach.cp.mult_pos act.2.1 side).le
  exact add_le_add (add_le_add (hc false) (hc true))
    (mul_le_mul_of_nonneg_left (mach.cp.res.monotone _ (mach.chosenMap_mono act hh)) mach.positive.le)

theorem normal_pos (act : mach.Action) : 0 < mach.normal act 1 := by
  have hc : ∀ side, 0 ≤ mach.cp.multiplier act.2.1 side * mach.clockMap act side 1 := by
    intro side
    refine mul_nonneg (mach.cp.mult_pos _ _).le ?_
    simpa using mach.clockMap_mono act side (show (0 : Vec mach.Coord) ≤ 1 from zero_le_one)
  exact add_pos_of_nonneg_of_pos (add_nonneg (hc false) (hc true))
    (mul_pos mach.positive (mach.cp.res.strict_pos _ (fun _ => (Package.combined mach.parts).positive _)))

def block : Blocking mach.Coord mach.Row where
  coeff
    | .inl row => (Package.combined mach.parts).coeff ⟨none, row.val⟩
    | .inr (.inl (bucket, side, _, idx)) => LinearMap.proj ⟨some (bucket, side), idx⟩
    | .inr (.inr act) => mach.normal act
  slope
    | .inl row => mach.sched.block.slope row.val
    | .inr (.inl (bucket, side, piece, _)) => mach.slope bucket side piece
    | .inr (.inr act) => mach.actSlope act
  offset
    | .inl row => mach.sched.block.offset row.val
    | .inr (.inl (bucket, side, piece, _)) => mach.offset bucket side piece
    | .inr (.inr act) => mach.actOffset act
  monotone := by
    rintro (row | ⟨bucket, side, piece, idx⟩ | act)
    · exact (Package.combined mach.parts).monotone _
    · exact fun _ _ hh => hh _
    · exact mach.normal_mono act
  positive := by
    rintro (row | ⟨bucket, side, piece, idx⟩ | act)
    · exact (Package.combined mach.parts).positive _
    · exact zero_lt_one
    · exact mach.normal_pos act
  individual := by
    rintro ⟨_ | ⟨bucket, side⟩, idx⟩
    · obtain ⟨row, weight, hr, hw, he⟩ := mach.paint.ordinary idx
      refine ⟨.inl ⟨row, hr⟩, weight, hw, ?_⟩
      change (mach.sched.block.coeff row).comp _ = _
      rw [he]; rfl
    · exact ⟨.inr (.inl (bucket, side, Classical.arbitrary _, idx)), 1, one_pos, (one_smul _ _).symm⟩

theorem intercept_eq (act : mach.Action) (side : Bool) (vec : Vec mach.Coord) :
    mach.cp.intercept act.2.1 (mach.clocks act.1 vec) side =
      mach.clockMap act side vec + mach.cp.intercept act.2.1 0 side := by
  unfold Coupler.intercept Coupler.upper Tuned.upper clockMap
  dsimp only
  cases act.2.1.side side with
  | none => simp
  | some row => simp [clocks, sub_eq_add_neg]

theorem chosen_eq (act : mach.Action) (pt : mach.Point) :
    mach.chosenVec act pt = mach.scale • (mach.chosenMap act pt.2 -
      (pt.1 • (mach.sched.block.slope ∘ mach.chosen act) + mach.sched.block.offset ∘ mach.chosen act)) := by
  funext idx
  change mach.scale * (_ - (_ * pt.1 + _)) = mach.scale * (_ - (pt.1 * _ + _))
  rw [mul_comm _ pt.1]
  rfl

theorem slack_eq (act : mach.Action) (pt : mach.Point) :
    mach.block.slack (.inr (.inr act)) pt =
      mach.cp.combined act.2.1 (mach.clocks act.1 pt.2) (mach.chosenVec act pt) := by
  change mach.normal act pt.2 - (mach.actSlope act * pt.1 + mach.actOffset act) = _
  unfold normal actSlope actOffset Coupler.combined
  rw [intercept_eq, intercept_eq, chosen_eq]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_add,
    map_sub, map_smul, map_zero, smul_eq_mul]
  ring

end Machine
end OAI.Geometry.Hirsch
