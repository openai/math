import OAI.Geometry.Hirsch.ClockTransfer
import OAI.Geometry.Hirsch.Windows

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

def avg {Space : Type} [AddCommGroup Space] [Module ℝ Space] (first last : Space) :=
  (1/2 : ℝ) • (first + last)

theorem avg_mem {Space : Type} [AddCommGroup Space] [Module ℝ Space] (first last : Space) :
    avg first last ∈ openSegment ℝ first last :=
  ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, (smul_add ..).symm⟩

def ConcaveMid {Coord : Type} (first mid last : Timed Coord) : Prop :=
  mid.1 = (first.1 + last.1) / 2 ∧ avg first.2 last.2 ≤ mid.2

theorem Placement.decode_mid {Coord Index : Type} (place : Placement Index) (bound : ℝ) (idx : Index)
    {first mid last : Timed Coord} (hm : ConcaveMid first mid last) :
    ConcaveMid (place.decode bound idx first) (place.decode bound idx mid) (place.decode bound idx last) := by
  obtain ⟨ht, hv⟩ := hm
  have hh : place.shift bound idx mid.1 =
      (place.shift bound idx first.1 + place.shift bound idx last.1) / 2 := by
    rw [ht]; unfold shift tangent axis; ring
  constructor
  · simp only [decode, localTime, axis, ht]; ring
  · intro coord
    specialize hv coord
    simp only [avg, decode, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, hh] at *
    linarith

namespace Machine

variable (mach : Machine) {first last : mach.Point} {bucket : mach.Bucket}

theorem readings_mid (hf : first ∈ mach.block.system.body) (hl : last ∈ mach.block.system.body)
    (ha : mach.Active (avg first last) bucket) :
    mach.reading bucket (avg first last) = (mach.reading bucket first + mach.reading bucket last) / 2 ∧
    ∀ side, mach.cp.read (mach.clocks bucket (avg first last).2) side =
      (mach.cp.read (mach.clocks bucket first.2) side + mach.cp.read (mach.clocks bucket last.2) side) / 2 := by
  obtain ⟨act, ht, rfl⟩ := ha
  have hm := avg_mem first last
  have hp := mach.block.system.convex_body.segment_subset hf hl (openSegment_subset_segment _ _ _ hm)
  have he := (System.active_openSegment hf hl hm).subset ht
  exact mach.cp.affine_read act.2.1 (by simp [avg, map_smul, map_add])
    (mach.of_tight hf he.1).1.1 (mach.of_tight hp ht).1.1 (mach.of_tight hl he.2).1.1

theorem clock_mid (hf : first ∈ mach.block.system.body) (hl : last ∈ mach.block.system.body)
    (ha : mach.Active (avg first last) bucket) (side : Bool) :
    ConcaveMid (mach.clockImage bucket side first) (mach.clockImage bucket side (avg first last))
      (mach.clockImage bucket side last) := by
  obtain ⟨ht, hr⟩ := mach.readings_mid hf hl ha
  refine ⟨ht, fun idx => le_of_eq ?_⟩
  simp only [clockImage, Coupler.clockPt, Tuned.image, hr, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  simp only [avg, Prod.smul_snd, Prod.snd_add, map_smul, map_add, Pi.smul_apply, Pi.sub_apply,
    Pi.add_apply, smul_eq_mul]
  ring

theorem resource_mid (hf : first ∈ mach.block.system.body) (hl : last ∈ mach.block.system.body)
    (ha : mach.Active (avg first last) bucket) :
    ConcaveMid (mach.resource bucket first) (mach.resource bucket (avg first last))
      (mach.resource bucket last) := by
  obtain ⟨ht, hr⟩ := mach.readings_mid hf hl ha
  refine ⟨ht, fun idx => ?_⟩
  have he : mach.schedPt (avg first last) = avg (mach.schedPt first) (mach.schedPt last) := by
    simp [avg]
  have hh := mach.paint.minimum_concave bucket (mach.schedPt first) (mach.schedPt last) idx
  change _ ≤ mach.paint.minimum bucket (avg _ _) idx at hh
  rw [← he] at hh
  have hv := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh mach.positive.le)
    (inv_nonneg.mpr mach.cp.resTune.positive.le)
  simp only [resource, Coupler.resPt, Tuned.image, hr, minimum, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  simp only [avg, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] at hv ⊢
  linarith

end Machine

structure Overlay (pkg : Package) (count : ℕ) (kind : Kind) (cap : ℝ) where
  countPos : 0 < count
  bound : ℝ
  positive : 0 < bound
  bounded : (Windows.place countPos kind).Bounded pkg.block.normalize cap bound

namespace Overlay

variable {pkg : Package} {count : ℕ} {kind : Kind} {cap : ℝ}

def make (pkg : Package) (hc : 0 < count) (kind : Kind) (cap : ℝ) : Overlay pkg count kind cap :=
  let hh := (Windows.place hc kind).bounded pkg.block.normalize cap
  ⟨hc, hh.choose, hh.choose_spec.1, hh.choose_spec.2⟩

variable (over : Overlay pkg count kind cap)

abbrev Rows (pkg : Package) (count : ℕ) := Placement.Rows (Fin count) pkg.prog.Coord pkg.Row

def block : Blocking pkg.prog.Coord (Rows pkg count) :=
  letI : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp over.countPos
  (Windows.place over.countPos kind).overlay pkg.block.normalize over.bound

theorem unit : over.block.UnitWeights := by
  let : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp over.countPos
  exact Placement.unit _ _ pkg.block.unit_normalize _

theorem influence {pt : Timed pkg.prog.Coord} (ht : |pt.1| ≤ cap)
    (hp : pt ∈ over.block.system.body) {idx row} (ha : Sum.inl (idx, row) ∈ over.block.system.active pt) :
    pt.1 ∈ (Windows.place over.countPos kind).influence idx := by
  let : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp over.countPos
  exact Placement.copy_influence _ _ pkg.block.unit_normalize over.positive over.bounded ht hp ha

theorem transfer {Coord : Type} [Fintype Coord] {region : Set (Timed Coord)}
    (read : Timed Coord → ℝ) (hc : Continuous read) (image : Timed Coord → Timed pkg.prog.Coord)
    (htime : ∀ pt, (image pt).1 = read pt) {phase : Set ℝ} {limit cost : ℕ}
    (good : ∀ pt ∈ region, pt.1 ∈ phase → read pt ∈ Icc (1/4) (3/4) →
      |read pt| ≤ cap ∧ image pt ∈ over.block.admissible pkg.prog.viable limit)
    (mid : ∀ first ∈ region, ∀ last ∈ region, avg first last ∈ region →
      (avg first last).1 ∈ phase → read (avg first last) ∈ Icc (1/4) (3/4) →
      ConcaveMid (image first) (image (avg first last)) (image last))
    (bound : CrossingBound (pkg.region limit) 0 1 (2 * cost + 1)) (idx : Fin count) :
    Transfer region read phase (Windows.start idx) (Windows.stop idx) cost := by
  let : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp over.countPos
  let place := Windows.place over.countPos kind
  let decode := fun pt => place.decode over.bound idx (image pt)
  obtain ⟨hl, hw, hr⟩ := Windows.bounds over.countPos kind idx
  have hsub := Icc_subset_Icc ((Windows.start_gt idx).le.trans hl) (hr.trans (Windows.stop_lt idx).le)
  refine transfer_of_chords hc decode hw hl hr ?_ ?_ ?_ bound
  · intro pt _ he
    change place.localTime idx (image pt).1 = 0
    rw [htime, he]; exact Windows.local_left ..
  · intro pt _ he
    change place.localTime idx (image pt).1 = 1
    rw [htime, he]; exact Windows.local_right ..
  intro first last hh
  have hadm : ∀ pt ∈ segment ℝ first last, decode pt ∈ pkg.region limit := by
    intro pt hp
    obtain ⟨hf, hphase, hwin⟩ := hh pt hp
    obtain ⟨ht, ha⟩ := good pt hf hphase (hsub hwin)
    rw [Package.region, ← pkg.block.admissible_normalize]
    apply place.decode_admissible _ pkg.block.unit_normalize over.positive over.bounded _ _ ha
    · rwa [htime]
    · rw [htime]; exact Windows.in_window _ _ _ hwin
  have hf := left_mem_segment ℝ first last
  have hl := right_mem_segment ℝ first last
  have hm := openSegment_subset_segment _ _ _ (avg_mem first last)
  obtain ⟨hp, hx, hw⟩ := hh _ hm
  have hmid := place.decode_mid over.bound idx (mid _ (hh _ hf).1 _ (hh _ hl).1 hp hx (hsub hw))
  obtain ⟨hs, ht⟩ := pkg.block.two_chords (hadm _ hf) (hadm _ hm) (hadm _ hl) hmid.1 hmid.2
  exact ⟨2, le_rfl, Links.cons hs (Links.cons ht (Links.nil _))⟩

end Overlay
end OAI.Geometry.Hirsch
