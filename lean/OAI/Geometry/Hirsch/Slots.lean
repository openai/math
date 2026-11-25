import OAI.Geometry.Hirsch.Actions

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch.Machine

variable (mach : Machine)

def insertCoord (slot : mach.Slot) (idx : (mach.parts slot).prog.Coord) : mach.Coord := ⟨slot, idx⟩

abbrev proj (slot : mach.Slot) := Package.project mach.parts slot
abbrev embed (slot : mach.Slot) := Package.embed mach.parts slot

theorem embed_inj (slot : mach.Slot) : Function.Injective (mach.embed slot) :=
  Function.LeftInverse.injective (Package.project_embed mach.parts slot)

theorem embed_supported {usable : Set mach.Coord} {slot : mach.Slot} {dir}
    (hd : dir ∈ supported (mach.insertCoord slot ⁻¹' usable)) :
    mach.embed slot dir ∈ supported usable := by
  rintro ⟨other, idx⟩ hn
  change Package.project mach.parts other (Package.embed mach.parts slot dir) idx = 0
  by_cases he : other = slot
  · subst other
    rw [Package.project_embed]
    exact hd idx hn
  · rw [Package.project_embed_ne _ he]; rfl

theorem dim_embed {slot : mach.Slot} {small : Submodule ℝ (Vec (mach.parts slot).prog.Coord)}
    {big : Submodule ℝ (Vec mach.Coord)} (hh : ∀ dir ∈ small, mach.embed slot dir ∈ big) :
    finrank ℝ small ≤ finrank ℝ big := by
  apply LinearMap.finrank_le_finrank_of_injective (f := (mach.embed slot).restrict hh)
  exact fun _ _ he => Subtype.ext (mach.embed_inj slot (congrArg Subtype.val he))

theorem clockMap_eq (act : mach.Action) (side : Bool) (dir : Vec mach.Coord) :
    mach.clockMap act side dir = (act.2.1.side side).elim 0
      (fun row => (mach.cp.clock side).coeff row (mach.proj (some (act.1, side)) dir)) := by
  unfold clockMap
  cases act.2.1.side side <;> rfl

theorem clockMap_other (act : mach.Action) (side : Bool) {slot} (hn : some (act.1, side) ≠ slot)
    (dir : Vec (mach.parts slot).prog.Coord) : mach.clockMap act side (mach.embed slot dir) = 0 := by
  rw [clockMap_eq, show mach.proj _ (mach.embed slot dir) = 0 from Package.project_embed_ne _ hn dir]
  cases act.2.1.side side <;> simp

theorem chosenMap_eq (act : mach.Action) (dir : Vec mach.Coord) :
    mach.chosenMap act dir = fun idx => mach.sched.block.coeff (mach.chosen act idx) (mach.proj none dir) := rfl

theorem normal_sched (act : mach.Action) (dir : Vec mach.sched.prog.Coord) :
    mach.normal act (mach.embed none dir) = mach.scale * mach.cp.res.coeff act.2.1.2.2
      (fun idx => mach.sched.block.coeff (mach.chosen act idx) dir) := by
  have hz := fun side => mach.clockMap_other act side (slot := none) (by simp) dir
  have he : mach.proj none (mach.embed none dir) = dir := Package.project_embed _ _ _
  simp [normal, hz, chosenMap_eq, he]

theorem normal_clock (act : mach.Action) (bucket : mach.Bucket) (side : Bool)
    (dir : Vec mach.clock.prog.Coord) :
    mach.normal act (mach.embed (some (bucket, side)) dir) =
      if act.1 = bucket then mach.cp.multiplier act.2.1 side *
        (act.2.1.side side).elim 0 (fun row => (mach.cp.clock side).coeff row dir) else 0 := by
  let slot := some (bucket, side)
  have hn : mach.proj none (mach.embed slot dir) = 0 := Package.project_embed_ne _ (by simp [slot]) _
  have hz : mach.chosenMap act (mach.embed slot dir) = 0 := by
    rw [chosenMap_eq, hn]; ext; simp
  have he := mach.clockMap_other act (!side) (slot := slot) (by cases side <;> simp [slot]) dir
  have hh : mach.normal act (mach.embed slot dir) =
      mach.cp.multiplier act.2.1 side * mach.clockMap act side (mach.embed slot dir) := by
    cases side <;> simp_all [normal]
  rw [hh]
  split
  · rename_i h
    subst bucket
    rw [clockMap_eq, show mach.proj slot (mach.embed slot dir) = dir from Package.project_embed _ _ _]
  · rename_i h
    rw [mach.clockMap_other act side (slot := slot) (by simp [slot, h]), mul_zero]

def single {Index : Type} (idx : Index) : Vec Index := by
  classical exact Pi.single idx 1

theorem embed_single (slot : mach.Slot) (idx : (mach.parts slot).prog.Coord) :
    mach.embed slot (single idx) = single (mach.insertCoord slot idx) := by
  classical
  ext ⟨other, coord⟩
  change Package.project mach.parts other (Package.embed mach.parts slot (single idx)) coord = _
  by_cases he : other = slot
  · subst other
    rw [Package.project_embed]
    simp [single, insertCoord, Pi.single_apply]
  · rw [Package.project_embed_ne _ he]
    simp [single, insertCoord, he]

theorem support_sched (act : mach.Action) (idx : mach.sched.prog.Coord) :
    mach.insertCoord none idx ∈ mach.block.support (.inr (.inr act)) ↔
      ∃ coord ∈ mach.cp.res.support act.2.1.2.2, idx ∈ mach.sched.block.support (mach.chosen act coord) := by
  change mach.normal act (single (mach.insertCoord none idx)) ≠ 0 ↔ _
  rw [← embed_single, normal_sched, mul_ne_zero_iff_left mach.positive.ne']
  let vec := fun coord => mach.sched.block.weight (mach.chosen act coord) idx
  change mach.cp.res.coeff act.2.1.2.2 vec ≠ 0 ↔ _
  constructor
  · intro he
    by_contra! hn
    apply he
    rw [← map_zero (mach.cp.res.coeff _)]
    exact mach.cp.res.local_eq _ (fun coord hc => not_ne_iff.mp (hn coord hc))
  · rintro ⟨coord, hc, hi⟩ he
    have hn : 0 ≤ vec := fun coord => mach.sched.block.weight_nonneg _ _
    have hz := mach.cp.res.eqOn_of_coeff_eq _ hn ((map_zero _).trans he.symm) hc
    exact hi hz.symm

theorem support_clock (act : mach.Action) (bucket : mach.Bucket) (side : Bool)
    (idx : mach.clock.prog.Coord) :
    mach.insertCoord (some (bucket, side)) idx ∈ mach.block.support (.inr (.inr act)) ↔
      act.1 = bucket ∧ ∃ row, act.2.1.side side = some row ∧ idx ∈ (mach.cp.clock side).support row := by
  change mach.normal act (single (mach.insertCoord (some (bucket, side)) idx)) ≠ 0 ↔ _
  rw [← embed_single, normal_clock]
  by_cases he : act.1 = bucket
  · cases act.2.1.side side <;> simp [he, Blocking.support, single, (mach.cp.mult_pos _ _).ne']
  · simp [he]

theorem selected_retained {pt : mach.Point} {usable : Set mach.Coord}
    (hs : ∀ row ∈ mach.block.system.active pt, mach.block.support row ⊆ usable) :
    mach.selected pt ⊆ mach.sched.block.retained (mach.insertCoord none ⁻¹' usable) := by
  rintro row (⟨hn, hz⟩ | ⟨act, ht, idx, hi, rfl⟩) coord hc
  · let ordinary : mach.Row := .inl ⟨row, hn⟩
    apply hs ordinary ((mach.block.tight _ _).mpr hz)
    change mach.insertCoord none coord ∈ (Package.combined mach.parts).support ⟨none, row⟩
    rw [Package.support_combined]
    exact ⟨coord, hc, rfl⟩
  · exact hs _ ht ((mach.support_sched act coord).mpr ⟨idx, hi, hc⟩)

end OAI.Geometry.Hirsch.Machine
