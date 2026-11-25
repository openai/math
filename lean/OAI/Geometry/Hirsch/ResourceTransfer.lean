import OAI.Geometry.Hirsch.Slots

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch.Machine

variable (mach : Machine) {pt : mach.Point} {bucket : mach.Bucket} {limit : ℕ}

def region (limit : ℕ) := mach.block.admissible mach.prog.viable limit

theorem variation_selected (hp : pt ∈ mach.block.system.body) {dir : Vec mach.client.Coord}
    (hd : dir ∈ (mach.cp.res.slice 0).directions (mach.cp.res.system.active (mach.resource bucket pt)))
    {delta : Vec mach.sched.prog.Coord}
    (he : ∀ row ∈ mach.selected pt, mach.sched.block.coeff row delta = mach.paint.variation bucket row dir) :
    mach.embed none delta ∈ (mach.block.slice 0).directions (mach.block.system.active pt) := by
  apply (System.mem_directions _).mpr
  rintro (row | ⟨other, side, piece, idx⟩ | act) hr
  · change mach.sched.block.coeff row.val (mach.proj none (mach.embed none delta)) = 0
    rw [show mach.proj none (mach.embed none delta) = delta from Package.project_embed ..]
    have hz : mach.sched.block.slack row.val (mach.schedPt pt) = 0 := (mach.block.tight _ _).mp hr
    rw [he _ (Or.inl ⟨row.property, hz⟩)]
    simp [Coloring.variation, row.property]
  · change mach.proj (some (other, side)) (mach.embed none delta) idx = 0
    exact congrFun (Package.project_embed_ne mach.parts (by simp : some (other, side) ≠ none) delta) idx
  · change mach.normal act (mach.embed none delta) = 0
    rw [normal_sched]
    apply mul_eq_zero_of_right
    let src := act.2.1.2.2
    have hv : ∀ idx ∈ mach.cp.res.support src,
        mach.sched.block.coeff (mach.chosen act idx) delta = if act.1 = bucket then dir idx else 0 := by
      intro idx hi
      rw [he _ (Or.inr ⟨act, hr, idx, hi, rfl⟩)]
      have hh : mach.paint.color (mach.chosen act idx) = some (act.1, idx) := mach.chosen_group act idx
      simp only [Coloring.variation, hh]
      split <;> rfl
    by_cases hb : act.1 = bucket
    · have ht := (mach.of_tight hp hr).1.2
      change src ∈ mach.cp.res.system.active (mach.resource act.1 pt) at ht
      rw [hb] at ht
      exact (mach.cp.res.local_eq src (fun idx hi => by simpa [hb] using hv idx hi)).trans
        ((System.mem_directions _).mp hd src ht)
    · rw [← map_zero (mach.cp.res.coeff _)]
      exact mach.cp.res.local_eq src (fun idx hi => by simpa [hb] using hv idx hi)

theorem resource_transfer {tol : ℝ} (ht : 0 < tol) (controlled : mach.Controlled tol)
    (large : mach.client.Large limit) (hp : pt ∈ mach.region limit) (hx : pt.1 ∈ Icc (0 : ℝ) 1)
    (probe : mach.paint.Probe bucket pt.1 tol) :
    mach.Active pt bucket ∧ mach.resource bucket pt ∈ mach.cp.res.admissible mach.client.viable limit := by
  obtain ⟨hf, usable, hv, hs, hd⟩ := hp
  obtain ⟨hl, hu⟩ := controlled pt hf hx
  obtain ⟨requests, hviable, hreq, lift, hinj, he⟩ :=
    mach.paint.lift (pt := mach.schedPt pt) ht probe (hv none) (mach.selected pt)
      (mach.selected_retained hs) hl hu
  let small := mach.cp.res.nullspace (mach.cp.res.system.active (mach.resource bucket pt)) requests
  let big := mach.block.nullspace (mach.block.system.active pt) usable
  let inc := Submodule.inclusion (show small ≤ supported requests from inf_le_left)
  let proj := (mach.embed none).comp ((supported _).subtype.comp (lift.comp inc))
  have hmap : ∀ dir, proj dir ∈ big := by
    intro dir
    refine ⟨mach.embed_supported (lift (inc dir)).property, ?_⟩
    exact mach.variation_selected hf dir.property.2 (he (inc dir))
  have hi : Function.Injective (proj.codRestrict big hmap) := by
    intro first last heq
    have hh : lift (inc first) = lift (inc last) :=
      Subtype.ext (mach.embed_inj none (congrArg Subtype.val heq))
    exact Subtype.ext (congrArg (fun v : supported requests => v.val) (hinj hh))
  have hadm : mach.resource bucket pt ∈ mach.cp.res.admissible mach.client.viable limit :=
    ⟨mach.feasible_resource hf _, requests, hviable, fun row hr => (mach.resource_selected hf hr).trans hreq,
      (LinearMap.finrank_le_finrank_of_injective hi).trans hd⟩
  obtain ⟨row, hr⟩ := mach.cp.res.exists_tight large hadm
  obtain ⟨idx, hi⟩ := mach.cp.res.support_nonempty row
  exact ⟨mach.active_iff.mpr ⟨idx, mach.resource_selected hf hr hi⟩, hadm⟩

end OAI.Geometry.Hirsch.Machine
