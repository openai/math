import OAI.Geometry.Hirsch.Restriction

noncomputable section

open Set Filter

namespace OAI.Geometry.Hirsch.Blocking

variable {Coord Row : Type} [Fintype Coord] [Finite Row] (block : Blocking Coord Row)

theorem extend_vertex {usable : Set Coord} {rhs : Row → ℝ}
    {pt : supported usable} (hv : pt ∈ (block.restriction usable rhs).body.extremePoints ℝ) :
    ∃ x : Vec Coord, (∀ r, rhs r ≤ block.coeff r x) ∧
      {r | block.coeff r x = rhs r} = Subtype.val '' (block.restriction usable rhs).active pt ∧
      ∀ d ∈ supported usable, (∀ r, block.coeff r x = rhs r → block.coeff r d = 0) → d = 0 := by
  classical
  let fill : Vec Coord := fun i => if i ∈ usable then 0 else 1
  let point := fun t : ℝ => pt.val + t • fill
  have same : ∀ t r, r ∈ block.retained usable → block.coeff r (point t) = block.coeff r pt.val := by
    intro t r hr
    exact block.local_eq r (fun i hi => by simp [point,fill,hr hi])
  have strict : ∀ᶠ t : ℝ in atTop, ∀ r, r ∉ block.retained usable → rhs r < block.coeff r (point t) := by
    apply eventually_all.mpr
    intro r
    by_cases hr : r ∈ block.retained usable
    · exact Eventually.of_forall fun _ hn => (hn hr).elim
    obtain ⟨i,hi,hn⟩ := not_subset.mp hr
    have hpos : 0 < block.coeff r fill := by
      apply (block.weight_pos hi).trans_le
      apply block.monotone
      intro j
      by_cases he : j = i
      · simp [fill,he,hn]
      · simp [fill,he]; split <;> norm_num
    filter_upwards [eventually_gt_atTop ((rhs r - block.coeff r pt.val) / block.coeff r fill)] with t ht _
    rw [show point t = _ + _ from rfl,map_add,map_smul,smul_eq_mul]
    linarith [(div_lt_iff₀ hpos).mp ht]
  obtain ⟨t,ht⟩ := strict.exists
  have he : {r | block.coeff r (point t) = rhs r} =
      Subtype.val '' (block.restriction usable rhs).active pt := by
    ext r
    constructor
    · intro hh
      have hr : r ∈ block.retained usable := by_contra fun hn => (ht r hn).ne' hh
      exact ⟨⟨r,hr⟩,(same _ _ hr).symm.trans hh,rfl⟩
    · rintro ⟨r,hh,rfl⟩
      exact (same _ _ r.property).trans hh
  refine ⟨point t,fun r => ?_,he,fun d hd hh => ?_⟩
  · by_cases hr : r ∈ block.retained usable
    · rw [same _ _ hr]
      exact hv.1 ⟨r,hr⟩
    · exact (ht r hr).le
  · have hmem : (⟨d,hd⟩ : supported usable) ∈
        (block.restriction usable rhs).directions ((block.restriction usable rhs).active pt) :=
      (System.mem_directions _).mpr fun r hr => hh r ((same t _ r.property).trans hr)
    rw [(System.vertex_iff hv.1).mp hv] at hmem
    exact congrArg Subtype.val (show (⟨d,hd⟩ : supported usable) = 0 from hmem)

end OAI.Geometry.Hirsch.Blocking
