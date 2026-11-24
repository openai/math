import OAI.Computability.VPVNP.RAMSortReplay
import OAI.Computability.VPVNP.RAMLayout

/-!
# Sorting stages and the physical exchange fields

In Lemma 10.1 of *VP and VNP differ over every field*, the stride exponent
determines whether a comparison needs an exchange. Every such stage has its
own field at each site, and its addressed record partner is precisely the
site partner designated by that field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

/-- The physical fields index exactly the stages with stride at least the
site block width. Physical steps increase as the stride decreases. -/
def crossStageEquiv (h d : ℕ) : RAMLayout.Layer d ≃ {s : Stage (h + d) // h ≤ s.stride} where
  toFun s :=
    ⟨⟨h + s.phase + 1, h + s.siteBit, by
        unfold RAMLayout.Layer.siteBit
        omega, by have := s.phase_lt; omega⟩, Nat.le_add_right ..⟩
  invFun s :=
    ⟨s.val.phase - h - 1, s.val.phase - s.val.stride - 1,
      by have := s.val.phase_le; have := s.val.stride_lt; have := s.property; omega,
      by have := s.val.stride_lt; have := s.property; omega⟩
  left_inv s := by
    apply RAMLayout.Layer.ext
    · dsimp
      omega
    · dsimp [RAMLayout.Layer.siteBit]
      have := s.step_le
      omega
  right_inv s := by
    rcases s with ⟨⟨a, j, hja, hab⟩, hj⟩
    change h ≤ j at hj
    apply Subtype.ext
    apply Stage.ext <;> dsimp [RAMLayout.Layer.siteBit] <;> omega

/-- The record address in a nonlocal comparator, decoded from its field,
has the same offset at the designated peer site. -/
theorem crossStage_partner {h d : ℕ} (s : {s : Stage (h + d) // h ≤ s.stride})
    (v : Fin (2 ^ d)) (i : Fin (2 ^ h)) :
    partner s.val.stride (v.val * 2 ^ h + i.val) =
      (((crossStageEquiv h d).symm s).partner v).val * 2 ^ h + i.val := by
  obtain ⟨l, rfl⟩ := (crossStageEquiv h d).surjective s
  simp only [Equiv.symm_apply_apply]
  exact l.record_partner v i

/-- The sender read during local replay is the peer specified by the physical field. -/
theorem sourceSite_eq_physical {h d : ℕ} (s : Stage (h + d)) (hc : h ≤ s.stride)
    (v : Fin (2 ^ d)) :
    sourceSite s hc v = ((crossStageEquiv h d).symm ⟨s, hc⟩).partner v := by
  have hs := (crossStageEquiv h d).apply_symm_apply ⟨s, hc⟩
  have hj := congrArg (fun t ↦ t.val.stride) hs
  let l := (crossStageEquiv h d).symm ⟨s, hc⟩
  change h + l.siteBit = s.stride at hj
  apply Fin.ext
  change partner (s.stride - h) v.val = partner l.siteBit v.val
  rw [← hj, Nat.add_sub_cancel_left]

@[simp] theorem mem_strides {b a k : ℕ} (ha : a ≤ b) (hk : k ≤ a) (s : Stage b) :
    s ∈ strides b a ha k hk ↔ s.phase = a ∧ s.stride < k := by
  induction k with
  | zero => simp [strides]
  | succ k ih =>
    rw [strides, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨hphase, hstride⟩)
      · exact ⟨rfl, Nat.lt_succ_self k⟩
      · exact ⟨hphase, Nat.lt_succ_of_lt hstride⟩
    · rintro ⟨hphase, hstride⟩
      by_cases h : s.stride = k
      · exact Or.inl (Stage.ext hphase h)
      · exact Or.inr ⟨hphase, by omega⟩

@[simp] theorem mem_phases {b a : ℕ} (ha : a ≤ b) (s : Stage b) :
    s ∈ phases b a ha ↔ s.phase ≤ a := by
  induction a with
  | zero => simp [phases]; have := s.stride_lt; omega
  | succ a ih =>
    rw [phases, List.mem_append, ih, mem_strides]
    have := s.stride_lt
    omega

theorem strides_nodup {b a k : ℕ} (ha : a ≤ b) (hk : k ≤ a) :
    (strides b a ha k hk).Nodup := by
  induction k with
  | zero => simp [strides]
  | succ k ih =>
    rw [strides, List.nodup_cons]
    exact ⟨by simp, ih _⟩

/-- Phases one through `a` visit each of their stages exactly once. -/
theorem phases_nodup {b a : ℕ} (ha : a ≤ b) : (phases b a ha).Nodup := by
  induction a with
  | zero => simp [phases]
  | succ a ih =>
    rw [phases, List.nodup_append]
    refine ⟨ih _, strides_nodup _ _, ?_⟩
    intro s hs t ht he
    subst t
    have hprev := (mem_phases _ s).mp hs
    have hnext := ((mem_strides _ _ s).mp ht).1
    omega

/-- The full physical schedule includes every allowed `(phase, stride)`. -/
theorem mem_fullPhases {b : ℕ} (s : Stage b) : s ∈ phases b b le_rfl :=
  (mem_phases _ _).mpr s.phase_le

end RAMSort

end VPVNP
end Computability
end OAI
