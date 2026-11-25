import OAI.Hierarchy.DescentColonyScanLeaves

namespace OAI
/-! # Host-site indexing preserves the exact computed colony score -/

namespace Hierarchy.DescentColonies.Scan
open scoped Classical BigOperators
noncomputable section
variable {V W : Type*} [Fintype V] [Fintype W] {k : ℕ}
variable (e : V≃W) (incoming : V→List V) (load : V→Block k→ℕ) (D cap : ℕ)
local notation "incoming'" => fun t:W=>List.map e (incoming (e.symm t))
local notation "load'" => fun t:W=>load (e.symm t)

theorem lookup_reindex (s d : ℕ) (v : V) (x : Block k) :
    lookup (build incoming' load' D cap s) d (e v) x=lookup (build incoming load D cap s) d v x := by
  induction s generalizing d v x with
  | zero => rfl
  | succ s ih =>
    rw [lookup_build_succ,lookup_build_succ]
    split
    · apply Bool.eq_iff_iff.mpr
      rw [rowValue_spec,rowValue_spec]
      simp only [mass,Equiv.symm_apply_apply,ih,List.mem_map]
      apply or_congr Iff.rfl
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨w,⟨w',edge,rfl⟩,y,grouped,has⟩
        exact ⟨w',edge,y,grouped,by simpa only [ih] using has⟩
      · rintro ⟨w,edge,y,grouped,has⟩
        exact ⟨e w,⟨w,edge,rfl⟩,y,grouped,by simpa only [ih] using has⟩
    · exact ih d v x

theorem leafScore_reindex [DecidableEq V] [DecidableEq W] :
    leafScore incoming' load' D cap=leafScore incoming load D cap := by
  unfold leafScore
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro v _
  apply congrArg (fun xs=> (uniqueIDs xs).1)
  unfold keyList leafDepth
  simp_rw [lookup_reindex e incoming load D cap]

end
end Hierarchy.DescentColonies.Scan

end OAI
