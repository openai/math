import OAI.Hierarchy.DescentFallbackOperandBranch

namespace OAI
/-! # Query and segment bounds for the two registered faces of a relay -/
namespace Hierarchy.DescentFallbackOperandBranch.Config
open DescentFallbackItemSelect DescentFallbackOperandQuery
noncomputable section
variable {n : ℕ} (C : Config)
private theorem selected_rank_lt {K : ℕ} (items : Fin K→Item) (live : Finset (Fin K)) (node : ℕ)
    {j : Fin K} (h : select items live node=some j) : node<K :=by
  classical
  unfold select at h
  split at h
  · rename_i hit
    obtain ⟨i,inside,atNode⟩:=hit
    rw [←atNode]
    have part : live.filter (before items · i) ⊂ Finset.univ :=by
      apply (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).2
      refine ⟨i,Finset.mem_univ _,?_⟩
      simp [before,Key.irrefl]
    simpa [rank] using Finset.card_lt_card part
  · contradiction

theorem relay_query (x : C.Data n) (target : DescentContacts.Endpoint (2^n)) (node arg : ℕ)
    (donors : C.donors≤2^C.residual) (capRoom : C.oldCap≤(C.header x 1).val)
    {out : ℕ×ℕ×ℕ×Bool} (got : C.relay x target node arg=some out) :
    out.1≤2*total C.toShape (C.header x 1).val :=by
  unfold relay at got
  split at got <;> try contradiction
  obtain ⟨j,_,found⟩:=Option.bind_eq_some_iff.mp got
  have pos:=j.isLt.trans_le (Nat.mul_le_mul donors (Nat.mul_le_mul_left 2 capRoom))
  dsimp only at found
  split at found <;> cases found <;> simp [directed,total,stemSlots] <;> omega

theorem relay_serial (x : C.Data n) (target : DescentContacts.Endpoint (2^n)) (node arg : ℕ)
    {out : ℕ×ℕ×ℕ×Bool} (got : C.relay x target node arg=some out) :
    (if out.2.2.2 then out.2.1/C.batches else 0)≤C.count :=by
  unfold relay at got
  split at got <;> try contradiction
  obtain ⟨j,chosen,found⟩:=Option.bind_eq_some_iff.mp got
  have bound:=selected_rank_lt (C.relayItems x) (C.relayRows x target) node chosen
  dsimp only at found
  split at found
  · rename_i first
    cases found
    by_cases mark : target.2.isSome=true
    · simp only [mark,↓reduceIte]
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt first),
        Nat.div_eq_of_lt first,Nat.zero_add]
      exact bound.le
    · simp [mark]
  · cases found
    exact Nat.zero_le _
end
end Hierarchy.DescentFallbackOperandBranch.Config

end OAI
