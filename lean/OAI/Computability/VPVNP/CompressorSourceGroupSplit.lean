import OAI.Computability.VPVNP.CompressorSourceGroups

/-! # Splitting a chronological group at a selected source row

The tail starts in the actual memory returned by the preceding packets,
and the native row ordinal advances by their number. In particular the
packet following a selector sees the selector's own output memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceOnline.Group

open BurstRAM BlockPlanner DescriptorSpace

variable {w : ℕ} {A : Script} {L : Layout} {base : Word w} {cap ordinal total : ℕ}
variable {m : Memory w} {xs ys : List (Packet A w)}

private theorem chronological_split (h : SourceWalk.Chronological Visit.Runs m (xs++ys)) :
    SourceWalk.Chronological Visit.Runs m xs ∧ SourceWalk.Chronological Visit.Runs (post m xs) ys := by
  induction xs generalizing m with
  | nil => exact ⟨trivial,h⟩
  | cons p ps ih =>
    obtain ⟨head,tail⟩ := ih h.2.2
    refine ⟨⟨h.1,h.2.1,head⟩,?_⟩
    have same : post m (p::ps) = post p.output ps := by
      rw [← h.1]
      simp only [post,List.flatMap_cons,SourceWalk.Packet.output,SourceWalk.after_append]
    exact same.symm ▸ tail

/-- Split without choosing new executions or resetting the ordinal. -/
theorem split (h : Group A L base cap ordinal total m (xs++ys)) :
    Group A L base cap ordinal total m xs ∧
      Group A L base cap (ordinal+xs.length) total (post m xs) ys := by
  obtain ⟨first,second⟩ := chronological_split h.chronological
  constructor
  · refine ⟨first,fun p hp => h.checked p (List.mem_append_left _ hp),?_⟩
    intro i
    have bound : i.val < (xs++ys).length := by simp; omega
    have hv := h.prepared ⟨i.val,bound⟩
    simpa only [List.getElem_append_left i.isLt] using hv
  · refine ⟨second,fun p hp => h.checked p (List.mem_append_right _ hp),?_⟩
    intro i
    have bound : xs.length+i.val < (xs++ys).length := by simpa only [List.length_append] using Nat.add_lt_add_left i.isLt xs.length
    have hv := h.prepared ⟨xs.length+i.val,bound⟩
    simpa only [List.getElem_append_right (Nat.le_add_right ..),Nat.add_sub_cancel_left,← Nat.add_assoc] using hv

/-- The selector is the next executed packet after the prefix. Its own
output memory is the source of the suffix, including when either side is empty. -/
theorem split_at_selector {sel : Packet A w} (h : Group A L base cap ordinal total m (xs++sel::ys)) :
    Group A L base cap ordinal total m xs ∧
      Group A L base cap (ordinal+xs.length) total (post m xs) [sel] ∧
      sel.input = post m xs ∧
      Group A L base cap (ordinal+xs.length+1) total sel.output ys := by
  obtain ⟨before,rest⟩ := h.split
  obtain ⟨selected,suffix⟩ := (split (xs := [sel]) (ys := ys) rest)
  have input : sel.input = post m xs := selected.chronological.1
  have returned : post (post m xs) [sel] = sel.output := by
    rw [← input]
    simp only [post,List.flatMap_cons,List.flatMap_nil,List.append_nil,SourceWalk.Packet.output]
  exact ⟨before,selected,input,returned ▸ suffix⟩

end CompressorRecords.SourceOnline.Group

end VPVNP
end Computability
end OAI
