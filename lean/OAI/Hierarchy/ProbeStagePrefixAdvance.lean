import OAI.Hierarchy.ProbeStagePrefixMemory

namespace OAI
/-! # Advance the true chronological counter and mask invariant one ordinal -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical
noncomputable section

variable {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))

def sideRank (left : Bool) (i : Fin (2^h)) :=
  if left then (assigned j π).enterRank i else (assigned j π).exitRank i

theorem rank_at (left : Bool) (i : Fin (2^h)) :
    (sideRank π j left i).val=Greedy.prefixCount (endpointKey j π left) (assigned j π).color i.val
      (endpointKey j π left i) ((assigned j π).color i) := by
  cases left <;> apply Greedy.rank_eq_prefix

theorem selected_color (i : Fin (2^h)) :
    let p := (history h d π j.val).tiles
    let pick := (formatAdvice h d).pick p (radix_pos h d)
    let good := Greedy.available (leftBlock p (radix_pos h d)) (rightBlock p (radix_pos h d))
      (Greedy.before (2^h) i.val) (Greedy.colors (radix_pos h d) pick (leftBlock p (radix_pos h d))
        (rightBlock p (radix_pos h d)) i.val) i
    (assigned j π).color i=maskedChoice (radix_pos h d)
      ((formatAdvice h d).row (maskIndex p (radix_pos h d) i)) good := by
  dsimp only
  apply Greedy.first_color

/-- When the two native endpoint commits visit the currently selected block and color, their
local effects imply the entire next prefix invariant on all physical counter and mask cells. -/
theorem prefix_advance {w : ℕ} (hd : 1≤d) (i : Fin (2^h)) (m o : Memory w)
    (before : PrefixState hd π j i.val m)
    (counterWords : ∀ left b c,
      let addr := counterLocation h d j.val left (blockNumber hd j π b) c
      o addr=if endpointKey j π left i=b ∧ (assigned j π).color i=c then m addr+1 else m addr)
    (maskWords : ∀ left b r chunk,
      let addr := maskLocation h d j.val left (blockNumber hd j π b) r chunk
      let full := Greedy.prefixFull (endpointKey j π left) (assigned j π).color i.val b
      o addr = if endpointKey j π left i=b ∧ (sideRank π j left i).val+1=quota (radix h d)
        then (PackedMask.word ((formatAdvice h d).row r) (insert ((assigned j π).color i) full)
          (fieldWidth h) chunk.val:Word w) else m addr) : PrefixState hd π j (i.val+1) o := by
  constructor
  · intro left b c
    rw [counterWords,Greedy.prefix_step,before.1 left b c]
    split <;> simp [*]
  · intro left b row chunk
    have safe := (sideRank π j left i).isLt
    rw [rank_at π j left i] at safe
    rw [maskWords,Greedy.full_step _ _ i b safe,←rank_at π j left i]
    by_cases hit : endpointKey j π left i=b ∧ (sideRank π j left i).val+1=quota (radix h d)
    · simp only [ite_eq_left hit]
    · simpa only [ite_eq_right hit] using before.2 left b row chunk

end
end Hierarchy.ProbeStage.Native

end OAI
