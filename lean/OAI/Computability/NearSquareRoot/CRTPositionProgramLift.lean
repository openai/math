import OAI.Computability.NearSquareRoot.CRTPositionProgramGates
import OAI.Computability.NearSquareRoot.CRTPositionEvaluation

/-! # Running three-chunk programs at the native word width

Deleting the residual positions keeps every chunk port at the same index.
Consequently any list of directed gates acts identically on the bulk at both
widths and preserves the native tail. This permits all gate and swap operations
of a reflected round to execute on the same full-width word.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open PositionPreparation

/-- Apply a word operation to the three complete chunks, carrying the remaining
positions through the operation. -/
def extendBulk {k : ℕ} (bulk : (Fin (3 * (k / 3)) → Bool) → Fin (3 * (k / 3)) → Bool)
    (w : Fin k → Bool) (x : Fin k) : Bool :=
  if hx : x.val < 3 * (k / 3) then
    bulk (fun j => w (Fin.castLE (by omega) j)) ⟨x.val,hx⟩
  else w x

private def agrees {k n : ℕ} (h : k / 3 = n / 3) (w : Fin k → Bool) (v : Fin n → Bool) :=
  ∀ c i, chunkWord w c i = chunkWord v c (Fin.cast h i)

private theorem xor_cast {m n : ℕ} (h : m = n) (t : ReadTable)
    (s d : Fin m → Bool) (s' d' : Fin n → Bool)
    (hs : ∀ i, s i = s' (Fin.cast h i)) (hd : ∀ i, d i = d' (Fin.cast h i)) (i : Fin m) :
    xorFrom (decodePort t) s d i = xorFrom (decodePort t) s' d' (Fin.cast h i) := by
  subst n
  rw [funext hs, funext hd]
  rfl

private theorem directed_chunk {k : ℕ} (a : Gate) (w : Fin k → Bool) (c : Fin 3)
    (i : Fin (k/3)) :
    chunkWord (directed a w) c i =
      if c = a.2.1 then xorFrom (decodePort a.2.2) (chunkWord w a.1) (chunkWord w a.2.1) i
      else chunkWord w c i := by
  simp only [chunkWord, directed, Equiv.apply_symm_apply]

private theorem agrees_directed {k n : ℕ} {h : k/3 = n/3} {w : Fin k → Bool} {v : Fin n → Bool}
    (hv : agrees h w v) (a : Gate) : agrees h (directed a w) (directed a v) := by
  intro c i
  rw [directed_chunk, directed_chunk]
  split
  · exact xor_cast h a.2.2 _ _ _ _ (hv a.1) (hv a.2.1) i
  · exact hv c i

private theorem agrees_run {k n : ℕ} {h : k/3 = n/3} (ls : List Gate)
    {w : Fin k → Bool} {v : Fin n → Bool} (hv : agrees h w v) : agrees h (run ls w) (run ls v) := by
  induction ls generalizing w v with
  | nil => exact hv
  | cons a ls ih => exact ih (agrees_directed hv a)

private theorem run_tail {k : ℕ} (ls : List Gate) (w : Fin k → Bool) (j : Fin (k%3)) :
    run ls w ((threeChunksWithTail k).symm (.inr j)) = w ((threeChunksWithTail k).symm (.inr j)) := by
  induction ls generalizing w with
  | nil => rfl
  | cons a ls ih =>
    change run ls (directed a w) _ = w _
    rw [ih]
    simp only [directed, Equiv.apply_symm_apply]

/-- Every native gate program restricts to the same program on the three
complete chunks and fixes every remaining bit. -/
theorem run_extendBulk {k : ℕ} (program : List Gate) (w : Fin k → Bool) :
    run program w = extendBulk (run program) w := by
  let n := 3 * (k/3)
  have hn : n ≤ k := by dsimp [n]; omega
  have h : k/3 = n/3 := by dsimp [n]; omega
  let v (j : Fin n) := w (Fin.castLE hn j)
  have hv : agrees h w v := by
    intro c i
    unfold chunkWord v
    apply congrArg w
    apply Fin.ext
    simp [← h]
  have same := agrees_run program hv
  funext x
  obtain ⟨a,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  cases a with
  | inr j =>
    rw [run_tail]
    simp [extendBulk, threeChunksWithTail_tail]
  | inl ci =>
    obtain ⟨c,i⟩ := ci
    have small : ((threeChunksWithTail k).symm (.inl (c,i))).val < n := by
      have ci := c.isLt
      have ii := i.isLt
      simp only [threeChunksWithTail_bulk, n]
      have hc : c.val ≤ 2 := by omega
      have mul := Nat.mul_le_mul_left (k/3) hc
      omega
    rw [extendBulk, dite_eq_left small]
    apply (same c i).trans
    apply congrArg (run program v)
    apply Fin.ext
    simp [← h]

/-- Exchange two unary-indexed positions when both are in range. -/
def swapPair {k : ℕ} (q : Reflections.Pair) (w : Fin k → Bool) (x : Fin k) : Bool :=
  if h : q.1.length < k ∧ q.2.length < k then
    w (Equiv.swap ⟨q.1.length,h.1⟩ ⟨q.2.length,h.2⟩ x)
  else w x

/-- Running the emitted swaps in reverse list order followed by all 36 native
gates gives the round interpreter for every serialized round. -/
theorem nativeRound_eq_executeRound {k : ℕ} (code : RoundCode) (w : Fin k → Bool) :
    run (gates code.1) (code.2.reverse.foldl (fun z q => swapPair q z) w) =
      executeRound @runTables code w := by
  rw [run_extendBulk, List.foldl_reverse]
  have e : (@run (3 * (k/3)) (gates code.1)) = runTables code.1 := funext (run_gates code.1)
  rw [e]
  rfl

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
