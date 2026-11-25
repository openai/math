import OAI.Computability.BorderVNP.TeamProbeStage
import OAI.Computability.BorderVNP.TeamProbeWordCast
import OAI.Computability.BorderVNP.TeamProbeWordLift

/-! # Appending an arbitrary ordinary or burst probe to the physical sorter

The four source ports contain the full logical RAM words. The fixed callback preserves
them, zero-extends them into one-bit-wider work registers, then emits the read half
and write half of the probe at the common tick. This supports every logical RAM address
and every previous and resulting word, including values at the top of the word range.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamProbeEmit

open VPVNP BurstRAM RAMTape RAMSerialization

variable {w H : ℕ}

/-- Companion-paper record prescribed by the four current RAM registers. -/
def probe (z : Operand → Word w) : TeamRecords.Record (Word w) :=
  ⟨(z .address).val, (z .tick).val, z .before, z .after⟩

/-- Extra width gives an unused phase bit at both ends of the whole address space. -/
theorem probeFits (z : Operand → Word w) : TeamTapeSorting.ProbeFits (widenRecord (probe z)) :=
  probeFits_widenRecord (probe z) (z .address).isLt (z .tick).isLt

/-- Both physical emissions are exactly the old read/write pair of the widened logical probe. -/
theorem halves_eq_pair (z : Operand → Word w) :
    [half (widen ∘ z) false, half (widen ∘ z) true] =
      TeamTapeSorting.wordPair (widenRecord (probe z)) (probeFits z) := by
  have hf := (probeFits z).1
  change 2*(z .address).val+1 < 2^(w+1) at hf
  simp only [TeamTapeSorting.wordPair, List.cons.injEq, and_true]
  constructor <;> apply WordRecord.record_injective <;>
    simp [half, probe, widenRecord, widen, WordRecord.record, WordRecord.ofRecord,
      TeamRecords.inputRecord, TeamRecords.outputRecord,
      Nat.mod_eq_of_lt (show 2*(z .address).val < 2^(w+1) by omega), Nat.mod_eq_of_lt hf]

private def widenedBank (ks : List Operand) (z : Operand → Word w) (s : Stacks Port) : Stacks Port
  | .lifted i => if i ∈ ks then BurstRAM.wordBits (widen (z i)) else s (.lifted i)
  | k => s k

private theorem widenAll_runs (ks : List Operand) (z : Operand → Word w) (s : Stacks Port)
    (hz : ∀ k, s (.operand k) = BurstRAM.wordBits (z k)) (ht : s .temp = [])
    (hold : ∀ k, (s (.lifted k)).length ≤ w+1) :
    ∃ t ≤ ks.length*(6*w+5)+1, (extendAll .temp Port.operand Port.lifted ks).Runs t s (widenedBank ks z s) := by
  induction ks generalizing s with
  | nil =>
    have he : widenedBank [] z s = s := by funext k; cases k <;> simp [widenedBank]
    exact ⟨1, by simp, he.symm ▸ Routine.runs_ret s⟩
  | cons k ks ih =>
    let u := Function.update s (.lifted k) (BurstRAM.wordBits (widen (z k)))
    have head := extendWord_runs (.operand k) (.lifted k) .temp (by simp) (by simp) (by simp) s ht
    rw [hz, length_wordBits, ← wordBits_widen] at head
    have hu (i) : u (.operand i) = BurstRAM.wordBits (z i) := by simpa [u] using hz i
    have hlen (i) : (u (.lifted i)).length ≤ w+1 := by
      by_cases hi : i = k
      · simp [u, hi]
      · simpa [u, hi] using hold i
    obtain ⟨t, htime, tail⟩ := ih u hu (by simpa [u] using ht) hlen
    have hbank : widenedBank ks z u = widenedBank (k::ks) z s := by
      funext p
      cases p with
      | lifted i => by_cases hi : i=k <;> simp [widenedBank, u, hi]
      | _ => simp [widenedBank, u]
    rw [hbank] at tail
    refine ⟨_, ?_, head.followedBy tail⟩
    rw [List.length_cons, Nat.succ_mul ks.length (6*w+5)]; have := hold k; omega

private def operands : List Operand := [.address, .tick, .before, .after]

private theorem mem_operands (k : Operand) : k ∈ operands := by cases k <;> decide

/-- One reusable fixed stack table. Scratch copies from the last probe may still be present. -/
def program : FiniteRoutine Port :=
  (extendAll .temp Port.operand Port.lifted operands).followedBy
    ((emitHalf false).followedBy (emitHalf true))

/-- Interface at the four arbitrary word operands and the current physical sorter buffer. -/
structure Staged (hw : 2 ≤ w+1) (H : ℕ) (z : Operand → Word w)
    (rs : List (WordRecord (w+1))) (s : Stacks Port) : Prop where
  operands : ∀ k, s (.operand k) = BurstRAM.wordBits (z k)
  scratch : s .temp = []
  work : ∀ k, (s (.lifted k)).length ≤ w+1
  buffer : RecordBuffer.Holds hw H rs (s ∘ Port.buffer)
  fields : ∀ j, (s (.buffer (.field j))).length ≤ w+1

/-- Explicit deterministic bound and postcondition for appending the read of the old word
and write of the new word. The same four RAM inputs remain available on return. -/
theorem runs {hw : 2 ≤ w+1} {z : Operand → Word w} {rs : List (WordRecord (w+1))}
    {s : Stacks Port} (hs : Staged hw H z rs s) (free : rs.length+2 ≤ 4*H) :
    ∃ t out, t ≤ 154*w+207 ∧ program.Runs t s out ∧
      Staged hw H z (rs ++ TeamTapeSorting.wordPair (widenRecord (probe z)) (probeFits z)) out := by
  obtain ⟨t, htime, lift⟩ := widenAll_runs operands z s hs.operands hs.scratch hs.work
  let u := widenedBank operands z s
  have ready : Ready hw H (widen ∘ z) rs u :=
    ⟨fun k => by simp [u, widenedBank, mem_operands], hs.buffer, hs.fields⟩
  have hbound := (probeFits z).1
  change 2*(z .address).val+1 < 2^(w+1) at hbound
  obtain ⟨n, mid, hn, one, hm, preserved, htmp⟩ :=
    emitHalf_runs (phase := false) ready (by change 2*(z .address).val+0 < 2^(w+1); omega) (by omega)
  obtain ⟨m, out, hm', two, hend, hsaved, htmp'⟩ :=
    emitHalf_runs (phase := true) hm hbound (by simp; omega)
  have he : (rs ++ [half (widen ∘ z) false]) ++ [half (widen ∘ z) true] =
      rs ++ TeamTapeSorting.wordPair (widenRecord (probe z)) (probeFits z) := by
    rw [← halves_eq_pair, List.append_assoc]; rfl
  rw [he] at hend
  refine ⟨_, out, ?_, lift.followedBy (one.followedBy two), ?_⟩
  · change t ≤ 4*(6*w+5)+1 at htime; omega
  · exact ⟨fun k => (hsaved k).trans ((preserved k).trans (hs.operands k)),
      htmp'.trans (htmp.trans hs.scratch), fun k => by rw [hend.lifted k, length_wordBits],
      hend.buffer, hend.fields⟩

end TeamProbeEmit

end BorderVNP
end Computability
end OAI
