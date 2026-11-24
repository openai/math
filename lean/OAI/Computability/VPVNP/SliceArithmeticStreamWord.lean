import OAI.Computability.VPVNP.EvaluatorRadixDivision
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-!
# Word transfers for the streamed extension-field evaluator

Each architectural register has the common word width. During a load, popping
the old register provides one iteration per input bit. A single scratch stack
then restores the loaded word to least-significant-bit-first order. A store
uses the same scratch space to prepend the register to a packed output stream.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.StreamWord

open RAMTape BurstRAM

variable {K : Type}

private def saveBit (stream scratch : K) :=
  Routine.popCase stream (Routine.halt false) (Routine.push scratch false) (Routine.push scratch true)

private def savePrefix (stream reg scratch : K) :=
  Routine.popLoop reg (fun _ => true) (saveBit stream scratch) (saveBit stream scratch)

/-- Replace the register by one word from the front of the stream. -/
def load (stream reg scratch : K) : FiniteRoutine K :=
  (FiniteRoutine.ofRoutine (savePrefix stream reg scratch)).followedBy
    (EvaluatorRadixDivision.reverseOnto scratch reg)

/-- Prepend the register to the stream and restore the register. -/
def store (stream reg scratch : K) : FiniteRoutine K :=
  SuccessorFields.prependCopy reg stream scratch

/-- Emit the register in the reverse bit order used by a backward output scan. -/
def storeReverse (stream reg scratch tmp : K) : FiniteRoutine K :=
  (store scratch reg tmp).followedBy (EvaluatorRadixDivision.reverseOnto scratch stream)

variable [DecidableEq K] {stream reg scratch : K}

private theorem savePrefix_runs (hsr : stream ≠ reg) (hst : stream ≠ scratch) (hrt : reg ≠ scratch)
    (bits tail : List Bool) (s u : Stacks K)
    (hreg : (s reg).length = bits.length) (hstream : s stream = bits ++ tail)
    (uread : u stream = tail) (ureg : u reg = []) (utmp : u scratch = bits.reverse ++ s scratch)
    (hframe : ∀ k, k ≠ stream → k ≠ reg → k ≠ scratch → u k = s k) :
    (savePrefix stream reg scratch).Runs (3 * bits.length + 1) s u := by
  induction bits generalizing s with
  | nil =>
    have hr : s reg = [] := List.length_eq_zero_iff.mp hreg
    have hu : u = s := by
      funext k
      by_cases hi : k = stream
      · subst k; exact uread.trans hstream.symm
      by_cases hj : k = reg
      · subst k; exact ureg.trans hr.symm
      by_cases hk : k = scratch
      · subst k; exact utmp
      exact hframe k hi hj hk
    rw [hu]
    exact Routine.Runs.popLoop_empty reg _ _ _ hr
  | cons b bits ih =>
    cases h : s reg with
    | nil => simp [h] at hreg
    | cons d old =>
      let a := Function.update s reg old
      let v := Function.update a stream (bits ++ tail)
      let next := Function.update v scratch (b :: s scratch)
      have ha : a stream = b :: (bits ++ tail) := by simp [a, hsr, hstream]
      have hv : v scratch = s scratch := by simp [v, a, hst.symm, hrt.symm]
      have hpush : (Routine.push scratch b).Runs 1 v next := by
        simpa only [hv] using Routine.runs_push scratch b v
      have hbit : (saveBit stream scratch).Runs 2 a next := by
        cases b with
        | false => exact Routine.runs_popCase_false _ _ _ _ ha hpush
        | true => exact Routine.runs_popCase_true _ _ _ _ ha hpush
      have hr : (savePrefix stream reg scratch).Runs (3 * bits.length + 1) next u := by
        apply ih next
        · have hlen : old.length = bits.length := by simpa [h] using hreg
          simpa [next, v, a, hrt, hsr.symm] using hlen
        · simp [next, v, hst]
        · simpa [next, List.reverse_cons, List.append_assoc] using utmp
        · intro k hi hj hk
          simpa [next, v, a, hi, hj, hk] using hframe k hi hj hk
      have run := Routine.Runs.popLoop_continue reg (fun _ => true) (saveBit stream scratch)
        (saveBit stream scratch) h rfl (by cases d <;> exact hbit) hr
      rw [show 3 * (b :: bits).length + 1 = 1 + 2 + (3 * bits.length + 1) by
        simp only [List.length_cons]; omega]
      exact run

/-- The width comes from the old register. Other stacks retain their contents,
the input tail is untouched, and the scratch stack returns empty. -/
theorem load_runs (hsr : stream ≠ reg) (hst : stream ≠ scratch) (hrt : reg ≠ scratch)
    (s : Stacks K) {w : ℕ} (x : BurstRAM.Word w) (tail : List Bool)
    (hreg : (s reg).length = w) (hstream : s stream = wordBits x ++ tail) (ht : s scratch = []) :
    (load stream reg scratch).Runs (5 * w + 2) s
      (Function.update (Function.update s stream tail) reg (wordBits x)) := by
  let base := Function.update s stream tail
  let mid := Function.update (Function.update base reg []) scratch (wordBits x).reverse
  let out := Function.update base reg (wordBits x)
  have first := savePrefix_runs hsr hst hrt (wordBits x) tail s mid (by simpa using hreg) hstream
    (by simp [mid, base, hst, hsr]) (by simp [mid, hrt]) (by simp [mid, ht])
    (fun k hi hj hk => by simp [mid, base, hi, hj, hk])
  have second := EvaluatorRadixDivision.reverseOnto_runs hrt.symm mid out
    (by simp [out, base, hst.symm, hrt.symm, ht]) (by simp [out, mid, hrt])
    (fun k hk hj => by simp [out, mid, hk, hj])
  have run := FiniteRoutine.Runs.followedBy (a := FiniteRoutine.ofRoutine (savePrefix stream reg scratch))
    first second
  change (load stream reg scratch).Runs
    (3 * (wordBits x).length + 1 + (2 * (mid scratch).length + 1)) s out at run
  simp only [mid, Function.update_self, List.length_reverse, length_wordBits] at run
  rw [show 3*w + 1 + (2*w + 1) = 5*w + 2 by omega] at run
  exact run

/-- Copy a register onto the output stream in its native bit order. -/
theorem store_runs (hsr : stream ≠ reg) (hst : stream ≠ scratch) (hrt : reg ≠ scratch)
    (s : Stacks K) {w : ℕ} (x : BurstRAM.Word w) (hreg : s reg = wordBits x) (ht : s scratch = []) :
    (store stream reg scratch).Runs (5 * w + 2) s
      (Function.update s stream (wordBits x ++ s stream)) := by
  simpa only [store, hreg, length_wordBits] using
    SuccessorFields.prependCopy_runs reg stream scratch hsr.symm hrt hst s ht

/-- A reversed store stages a copy of the register, then transfers its bits to
the stream. Both temporary stacks return empty. -/
theorem storeReverse_runs {tmp : K} (_hsr : stream ≠ reg) (hss : stream ≠ scratch)
    (_hst : stream ≠ tmp) (hrs : reg ≠ scratch) (hrt : reg ≠ tmp) (hstmp : scratch ≠ tmp)
    (s : Stacks K) {w : ℕ} (x : BurstRAM.Word w) (hreg : s reg = wordBits x)
    (hs : s scratch = []) (ht : s tmp = []) :
    (storeReverse stream reg scratch tmp).Runs (7*w + 3) s
      (Function.update s stream ((wordBits x).reverse ++ s stream)) := by
  let mid := Function.update s scratch (wordBits x)
  let out := Function.update s stream ((wordBits x).reverse ++ s stream)
  have first : (store scratch reg tmp).Runs (5*w + 2) s mid := by
    simpa only [hs, List.append_nil] using store_runs hrs.symm hstmp hrt s x hreg ht
  have second := EvaluatorRadixDivision.reverseOnto_runs hss.symm mid out
    (by simp [out, hss.symm, hs]) (by simp [out, mid, hss])
    (fun k hi hj => by simp [out, mid, hi, hj])
  have run := first.followedBy second
  simp only [mid, Function.update_self, length_wordBits] at run
  rw [show 5*w + 2 + (2*w + 1) = 7*w + 3 by omega] at run
  exact run

end SliceArithmetic.StreamWord

end VPVNP
end Computability
end OAI
