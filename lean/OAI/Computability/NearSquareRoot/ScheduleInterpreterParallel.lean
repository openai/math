import OAI.Computability.IntegerMultiplication.TMModel
import Mathlib.Data.Fintype.Pi

/-!
# Running independent scratch routines on all physical tapes

The finite state keeps one local control state per tape. Finished heads
remain still while the other heads finish. A common upper bound on the
individual running times therefore bounds the entire physical trace.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Parallel

open IntegerMultiplication TM

variable {A Q I : Type}

def pack (localCfg : I → Config A Q Unit) : Config A (I → Q) I :=
  ⟨fun i => (localCfg i).pc, fun i => (localCfg i).tape ()⟩

private def action (m : Rule A Q Unit) (q : Q) (v : A) : Q × A × Move :=
  match m q (fun _ => v) with
  | none => (q, v, .stay)
  | some (q', ops) => (q', ops ())

def rule [Fintype I] (m : I → Rule A Q Unit) : Rule A (I → Q) I := fun q v =>
  if ∀ i, ((m i) (q i) (fun _ => v i)).isNone then none
  else some (fun i => (action (m i) (q i) (v i)).1,
             fun i => (action (m i) (q i) (v i)).2)

private def padded (m : Rule A Q Unit) (c : Config A Q Unit) : Config A Q Unit :=
  (advance m c).getD c

private theorem stationary (t : Tape A) : t.apply (t.view 0, Move.stay) = t := by
  cases t with
  | mk p v =>
    simp [Tape.apply, Move.shift]
    funext j
    split <;> simp_all

private theorem pad_eq (m : Rule A Q Unit) (c : Config A Q Unit) :
    padded m c = ⟨(action m c.pc ((c.tape ()).view 0)).1,
      fun _ => (c.tape ()).apply (action m c.pc ((c.tape ()).view 0)).2⟩ := by
  cases c with
  | mk q t =>
    have h : (fun i => (t i).view 0) = fun _ => (t ()).view 0 := by
      funext i
      cases i
      rfl
    unfold padded advance
    rw [h]
    cases hm : m q (fun _ => (t ()).view 0) with
    | none =>
      simp [action, hm, stationary]
    | some qo =>
      obtain ⟨q', ops⟩ := qo
      simp [action, hm]

theorem advance_pack [Fintype I] (m : I → Rule A Q Unit) (x : I → Config A Q Unit) :
    advance (rule m) (pack x) =
      if ∀ i, (advance (m i) (x i)).isNone then none
      else some (pack (fun i => padded (m i) (x i))) := by
  have h : ∀ i, (fun j => ((x i).tape j).view 0) = fun _ => ((x i).tape ()).view 0 := by
    intro i
    funext j
    cases j
    rfl
  simp only [advance, h, Option.isNone_map]
  simp only [rule, pack]
  split <;> rename_i hg
  · simp only [hg, show (∀ _ : I, True) ↔ True from iff_true_intro (fun _ => trivial), ite_true, Option.map_none]
  · simp only [hg, ite_false, Option.map_some, pad_eq]

private theorem drop (m : Rule A Q Unit) {c d : Config A Q Unit} {k n : ℕ}
    (run : Trace (advance m) c k d) (hn : k ≤ n+1) (stop : advance m d = none) :
    ∃ j ≤ n, Trace (advance m) (padded m c) j d := by
  cases run with
  | nil => exact ⟨0, Nat.zero_le _, by simp [padded, stop]; exact .nil _⟩
  | @cons _ u _ k ht tail => exact ⟨k, by omega, by simpa [padded, ht] using tail⟩

private theorem eq_if_zero {D : Type} {step : D → Option D} {c d : D} {k : ℕ}
    (h : Trace step c k d) (hk : k = 0) : c = d := by
  cases h with
  | nil => rfl
  | cons => omega

private theorem eq_if_halted {D : Type} (step : D → Option D) {c d : D} {k : ℕ}
    (run : Trace step c k d) (stop : step c = none) : c = d := by
  cases run with
  | nil => rfl
  | cons ht => simp [stop] at ht

/-- Unequal local run lengths are allowed. No absence test on distant cells
or local rewind distance is built into the joint control. -/
theorem trace [Fintype I] (m : I → Rule A Q Unit) (x y : I → Config A Q Unit) (n : ℕ)
    (runs : ∀ i, ∃ k ≤ n, Trace (advance (m i)) (x i) k (y i))
    (halts : ∀ i, advance (m i) (y i) = none) :
    ∃ t ≤ n, Trace (advance (rule m)) (pack x) t (pack y) ∧
      advance (rule m) (pack y) = none := by
  have hfinal : advance (rule m) (pack y) = none := by simp [advance_pack, halts]
  induction n generalizing x with
  | zero =>
    have eq : x = y := by
      funext i
      obtain ⟨k, hk, ht⟩ := runs i
      obtain rfl : k = 0 := by omega
      exact eq_if_zero ht rfl
    subst x
    exact ⟨0, by omega, .nil _, hfinal⟩
  | succ n ih =>
    by_cases hs : ∀ i, (advance (m i) (x i)).isNone
    · have eq : x = y := by
        funext i
        obtain ⟨k, _, ht⟩ := runs i
        exact eq_if_halted _ ht (by simpa using hs i)
      subst x
      exact ⟨0, by omega, .nil _, hfinal⟩
    · obtain ⟨t, ht, tail, halt⟩ := ih (fun i => padded (m i) (x i)) (fun i => by
        obtain ⟨k, hk, htr⟩ := runs i
        exact drop _ htr hk (halts i))
      exact ⟨1+t, by omega, .cons (by simp only [advance_pack, hs, ite_false]) tail, halt⟩

/-- Project any prefix of the physical simultaneous execution to a prefix of
each constituent trace. After a local halt a head only stutters. -/
theorem project_prefix [Fintype I] (m : I → Rule A Q Unit) (x : I → Config A Q Unit)
    {k : ℕ} {w : Config A (I → Q) I} (h : Trace (advance (rule m)) (pack x) k w) :
    ∃ y : I → Config A Q Unit, w = pack y ∧
      ∀ i, ∃ j ≤ k, Trace (advance (m i)) (x i) j (y i) := by
  generalize heq : pack x = init at h
  induction h generalizing x with
  | nil init => exact ⟨x, heq.symm, fun i => ⟨0, le_rfl, .nil _⟩⟩
  | @cons init u w n step _ ih =>
    subst init
    rw [advance_pack] at step
    split at step
    · cases step
    · have hc := Option.some.inj step
      obtain ⟨z, hzc, hz⟩ := ih _ hc
      refine ⟨z, hzc, fun i => ?_⟩
      obtain ⟨j, hj, tr⟩ := hz i
      cases hi : advance (m i) (x i) with
      | none => exact ⟨j, by omega, by simpa [padded, hi] using tr⟩
      | some v =>
        exact ⟨1+j, by omega, .cons hi (by simpa [padded, hi] using tr)⟩

end Uniform.Parallel

end NearSquareRoot
end Computability
end OAI
