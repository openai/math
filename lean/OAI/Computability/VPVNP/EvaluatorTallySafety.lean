import OAI.Computability.VPVNP.EvaluatorTallySemantics
import OAI.Computability.VPVNP.EvaluatorRoutineSafety

/-! # All-branch clock and storage bounds for unary evaluator scans

The two counters move one mark per iteration, then the used index is
discarded. Only the callback needs a separate bound on its internal banks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorTallyLoop

open RAMTape EvaluatorRoutineSafety

variable {K Q S : Type*} [DecidableEq K]
variable (remain index : K) (body : Routine K Q) (bank : ℕ → ℕ → S → Stacks K)
    (hb : TallyBank remain index bank) (safe : Stacks K → Prop)

include hb

private theorem clear_safe (i fuel : ℕ) (x : S) (c : ℕ → Stacks K → Prop)
    (hbanks : ∀ j ≤ i, safe (bank j 0 x)) (hc : c fuel (bank 0 0 x)) :
    (tallyLoop remain index body).SafeFrom safe c (fuel+i+1) (some .clearIndex) (bank i 0 x) := by
  induction i with
  | zero =>
    rw [Routine.SafeFrom]
    exact ⟨hbanks _ le_rfl, by simpa [tallyLoop, hb.indexAt, hb.clearIndex] using hc⟩
  | succ i ih =>
    rw [Routine.SafeFrom]
    refine ⟨hbanks _ le_rfl, ?_⟩
    have hu : Function.update (bank (i+1) 0 x) index (List.replicate i true) = bank i 0 x := by
      rw [← hb.pushIndex, Function.update_idem, ← hb.indexAt i 0 x, Function.update_eq_self]
    have h := ih (fun j hj => hbanks j (by omega))
    simpa only [tallyLoop, hb.indexAt, List.replicate_succ, List.head?_cons, List.tail_cons,
      Option.map_some, hu, Nat.add_assoc] using h

private theorem scan_safe (i r fuel : ℕ) (x : S) (c : ℕ → Stacks K → Prop)
    (hbank : safe (bank i (r+1) x))
    (h : body.Safe safe (fun t s => (tallyLoop remain index body).SafeFrom safe c t (some .advance) s)
      fuel (bank i r x)) :
    (tallyLoop remain index body).Safe safe c (fuel+1) (bank i (r+1) x) := by
  have installed := (Routine.safeFrom_install (tallyLoop remain index body) body State.call (some .advance)
    (fun _ => rfl) safe c fuel (some body.entry) (bank i r x)).mpr h
  rw [Routine.Safe, Routine.SafeFrom]
  refine ⟨hbank, ?_⟩
  simpa only [tallyLoop, hb.remainAt, List.replicate_succ, List.head?_cons, List.tail_cons,
    hb.popRemain, Option.elim_some, Function.comp_apply] using installed

/-- The tally scan meets the same clock bound on all paths, including
rejecting ones, and preserves the given storage bound at every instruction. -/
theorem loop_bounded (B i r : ℕ)
    (hbanks : ∀ j left, j+left ≤ i+r → ∀ x, safe (bank j left x))
    (hbody : ∀ j left, j+left < i+r → Bounded body safe (bank j left) (bank j left) B) :
    Bounded (tallyLoop remain index body) safe (bank i r) (bank 0 0) (r*(B+2)+(i+r)+2) := by
  induction r generalizing i with
  | zero =>
    intro extra fuel hf x c hc
    let free := fuel-(i+2)
    have hh := clear_safe remain index body bank hb safe i free x c
      (fun j hj => hbanks j 0 (by omega) x) (hc x free (by dsimp [free]; simp at hf; omega))
    have he : fuel = (free+i+1)+1 := by dsimp [free]; simp at hf; omega
    rw [he, Routine.Safe, Routine.SafeFrom]
    refine ⟨hbanks i 0 le_rfl x, ?_⟩
    have hu : Function.update (bank i 0 x) remain [] = bank i 0 x := by
      have hempty : bank i 0 x remain = [] := hb.remainAt i 0 x
      rw [← hempty, Function.update_eq_self]
    simpa only [tallyLoop, hb.remainAt, List.replicate_zero, List.head?_nil, List.tail_nil, hu] using hh
  | succ r ih =>
    have later := ih (i+1) (fun j left hj => hbanks j left (by omega))
      (fun j left hj => hbody j left (by omega))
    intro extra fuel hf x c hc
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    apply scan_safe remain index body bank hb safe _ _ _ x c (hbanks i _ le_rfl x)
    let rest := r*(B+2)+(i+1+r)+2
    apply hbody i r (by omega) (extra+rest+1) fuel (by
      dsimp [rest]
      simp only [Nat.succ_mul] at hf
      omega)
    intro y k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Routine.SafeFrom]
    refine ⟨hbanks i r (by omega) y, ?_⟩
    simpa only [Routine.Safe, tallyLoop, hb.pushIndex] using
      later extra k (by dsimp [rest] at hk; omega) y c hc

end EvaluatorTallyLoop

end VPVNP
end Computability
end OAI
