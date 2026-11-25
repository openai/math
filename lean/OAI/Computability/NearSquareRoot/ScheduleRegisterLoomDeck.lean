import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect
import OAI.Computability.NearSquareRoot.BoundedBranch

/-!
# Transport of a bounded-deck clock to arbitrary parked decks

A finite program and its surrounding scope can inspect only a fixed finite
prefix of the register bank. Filling the other registers with their original
contents therefore preserves its exact clock and results.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code CommonRegisters Space Filter

private def retain {A : Type} (R : ℕ) (extra d : Reg A) : Reg A :=
  fun i => if i < R then d i else extra i

private theorem retain_update {A : Type} {R i : ℕ} (h : i < R)
    (extra d : Reg A) (x : List A) :
    retain R extra (Function.update d i x) = Function.update (retain R extra d) i x := by
  funext j
  by_cases e : j = i
  · subst j
    simp [retain, h]
  · simp [retain, Function.update_of_ne e]

private theorem run_retain {A : Type} {R : ℕ} {env : Scope A} {c : Prog A}
    {r s : Reg A} {n : ℕ} (h : Prog.Run env c r n s)
    (hc : Within R c) (hs : ∀ d ∈ env, Within R d) (extra : Reg A) :
    Prog.Run env c (retain R extra r) n (retain R extra s) := by
  induction h with
  | pass => exact .pass
  | @push env i x r =>
    rw [retain_update hc]
    simpa only [retain, ite_eq_left (show i < R from hc)] using
      (Prog.Run.push (Γ := env) (i := i) (x := x) (r := retain R extra r))
  | @pop env i r =>
    rw [retain_update hc]
    simpa only [retain, ite_eq_left (show i < R from hc)] using
      (Prog.Run.pop (Γ := env) (i := i) (r := retain R extra r))
  | @look env i f r n s child ih =>
    apply Prog.Run.look
    simpa only [retain, ite_eq_left hc.1] using ih (hc.2 _) hs
  | join _ _ left right => exact (left hc.1 hs).join (right hc.2 hs)
  | tie _ ih =>
    apply Prog.Run.tie
    apply ih hc
    intro d hd
    rcases List.mem_cons.mp hd with rfl | md
    · exact hc
    · exact hs d md
  | again look _ ih =>
    exact .again look (ih (hs _ (List.mem_of_getElem? look)) fun d hd => hs d (List.mem_of_mem_drop hd))

/-- A clock verified on every bounded background deck holds on all background
decks, including a deck whose unrelated registers have unbounded lengths. -/
theorem fits_of_bounded_decks (c : Cmd) (p q : Tree) (time : ℕ)
    (h : ∀ env r base, DeckCap base r → Fits env c (pile 0 p r) (pile 0 q r) time)
    (env : Env) (r : Deck) : Fits env c (pile 0 p r) (pile 0 q r) time := by
  classical
  have he : ∀ᶠ R in atTop, ∀ d ∈ env, Within R d := by
    induction env with
    | nil => simp
    | cons d env ih =>
      filter_upwards [RegisterSelect.within_eventually d, ih] with R hd he
      exact List.forall_mem_cons.mpr ⟨hd, he⟩
  obtain ⟨R, hR, hc, he⟩ := ((eventually_gt_atTop 0).and ((RegisterSelect.within_eventually c).and he)).exists
  let core : Deck := fun i => if i < R then r i else []
  let cap := (Finset.range R).sup (fun i => (letters r i).length)
  have bounded : DeckCap cap core := by
    intro i
    by_cases hi : i < R
    · simpa only [cap, letters, core, ite_eq_left hi] using
        (Finset.le_sup (f := fun i => (letters r i).length) (Finset.mem_range.mpr hi))
    · simp [letters, core, hi]
  obtain ⟨t, ht, run⟩ := h env core cap bounded
  have same (z : Tree) : retain R (letters r) (letters (pile 0 z core)) = letters (pile 0 z r) := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [retain, hR, letters, core]
    · by_cases hr : i < R <;> simp [retain, letters, core, hr, pile_else 0 z _ i hi]
  exact ⟨t, ht, by simpa only [same] using run_retain run hc he (letters r)⟩

/-- Forgetting the peak bounds keeps the register cutoff, the same compiled
program and its time constant, even on an arbitrary background deck. -/
theorem timed_of_bounded {I : Type*} {R : ℕ} {T S : I → ℕ} {p q : I → Tree}
    (h : RegisterWitness.Bounded R T S p q) : RegisterWitness.Timed R T p q := by
  obtain ⟨c, within, C, run⟩ := h
  refine ⟨c, within, C, fun i env r => ?_⟩
  exact fits_of_bounded_decks c (p i) (q i) (C * (T i + 1))
    (fun scope deck b hb => (run i scope deck b hb).fits) env r

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
