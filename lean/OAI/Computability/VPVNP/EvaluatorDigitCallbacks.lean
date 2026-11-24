import OAI.Computability.VPVNP.EvaluatorDigitRepeat
import OAI.Computability.VPVNP.RAMTapeWordSlice

/-!
# Iterating a branching evaluator callback by a binary digit

Each positive counter value dispatches one copy of the same callback. Its
different outcomes can take different times and change the evaluator state.
The counter stays at the decremented value for all of these outcomes. At
zero the loop clears the counter and invokes the caller once per sequence
of callback outcomes, with the actual remaining fuel for that sequence.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorDigitCallbacks

open RAMTape TapeWord EvaluatorDigitRepeat

theorem split_positive (bits : List Bool) (h : 0 < value bits) :
    ∃ l tail, bits = List.replicate l false ++ true :: tail := by
  induction bits with
  | nil => exact (Nat.not_lt_zero _ h).elim
  | cons b bits ih =>
    cases b
    · have hp : 0 < value bits := by simp [value] at h; omega
      obtain ⟨l, tail, rfl⟩ := ih hp
      exact ⟨l + 1, tail, by rw [List.replicate_succ, List.cons_append]⟩
    · exact ⟨0, bits, rfl⟩

private theorem sum_traces_succ {I : Type*} [Fintype I] {d : ℕ}
    (f : (Fin (d + 1) → I) → ℕ) : ∑ z, f z = ∑ i, ∑ tail, f (Fin.cons i tail) := by
  rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => I)).sum_comp f, Fintype.sum_prod_type]
  rfl

/-- A per-trace upper bound. It covers the empty-counter pass at the end,
one scan and restoration per positive counter, and every callback. -/
def repeatBudget (w B d : ℕ) := (d + 1) * (4 * w + B + 3)

/-- The output on trace `z` is obtained by folding the callback transition
over exactly `d` outcomes. The single family of actual delays works for
every continuation, including continuations that inspect the fuel. -/
theorem repeat_count_of_bound {K Q S I : Type*} [DecidableEq K] [Fintype I]
    (src tmp : K) (hne : src ≠ tmp) (body : Routine K Q)
    (bank : S → Stacks K) (next : S → I → S) (w B : ℕ)
    (callback : ∀ x bits fuel, (bits : List Bool).length = w → B ≤ fuel →
      ∃ delay : I → ℕ, (∀ i, delay i ≤ B) ∧ ∀ c,
        body.count c fuel (frame src tmp (bank x) bits []) =
          ∑ i, c (fuel - delay i) (frame src tmp (bank (next x i)) bits []))
    (d : ℕ) (bits : List Bool) (hw : bits.length = w) (hd : value bits = d)
    (x : S) (fuel : ℕ) (hf : repeatBudget w B d ≤ fuel) :
    ∃ delay : (Fin d → I) → ℕ, (∀ z, delay z ≤ repeatBudget w B d) ∧ ∀ c,
      (repeatRoutine src tmp body).count c fuel (frame src tmp (bank x) bits []) =
        ∑ z, c (fuel - delay z) (frame src tmp (bank ((List.ofFn z).foldl next x)) [] []) := by
  classical
  induction d generalizing bits x fuel with
  | zero =>
    have hz : bits = List.replicate w false := eq_of_length_value (by simpa using hw) (by simpa using hd)
    subst bits
    have h₀ : 3 * w + 2 ≤ repeatBudget w B 0 := by simp [repeatBudget]; omega
    refine ⟨fun _ => 3 * w + 2, fun _ => h₀, fun c => ?_⟩
    rw [← Nat.sub_add_cancel (h₀.trans hf)]
    have h := count_zero src tmp hne body c (bank x) w (fuel - (3 * w + 2))
    simpa only [Nat.sub_add_cancel (h₀.trans hf), List.ofFn_zero, List.foldl_nil, Fintype.sum_unique]
      using h
  | succ d ih =>
    obtain ⟨l, tail, rfl⟩ := split_positive bits (by omega)
    let smaller := List.replicate l true ++ false :: tail
    let scan := 4 * l + 3
    let rest := fuel - scan
    have hs : smaller.length = w := by simpa [smaller] using hw
    have hv : value smaller = d := by
      have := value_decrement l tail
      dsimp [smaller]; omega
    have hl : l ≤ w := by simp at hw; omega
    have hb : repeatBudget w B (d + 1) = repeatBudget w B d + (4 * w + B + 3) :=
      Nat.succ_mul ..
    have hsum : repeatBudget w B d + scan + B ≤ fuel := by
      rw [hb] at hf
      dsimp [scan]; omega
    obtain ⟨cost, hcost, hbody⟩ := callback x smaller rest hs (by dsimp [rest]; omega)
    have follow (i : I) := ih smaller hs hv (next x i) (rest - cost i)
      (by have := hcost i; dsimp [rest]; omega)
    choose later hlater hloop using follow
    let delay (z : Fin (d + 1) → I) := scan + cost (z 0) + later (z 0) (Fin.tail z)
    refine ⟨delay, fun z => ?_, fun c => ?_⟩
    · have := hlater (z 0) (Fin.tail z)
      have := hcost (z 0)
      dsimp only [delay, scan]; rw [hb]; omega
    · have hscan := count_positive src tmp hne body c (bank x) l rest tail
      rw [show rest + (4 * l + 3) = fuel by dsimp [rest, scan]; omega] at hscan
      rw [hscan, hbody, sum_traces_succ]
      apply Finset.sum_congr rfl
      intro i _
      rw [hloop i c]
      apply Finset.sum_congr rfl
      intro z _
      simp only [delay, Fin.cons_zero, Fin.tail_cons, List.ofFn_succ, Fin.cons_succ,
        List.foldl_cons, rest, Nat.sub_sub, Nat.add_assoc]

end EvaluatorDigitCallbacks

end VPVNP
end Computability
end OAI
