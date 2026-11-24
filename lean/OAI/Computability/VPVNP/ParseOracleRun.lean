import OAI.Computability.VPVNP.ParseOracleCircuit
import OAI.Computability.VPVNP.UniversalCountQuery

/-!
# Deterministic stack execution of the grammar coefficient query

One fixed bit-stack control enumerates event flags and evaluates the advised circuit
on the word and binary histogram coordinates. The output stack contains the full
integer coefficient in little-endian binary. The supplied advice depends on the
table dimensions, root and coordinate ordering, independently of the queried values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseOracle

open ParseGrammar UniversalCountStack RAMTape

variable {m D L W : ℕ} {H : Type} [Fintype H]
open scoped Classical

/-- The number of candidate event flags, one for each bounded event code on the paired
variables and grammar states. -/
abbrev Flags (m D : ℕ) (H : Type) [Fintype H] := Fintype.card (EventCode (Var m) H D)

/-- Circuit supplied as advice. Its ordered gate stream is independent of both
the input word and the queried monomial. -/
noncomputable def checker (d : Fin D) (h : H) (addr : Label m D H → Fin L) (W : ℕ) :=
  (frame (parseOracleMetadata (Var m) H D d h) addr W).circuit ()

theorem count_checker (d : Fin D) (h : H) (addr : Label m D H → Fin L)
    (x : Fin m → Bool) (z : Fin L → ℕ) (hz : ∀ l, z (addr l) < 2^W)
    (e : Label m D H →₀ ℕ) (he : ∀ l, z (addr l) = e l) :
    (∑ flags, ((checker d h addr W).eval (Sum.elim (query x z W) flags)).toNat) =
      ((labelQuery d h x).coeff e).toNat := by
  let M := parseOracleMetadata (Var m) H D d h
  rw [coeff_labelQuery_eq_flagCount, Int.toNat_natCast, Finset.card_filter]
  refine Finset.sum_congr rfl fun flags _ ↦ ?_
  have ok : (checker d h addr W).eval (Sum.elim (query x z W) flags) = true ↔
      M.Accepts (pairedExponent x) e flags := by
    rw [checker, VerifierNetwork.Frame.circuit_eval]
    exact frame_eval_iff M addr x z hz e he flags
  cases hb : (checker d h addr W).eval (Sum.elim (query x z W) flags) <;> simp [hb] at ok
  · simp only [M] at ok; simp [ok]
  · simp only [M] at ok; simp [ok]

/-- Space and per-candidate time hold along every intermediate machine step.
The accepting flags are counted once each, including when several have the
same histogram. -/
theorem coefficient_query_runs (d : Fin D) (h : H) (addr : Label m D H → Fin L)
    (x : Fin m → Bool) (z : Fin L → ℕ) (hz : ∀ l, z (addr l) < 2^W)
    (e : Label m D H →₀ ℕ) (he : ∀ l, z (addr l) = e l) :
    let c := checker d h addr W
    let k := Flags m D H
    let aux := scalarInputs c (query x z W)
    ∃ t ≤ 2^k * perChoice c,
      SpaceRun countCircuit.standalone (stackLimit c) t (some countCircuit.entry)
        (bank aux (digits k 0) (digits (k+1) 0) [] []) none
        (bank aux (digits k 0) (digits (k+1) ((labelQuery d h x).coeff e).toNat) [] []) := by
  simpa only [count_checker d h addr x z hz e he] using
    countCircuit_runs (checker d h addr W) (query x z W)

/-- The result bits represent the full integer, since the number of satisfying flag
words is at most two to the width of the enumeration. -/
theorem coefficient_query_value (d : Fin D) (h : H) (x : Fin m → Bool) (e : Label m D H →₀ ℕ) :
    (TapeWord.value (digits (Flags m D H+1) ((labelQuery d h x).coeff e).toNat) : ℤ) =
      (labelQuery d h x).coeff e := by
  classical
  rw [coeff_labelQuery_eq_flagCount, Int.toNat_natCast, value_digits, Nat.mod_eq_of_lt]
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin (Flags m D H) → Bool))
    ((parseOracleMetadata (Var m) H D d h).Accepts (pairedExponent x) e)
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact h.trans_lt (by rw [pow_succ]; have := Nat.pow_pos (n := Flags m D H) (by decide : 0 < 2); omega)

end ParseOracle

end VPVNP
end Computability
end OAI
