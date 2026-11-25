import OAI.Computability.NearSquareRoot.CommonAlphabetAlignRewind
import OAI.Computability.NearSquareRoot.CommonAlphabetAlignRun
import OAI.Computability.NearSquareRoot.CommonAlphabetAlignSpace

/-! # Distinct physical space for the folded output-position wrapper -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Align

open IntegerMultiplication TM
variable {A Q I : Type}
variable (out : I) (blank marker : A)

private theorem tracks_running (neg : Bool) (x : Config A Q I) :
    Tracks out x (running out blank marker neg x) :=
  tracks_exact _ _ _ (fun _ => rfl) rfl

variable [DecidableEq I]

private theorem tracks_ret (neg : Bool) (x : Config A Q I)
    (sign : (x.tape out).pos ≠ 0 → neg = decide ((x.tape out).pos < 0))
    (n : ℕ) (hn : n ≤ (x.tape out).pos.natAbs) :
    Tracks out x (ret out blank marker neg x n) := by
  have endPos := side_natAbs (x.tape out).pos neg sign
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  · simp [ret,banks,outputAt,hi]
  · simp only [ret,banks,outputAt,↓reduceIte,Reset.atHead]
    cases neg <;> simp only [side, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  · simp only [ret,banks,outputAt,↓reduceIte,Reset.atHead]
    cases neg <;> simp only [side, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_le.mpr hn

private theorem tracks_final (x : Config A Q I) : Tracks out x (final out blank x) := by
  exact ⟨fun i hi => by simp [final,banks,outputAt,hi],
    by simp [final,banks,outputAt,Reset.atHead],
    by simp [final,banks,outputAt,Reset.atHead],le_rfl,Int.natCast_nonneg _⟩

variable [DecidableEq A] (entry : Q) (m : Rule A Q I)
local notation "M" => rule out blank marker entry m

/-- A partial rewind uses exactly as many steps as its decrease in unsigned distance. -/
theorem rewind_prefix (hne : blank ≠ marker) (neg : Bool) (v : Config A Q I) (n k : ℕ) (hk : k ≤ n) :
    Trace (advance M) (ret out blank marker neg v n) k (ret out blank marker neg v (n-k)) := by
  induction k generalizing n with
  | zero => simpa only [Nat.sub_zero] using Trace.nil (step := advance M) (ret out blank marker neg v n)
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      simpa only [Nat.succ_sub_succ_eq_sub, Nat.add_comm 1] using
        Trace.cons (rewindStep out blank marker entry m hne neg v n) (ih n (by omega))

/-- After the old machine halts, each prefix charges the other tapes to their
final old cells and charges the two moving heads to the old output path. -/
theorem tracks_unwind (hne : blank ≠ marker) (neg : Bool) (v : Config A Q I) (halt : advance m v = none)
    (sign : (v.tape out).pos ≠ 0 → neg = decide ((v.tape out).pos < 0))
    {k : ℕ} {z} (hk : k ≤ (v.tape out).pos.natAbs+2)
    (tr : Trace (advance M) (running out blank marker neg v) k z) : Tracks out v z := by
  cases k with
  | zero =>
    obtain rfl := trace_endpoint_unique tr (.nil _)
    exact tracks_running out blank marker neg v
  | succ k =>
    have enter := dispatch out blank marker entry m neg v halt sign
    by_cases going : k ≤ (v.tape out).pos.natAbs
    · have sub := rewind_prefix out blank marker entry m hne neg v _ k going
      obtain rfl := trace_endpoint_unique tr (by simpa only [Nat.add_comm 1] using Trace.cons enter sub)
      exact tracks_ret out blank marker neg v sign _ (Nat.sub_le ..)
    · obtain rfl : k = (v.tape out).pos.natAbs+1 := by omega
      have done := unwind out blank marker entry m hne neg v (v.tape out).pos.natAbs
      obtain rfl := trace_endpoint_unique tr (by simpa only [Nat.add_comm 1] using Trace.cons enter done)
      exact tracks_final out blank v

/-- The whole physical boot, execution, rewind and sentinel cleanup occupy at
most twice the number of distinct cells visited by the original machine. -/
theorem visits (hne : blank ≠ marker) (m : Rule A Q I) {x y : Config A Q I} {n cells : ℕ}
    (zero : (x.tape out).pos = 0) (run : Trace (advance m) x n y) (halt : advance m y = none)
    (space : VisitsAtMost m x n cells) :
    VisitsAtMost (rule out blank marker x.pc m) (initial x blank)
      (n+(y.tape out).pos.natAbs+3) (2*cells) := by
  obtain ⟨neg,sign,checkLast⟩ := checkpoint out blank marker hne m zero run
  have cover := visits_of_segments (machine := rule out blank marker x.pc m) out zero space run
    (start := initial x blank) (last := running out blank marker neg y)
    (back := (y.tape out).pos.natAbs+2)
    (tracks_exact _ _ _ (fun _ => rfl) (by change (0 : ℤ) = _; rw [zero]; rfl)) (fun k hk => ?_)
    checkLast
    (fun _ hk _ tail => tracks_unwind out blank marker x.pc m hne neg y halt sign hk tail)
  · convert cover using 1
    omega
  · obtain ⟨v,old,_⟩ := trace_split run hk
    obtain ⟨sn,_,steps⟩ := checkpoint out blank marker hne m zero old
    exact ⟨v,_,old,steps,tracks_running _ _ _ sn _⟩

end CommonAlphabet.Align

end NearSquareRoot
end Computability
end OAI
