import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! # Euclidean reduction with charged quotient/remainder calls

The input integers in this procedure have been constructed by the algorithm.
Each division appears in the trace and its implementation cost is charged
separately. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- A deterministic callback returning the two outputs of division. Only
calls with positive divisor need satisfy the specification. -/
structure EuclidDivider where
  run : ℕ → ℕ → ℕ × ℕ
  spec (a b : ℕ) (hb : 0 < b) :
    a = (run a b).2 + b * (run a b).1 ∧ (run a b).2 < b

/-- The mathematical reference implementation of the callback. Its invocation
cost is supplied by the caller, just as for any other divider. -/
def natEuclidDivider : EuclidDivider where
  run a b := (a / b, a % b)
  spec a b hb := ⟨(Nat.mod_add_div a b).symm, Nat.mod_lt a hb⟩

/-- The sequence of all quotient/remainder calls, in execution order. -/
inductive EuclidTrace (D : EuclidDivider) : ℕ → ℕ → ℕ → List (ℕ × ℕ) → Prop
  | done (a : ℕ) : EuclidTrace D a 0 a []
  | next {a b g : ℕ} {calls : List (ℕ × ℕ)} (hb : 0 < b)
      (tail : EuclidTrace D b (D.run a b).2 g calls) :
      EuclidTrace D a b g ((a,b) :: calls)

/-- Execute Euclid's algorithm using the supplied divider and record its inputs. -/
def euclidRun (D : EuclidDivider) (a b : ℕ) : ℕ × List (ℕ × ℕ) :=
  if _hb : b = 0 then (a, []) else
    let tail := euclidRun D b (D.run a b).2
    (tail.1, (a,b) :: tail.2)
termination_by b
decreasing_by exact (D.spec a b (Nat.pos_of_ne_zero _hb)).2

theorem euclidRun_trace (D : EuclidDivider) (a b : ℕ) :
    EuclidTrace D a b (euclidRun D a b).1 (euclidRun D a b).2 := by
  rw [euclidRun]
  split
  · next h => subst b; exact .done _
  · next h => exact .next (Nat.pos_of_ne_zero h) (euclidRun_trace D b (D.run a b).2)
termination_by b
decreasing_by exact (D.spec a b (by omega)).2

/-- Every legal callback gives the same greatest common divisor. -/
theorem EuclidTrace.result {D : EuclidDivider} {a b g calls} (t : EuclidTrace D a b g calls) :
    g = Nat.gcd a b := by
  induction t with
  | done => simp
  | @next a b g calls hb _ ih =>
    obtain ⟨he, _⟩ := D.spec a b hb
    calc
      g = b.gcd (D.run a b).2 := ih
      _ = (D.run a b).2.gcd b := Nat.gcd_comm _ _
      _ = a.gcd b := by
        conv_rhs => rw [he, Nat.gcd_add_mul_left_left]

/-- When the divisor of a callback is at most its dividend, its remainder
is strictly less than half its dividend. This applies to the second of
every two successive calls, including in an initially unsorted pair. -/
theorem EuclidDivider.twice_remainder_lt (D : EuclidDivider) {a b : ℕ} (hb : 0 < b) (hle : b ≤ a) :
    2 * (D.run a b).2 < a := by
  obtain ⟨he, hr⟩ := D.spec a b hb
  have hq : 0 < (D.run a b).1 := by
    by_contra! h
    have hz : (D.run a b).1 = 0 := by omega
    rw [hz, Nat.mul_zero, Nat.add_zero] at he
    omega
  have hmul := Nat.le_mul_of_pos_right b hq
  omega

private theorem EuclidTrace.calls_nil_or_next {D : EuclidDivider} {a b g calls}
    (t : EuclidTrace D a b g calls) : calls = [] ∨
      ∃ tail, calls = (a,b) :: tail ∧ 0 < b ∧ EuclidTrace D b (D.run a b).2 g tail := by
  cases t with
  | done => exact Or.inl rfl
  | next hb h => exact Or.inr ⟨_, rfl, hb, h⟩

/-- A divisor having at most `k` bits causes at most `2*k` divisions. -/
theorem EuclidTrace.length_le_twice_bits {D : EuclidDivider} {a b g calls}
    (t : EuclidTrace D a b g calls) (k : ℕ) (hbits : b < 2^k) : calls.length ≤ 2*k := by
  induction k generalizing a b g calls with
  | zero =>
    have hz : b = 0 := by simpa using (show b < 1 from hbits)
    subst b
    cases t with
    | done => simp
    | next hb => omega
  | succ k ih =>
    cases t with
    | done => simp
    | @next a b g tail hb rest =>
      rcases rest.calls_nil_or_next with rfl | ⟨_, rfl, hr, rest'⟩
      · simp only [List.length_cons, List.length_nil]
        omega
      ·
        have hlt := D.twice_remainder_lt hr (D.spec a b hb).2.le
        have hbits' : (D.run b (D.run a b).2).2 < 2^k := by
          rw [pow_succ] at hbits
          omega
        have hlen := ih rest' hbits'
        simp only [List.length_cons]
        omega

/-- The bit count may be bounded uniformly across all calls by any common
upper bound on the input operands. -/
theorem EuclidTrace.bounded_inputs {D : EuclidDivider} {a b g calls}
    (t : EuclidTrace D a b g calls) {H : ℕ} (ha : a ≤ H) (hb : b ≤ H) :
    ∀ p ∈ calls, p.1 ≤ H ∧ p.2 ≤ H ∧ 0 < p.2 := by
  induction t with
  | done => simp
  | @next a b g calls hpos _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨ha, hb, hpos⟩
    · exact ih hb ((D.spec a b hpos).2.le.trans hb) p hp

/-- If a division on bounded operands costs at most `T` steps, the total
callback cost along the recorded computation is at most this quantity.
Each invocation's actual cost is counted individually. -/
theorem EuclidTrace.callback_cost {D : EuclidDivider} {a b g calls}
    (t : EuclidTrace D a b g calls) (cost : ℕ → ℕ → ℕ) {H T : ℕ}
    (ha : a ≤ H) (hb : b ≤ H) (hc : ∀ i ≤ H, ∀ j ≤ H, 0 < j → cost i j ≤ T) :
    (calls.map (fun p => cost p.1 p.2)).sum ≤ 2 * (H.log2 + 1) * T := by
  have heach : ∀ p ∈ calls, cost p.1 p.2 ≤ T := by
    intro p hp
    obtain ⟨h₁, h₂, h₃⟩ := t.bounded_inputs ha hb p hp
    exact hc _ h₁ _ h₂ h₃
  have hsum (l : List (ℕ × ℕ)) (h : ∀ p ∈ l, cost p.1 p.2 ≤ T) :
      (l.map (fun p => cost p.1 p.2)).sum ≤ l.length * T := by
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have hhead := h p (List.mem_cons_self ..)
      have htail := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      omega
  exact (hsum calls heach).trans <| Nat.mul_le_mul_right T
    (t.length_le_twice_bits _ (hb.trans_lt H.lt_log2_self))

theorem EuclidDivider.quotient_eq (D : EuclidDivider) {a b : ℕ} (hb : 0 < b) :
    (D.run a b).1 = a / b := by
  obtain ⟨he, hr⟩ := D.spec a b hb
  rw [Nat.mul_comm b] at he
  symm
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [Nat.succ_mul]
    omega

/-- The two exact divisions after Euclid produce the signed reduced numerator
and positive denominator. Their callback inputs are included in the trace. -/
structure EuclidReducedPair where
  numerator : ℤ
  denominator : ℕ
  calls : List (ℕ × ℕ)

def reduceSignedPair (D : EuclidDivider) (p : ℤ) (q : ℕ) : EuclidReducedPair :=
  let r := euclidRun D p.natAbs q
  ⟨p.sign * (D.run p.natAbs r.1).1, (D.run q r.1).1,
    r.2 ++ [(p.natAbs, r.1), (q, r.1)]⟩

/-- The postprocessing restores the sign after dividing magnitudes. -/
private theorem signed_natAbs_quotient (p : ℤ) {g : ℕ} (hg : 0 < g) (hd : g ∣ p.natAbs) :
    p.sign * ((p.natAbs / g : ℕ) : ℤ) = p / (g : ℤ) := by
  have hm : (p.sign * ((p.natAbs / g : ℕ) : ℤ)) * (g : ℤ) = p := by
    rw [mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hd, Int.sign_mul_natAbs]
  calc
    _ = ((p.sign * ((p.natAbs / g : ℕ) : ℤ)) * (g : ℤ)) / (g : ℤ) :=
      (Int.mul_ediv_cancel _ (by exact_mod_cast hg.ne')).symm
    _ = _ := congrArg (fun z : ℤ => z / (g : ℤ)) hm

/-- The returned pair equals the canonical reduced representation of the input
fraction, including negative and zero numerators. -/
theorem reduceSignedPair_correct (D : EuclidDivider) (p : ℤ) {q : ℕ} (hq : 0 < q) :
    (reduceSignedPair D p q).numerator = ((p : ℚ) / (q : ℚ)).num ∧
    (reduceSignedPair D p q).denominator = ((p : ℚ) / (q : ℚ)).den := by
  have hg := (euclidRun_trace D p.natAbs q).result
  have hpos := Nat.gcd_pos_of_pos_right p.natAbs hq
  have heq : (p : ℚ) / (q : ℚ) = mkRat p q := by
    rw [← Rat.divInt_ofNat, Rat.divInt_eq_div, Int.cast_natCast]
  simp only [reduceSignedPair, hg, D.quotient_eq hpos, heq, Rat.num_mkRat, Rat.den_mkRat,
    hq.ne', ↓reduceIte, Nat.gcd_comm q p.natAbs]
  exact ⟨signed_natAbs_quotient p hpos (Nat.gcd_dvd_left ..), True.intro⟩

/-- Include both final exact divisions in the cost of normalization. -/
theorem reduceSignedPair_callback_cost (D : EuclidDivider) (p : ℤ) {q H T : ℕ} (hq : 0 < q)
    (hpH : p.natAbs ≤ H) (hqH : q ≤ H) (cost : ℕ → ℕ → ℕ)
    (hc : ∀ i ≤ H, ∀ j ≤ H, 0 < j → cost i j ≤ T) :
    ((reduceSignedPair D p q).calls.map (fun t => cost t.1 t.2)).sum ≤
      (2 * (H.log2 + 1) + 2) * T := by
  have ht := euclidRun_trace D p.natAbs q
  have hmain := ht.callback_cost cost hpH hqH hc
  have hg := ht.result
  have hpos : 0 < (euclidRun D p.natAbs q).1 := hg ▸ Nat.gcd_pos_of_pos_right p.natAbs hq
  have hle : (euclidRun D p.natAbs q).1 ≤ H := hg ▸ (Nat.gcd_le_right _ hq).trans hqH
  have hnum := hc _ hpH _ hle hpos
  have hden := hc _ hqH _ hle hpos
  simp only [reduceSignedPair, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_mul]
  omega

end Compression
end LinearProgramming
end Optimization
end OAI
