import OAI.Optimization.LinearProgramming.Compression.PowerTape

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

private theorem digitOps_append (xs ys : List Bool) :
    digitOps (xs ++ ys) = digitOps xs ++ digitOps ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [digitOps, ih]

theorem digitOps_length (bs : List Bool) : (digitOps bs).length ≤ 2 * bs.length := by
  induction bs with
  | nil => simp [digitOps]
  | cons b bs ih => cases b <;> simp only [digitOps, List.length_cons] <;> omega

theorem termOps_length (e : ℤ) : (termOps e).length ≤ 2 * e.natAbs.size + 3 := by
  have h := digitOps_length e.natAbs.bits.reverse
  rw [List.length_reverse, Nat.size_eq_bits_len] at h
  unfold termOps
  split <;> simp only [List.length_cons, List.length_append, List.length_nil] <;> omega

theorem productOps_length (es : List ℤ) :
    (productOps es).length ≤ (es.map fun e => 2 * e.natAbs.size + 3).sum := by
  induction es with
  | nil => simp [productOps]
  | cons e es ih =>
    change ((termOps e ++ productOps es).length) ≤ _
    simpa only [List.length_append, List.map_cons, List.sum_cons] using
      Nat.add_le_add (termOps_length e) ih

/-- Counts the intermediate power and also the scalar base when the exponent is zero. -/
def powerTermBudget (p : ℚ × ℤ) : ℕ := 3 + (p.2.natAbs + 1) * ratBits p.1

private theorem digitOps_run {B : ℕ} (q y : ℚ) (qs : List ℚ) (bs : List Bool)
    (hq : ratBits q ≤ B) (hy : ratBits y ≤ B) (hqs : ∀ x ∈ qs, ratBits x ≤ B)
    (hp : ∀ k ≤ exponentDigits bs, ratBits (q^k) ≤ B) :
    PowerRun (PowerMem.fits B) (digitOps bs.reverse)
      ⟨q,1,y,qs⟩ ⟨q,q^(exponentDigits bs),y,qs⟩ := by
  induction bs with
  | nil =>
    have h := hp 0 le_rfl
    simpa [exponentDigits, digitOps] using
      (PowerRun.nil (PowerMem.mk q 1 y qs) ⟨hq, by simpa using h, hy, hqs⟩ :
        PowerRun (PowerMem.fits B) [] _ _)
  | cons b bs ih =>
    let n := exponentDigits bs
    have h₂ : 2*n ≤ exponentDigits (b::bs) := by simp [exponentDigits, n, Nat.bit_val]
    have hn : n ≤ exponentDigits (b::bs) := by omega
    have prevRun := ih (fun k hk => hp k (hk.trans hn))
    have hbefore : PowerMem.fits B ⟨q, q^n, y, qs⟩ := ⟨hq, hp _ hn, hy, hqs⟩
    have hsq : q^n*q^n = q^(2*n) := by rw [two_mul, pow_add]
    have hmid : PowerMem.fits B ⟨q,q^(2*n),y,qs⟩ := ⟨hq, hp _ h₂, hy, hqs⟩
    have hfinal : PowerMem.fits B ⟨q,q^(exponentDigits (b::bs)),y,qs⟩ :=
      ⟨hq, hp _ le_rfl, hy, hqs⟩
    rw [List.reverse_cons, digitOps_append]
    apply prevRun.append
    cases b with
    | false =>
      refine .cons hbefore ?_ (.nil _ hfinal)
      simpa [PowerOp.step, exponentDigits, Nat.bit_val, n] using
        congrArg (fun z => some (PowerMem.mk q z y qs)) hsq
    | true =>
      refine .cons (n := ⟨q,q^(2*n),y,qs⟩) hbefore ?_ (.cons hmid ?_ (.nil _ hfinal))
      · exact congrArg (fun v => some (PowerMem.mk q v y qs)) hsq
      · simp [PowerOp.step, exponentDigits, Nat.bit_val, pow_succ, n]

private theorem termOps_run {B : ℕ} (m : PowerMem) (q : ℚ) (e : ℤ) (qs : List ℚ)
    (hm : m.fits B) (hrem : m.remaining = q :: qs) (hnz : e < 0 → q ≠ 0)
    (hterm : powerTermBudget (q,e) ≤ B) (hprod : ratBits (m.product * q^e) ≤ B) :
    PowerRun (PowerMem.fits B) (termOps e) m ⟨q,q^e,m.product * q^e,qs⟩ := by
  have hq : ratBits q ≤ B := hm.2.2.2 q (by simp [hrem])
  have hqs : ∀ z ∈ qs, ratBits z ≤ B := fun z hz => hm.2.2.2 z (by simp [hrem,hz])
  have hp (k : ℕ) (hk : k ≤ e.natAbs) : ratBits (q^k) ≤ B :=
    (ratBits_natPow_le q k).trans ((Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (hk.trans (Nat.le_succ _))) _).trans hterm)
  have hd := digitOps_run q m.product qs e.natAbs.bits hq hm.2.2.1 hqs
    (by simpa only [exponentDigits_bits] using hp)
  rw [exponentDigits_bits] at hd
  have he : ratBits (q^e) ≤ B := (ratBits_intPow_le q e).trans
    ((Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _).trans hterm)
  have hpos : PowerMem.fits B ⟨q,q^e.natAbs,m.product,qs⟩ :=
    ⟨hq, hp _ le_rfl, hm.2.2.1, hqs⟩
  have hpow : PowerMem.fits B ⟨q,q^e,m.product,qs⟩ := ⟨hq,he,hm.2.2.1,hqs⟩
  have hfinal : PowerMem.fits B ⟨q,q^e,m.product*q^e,qs⟩ := ⟨hq,he,hprod,hqs⟩
  refine .cons hm (by simp [PowerOp.step,hrem]) (hd.append ?_)
  by_cases hneg : e < 0
  · rw [ite_eq_left hneg]
    have hh : (q^e.natAbs)⁻¹ = q^e := by
      cases e with
      | ofNat n => exact ((Int.natCast_nonneg n).not_gt hneg).elim
      | negSucc n => simp [zpow_negSucc]
    refine .cons hpos ?_ (.cons hpow rfl (.nil _ hfinal))
    simp [PowerOp.step, pow_ne_zero _ (hnz hneg), hh]
  · rw [ite_eq_right hneg]
    have hh : q^e.natAbs = q^e := by
      cases e with
      | ofNat n => simp
      | negSucc n => omega
    rw [hh]
    exact .cons hpow rfl (.nil _ hfinal)

private theorem productOps_run_from {B : ℕ} (m : PowerMem) (ps : List (ℚ × ℤ))
    (hm : m.fits B) (hrem : m.remaining = ps.map Prod.fst)
    (hnz : ∀ p ∈ ps, p.2 < 0 → p.1 ≠ 0)
    (hbudget : ratBits m.product + (ps.map powerTermBudget).sum ≤ B) :
    ∃ z, PowerRun (PowerMem.fits B) (productOps (ps.map Prod.snd)) m z ∧
      z.product = m.product * (ps.map fun p => p.1^p.2).prod ∧ z.remaining = [] := by
  induction ps generalizing m with
  | nil => exact ⟨m, .nil _ hm, by simp, by simpa using hrem⟩
  | cons p ps ih =>
    rcases p with ⟨q,e⟩
    let cost := powerTermBudget (q,e)
    let tail := (ps.map powerTermBudget).sum
    change ratBits m.product + (cost + tail) ≤ B at hbudget
    have hterm : cost ≤ B := by omega
    have he : ratBits (q^e) ≤ cost := (ratBits_intPow_le q e).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _)
    have hprod := (ratBits_mul_le_add m.product (q^e)).trans (Nat.add_le_add_left he _)
    have prefixRun := termOps_run m q e _ hm hrem (hnz (q,e) (by simp)) hterm (by omega)
    obtain ⟨z, hz, hval, hrest⟩ := ih _ prefixRun.safe_end rfl
      (fun p hp => hnz p (List.mem_cons_of_mem _ hp)) (by change ratBits (m.product*q^e) + tail ≤ B; omega)
    refine ⟨z,prefixRun.append hz,?_,hrest⟩
    simpa [mul_assoc] using hval

/-- The opcode stream generated from the explicit signed integers consumes every supplied
base, returns the product of powers, and keeps every live scalar within the encoding bound. -/
theorem productOps_run (ps : List (ℚ × ℤ)) (hnz : ∀ p ∈ ps, p.2 < 0 → p.1 ≠ 0) :
    ∃ z, PowerRun (PowerMem.fits (3 + (ps.map powerTermBudget).sum))
      (productOps (ps.map Prod.snd)) (PowerMem.initial (ps.map Prod.fst)) z ∧
      z.product = (ps.map fun p => p.1^p.2).prod ∧ z.remaining = [] := by
  let B := 3 + (ps.map powerTermBudget).sum
  have hB : 3 ≤ B := Nat.le_add_right _ _
  have hb : (PowerMem.initial (ps.map Prod.fst)).fits B := by
    refine ⟨hB,hB,hB,?_⟩
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have hle : powerTermBudget p ≤ (ps.map powerTermBudget).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨p,hp,rfl⟩)
    have hs : ratBits p.1 ≤ powerTermBudget p := by unfold powerTermBudget; rw [Nat.add_mul]; omega
    omega
  obtain ⟨z,hz,hr,hrest⟩ := productOps_run_from _ ps hb rfl hnz le_rfl
  exact ⟨z,hz,by simpa [PowerMem.initial] using hr,hrest⟩

end Compression
end LinearProgramming
end Optimization
end OAI
