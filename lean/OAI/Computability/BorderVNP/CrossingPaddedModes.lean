import OAI.Computability.BorderVNP.CrossingDualPaths

/-!
# Fixed-width witnesses for a variable derivative word

The order mask is input to the verifier. One fixed-width packet is reserved for every
possible derivative order. Inactive orders admit just the all-zero packet. This padding
allows a single Boolean circuit to evaluate any word while counting each witness once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed.Padded

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open scoped BigOperators

/-- Number of bits reserved for each of the mode and multiplicity guesses. -/
abbrev width (L : ℕ) := 2 * L + 1

/-- One mode guess, deletion bit, and multiplicity guess. -/
abbrev Packet (L : ℕ) := Bool × Fin (2 ^ width L) × Fin (2 ^ width L)

/-- Unique legal padding for an unused derivative order. -/
def padding (L : ℕ) : Packet L := (false, 0, 0)

/-- Select a creation or a deletion coefficient in either the Pascal word or the derivative word. -/
def coefficient (dual del : Bool) (m k : ℕ) : ℤ :=
  if dual then (if del then 0 else pascalCoefficient m k)
  else (if del then negativeCoefficient m k else positiveCoefficient m k)

/-- Each local coefficient fits in the prescribed multiplicity width. -/
theorem coefficient_le {L m k : ℕ} (dual del : Bool) (hm : m < L) (hk : k < L) :
    (coefficient dual del m k).natAbs ≤ 2 ^ width L := by
  have hc (a b : ℕ) (ha : a ≤ width L) : a.choose b ≤ 2 ^ width L :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) ha)
  cases dual <;> cases del <;>
    simp only [coefficient, Bool.false_eq_true, ite_true, ite_false, pascalCoefficient, negativeCoefficient,
      positiveCoefficient, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
      Int.natAbs_natCast, one_pow, one_mul, Int.natAbs_zero, Nat.zero_le]
  all_goals apply hc; unfold width; omega

/-- A packet updates the appropriate endpoint by erasing its mode if the order is active. -/
def next {L : ℕ} (active : Bool) (g : Packet L) (I J : Finset ℕ) : Finset ℕ × Finset ℕ :=
  if active then
    if g.1 then (I, J.erase g.2.1.val) else (I.erase g.2.1.val, J)
  else (I, J)

/-- Local signed acceptance of a packet, including exterior and normal-ordering signs. -/
def localWeight {L : ℕ} (dual active : Bool) (m remaining : ℕ)
    (g : Packet L) (I J : Finset ℕ) : ℤ :=
  if active then
    let k := g.2.1.val
    let S := if g.1 then J else I
    if k < L ∧ k ∈ S then
      (if g.1 then (-1 : ℤ) ^ remaining else 1) * insertionSign k (S.erase k) *
        signedGuess (coefficient dual g.1 m k) g.2.2.val
    else 0
  else if g = padding L then 1 else 0

private theorem truncate {L M : ℕ} (h : L ≤ M) (f : ℕ → ℤ) :
    (∑ k : Fin M, if k.val < L then f k.val else 0) = ∑ k : Fin L, f k.val := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.sum_univ_add]
  simp [Fin.natAdd, Fin.castAdd]

private theorem sum_packet {L m : ℕ} (hm : m < L) (dual : Bool) (remaining : ℕ) (I J : Finset ℕ)
    (f : Finset ℕ → Finset ℕ → ℤ) :
    (∑ g : Packet L, localWeight dual true m remaining g I J *
      f (next true g I J).1 (next true g I J).2) =
    ∑ dk : Bool × Fin L,
      if dk.1 then
        (if dk.2.val ∈ J then (-1 : ℤ)^remaining * coefficient dual true m dk.2.val *
          insertionSign dk.2.val (J.erase dk.2.val) * f I (J.erase dk.2.val) else 0)
      else
        (if dk.2.val ∈ I then coefficient dual false m dk.2.val * insertionSign dk.2.val
          (I.erase dk.2.val) * f (I.erase dk.2.val) J else 0) := by
  have hL : L ≤ 2 ^ width L := (Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by decide) (by unfold width; omega))
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro del _
  rw [Fintype.sum_prod_type]
  let S := if del then J else I
  let v (k : ℕ) := (if del then (-1 : ℤ)^remaining else 1) * insertionSign k (S.erase k)
  let cont (k : ℕ) := if del then f I (J.erase k) else f (I.erase k) J
  have single (k : Fin (2 ^ width L)) :
      (∑ u : Fin (2 ^ width L), localWeight dual true m remaining (del,k,u) I J *
        f (next true (del,k,u) I J).1 (next true (del,k,u) I J).2) =
      if k.val < L then (if k.val ∈ S then v k * coefficient dual del m k * cont k else 0) else 0 := by
    by_cases h : k.val < L ∧ k.val ∈ S
    · have hu : (∑ u : Fin (2 ^ width L), signedGuess (coefficient dual del m k) u.val) =
            coefficient dual del m k := by
          rw [Fin.sum_univ_eq_sum_range, sum_signedGuess (coefficient_le dual del hm h.1)]
      cases del <;> simp_all [localWeight, v, cont, S, next, ← Finset.sum_mul, ← Finset.mul_sum]
    · cases del <;> simp_all [localWeight, S]
  simp_rw [single]
  rw [truncate hL (fun k => if k ∈ S then v k * coefficient dual del m k * cont k else 0)]
  apply Finset.sum_congr rfl
  intro k _
  cases del <;> simp only [S, v, cont, Bool.false_eq_true, ite_false, ite_true, one_mul] <;>
    split_ifs <;> ring

/-- List of actual factors in the order mask, omitting all inactive orders. -/
def word {L : ℕ} (dual : Bool) (A : Finset ℕ) (ms : List ℕ) :
    List ((Fin L → ℤ) × (Fin L → ℤ)) :=
  (ms.filter (· ∈ A)).map fun m =>
    (fun k => coefficient dual false m k, fun k => coefficient dual true m k)

/-- A witness with a fixed packet at each candidate order. -/
def value {L : ℕ} (dual : Bool) (A : Finset ℕ) : (ms : List ℕ) →
    (Fin ms.length → Packet L) → Finset ℕ → Finset ℕ → ℤ
  | [], _, I, J => if J = I then 1 else 0
  | m :: ms, gs, I, J =>
    let active := decide (m ∈ A)
    let ij := next active (gs 0) I J
    localWeight dual active m (ms.filter (· ∈ A)).length (gs 0) I J *
      value dual A ms (Fin.tail gs) ij.1 ij.2

/-- Summing fixed-width signed guesses gives the same coefficient as the sparse normally ordered word. -/
theorem value_sum {L : ℕ} (dual : Bool) (A : Finset ℕ) (ms : List ℕ)
    (hms : ∀ m ∈ ms, m < L) (I J : Finset ℕ) :
    (∑ gs : Fin ms.length → Packet L, value dual A ms gs I J) =
      ∑ p : ModePath L (word (L := L) dual A ms).length, modeWeight (word dual A ms) p I J := by
  induction ms generalizing I J with
  | nil =>
    change (∑ _ : Fin 0 → Packet L, if J = I then (1 : ℤ) else 0) =
      ∑ _ : Unit, if J = I then (1 : ℤ) else 0
    simp
  | cons m ms ih =>
    have htail := ih (fun a ha => hms _ (List.mem_cons_of_mem _ ha))
    change (∑ gs : Fin (ms.length + 1) → Packet L, value dual A (m :: ms) gs I J) = _
    rw [← (Fin.consEquiv (fun _ : Fin (ms.length+1) => Packet L)).sum_comp
      (fun gs => value dual A (m::ms) gs I J), Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, value, Fin.cons_zero, Fin.tail_cons, ← Finset.mul_sum]
    by_cases ha : m ∈ A
    · simp only [ha, decide_true]
      rw [sum_packet (hms m List.mem_cons_self) dual _ I J
        (fun U V => ∑ gs : Fin ms.length → Packet L, value dual A ms gs U V)]
      let a : (Fin L → ℤ) × (Fin L → ℤ) := (fun k => coefficient dual false m k, fun k => coefficient dual true m k)
      have he : word (L := L) dual A (m :: ms) = a :: word dual A ms := by
        simp [word, ha, a]
      have hr := congrArg (fun s : List ((Fin L → ℤ) × (Fin L → ℤ)) =>
        ∑ p : ModePath L s.length, modeWeight s p I J) he
      refine Eq.trans ?_ hr.symm
      change _ = ∑ p : (Bool × Fin L) × ModePath L (word dual A ms).length, _
      conv_rhs => rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      rintro ⟨del,k⟩ _
      cases del <;> simp only [modeWeight, Bool.false_eq_true, ite_true, ite_false]
      all_goals split_ifs <;> simp [← Finset.mul_sum, htail, a, word]
    · have he : word (L := L) dual A (m :: ms) = word dual A ms := by
        simp [word, ha]
      have hr := congrArg (fun s : List ((Fin L → ℤ) × (Fin L → ℤ)) =>
        ∑ p : ModePath L s.length, modeWeight s p I J) he
      rw [← htail I J] at hr
      simpa [ha, localWeight, next] using hr.symm

end Crossing.Signed.Padded

end BorderVNP
end Computability
end OAI
