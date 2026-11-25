import OAI.Computability.BorderVNP.CrossingMaskCounter
import OAI.Computability.VPVNP.JointScalarCore

/-!
# Boolean circuits for the scalar part of the crossing modes

The mode, the two endpoint energies and the source grade have polynomially many possible
values. One lookup enforces the energy shift and supplies the integer mark coefficient
or the bare orientation sign. The exterior-state paths are supplied by the word circuits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed.CoefficientFrame

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open VPVNP.VerifierNetwork (Frame)
open VPVNP.JointScalar (parallel parallel_eval parallel_size)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open scoped BigOperators

/-- Integer contributed by positive and negative Boolean outputs. -/
def value (o : Bool → Bool) : ℤ := (o false).toNat - ((o true).toNat : ℤ)

/-- Multiply signed Boolean outputs by combining the like and unlike sign pairs. -/
noncomputable def times {X : Type*} [Fintype X] (f g : Frame X Bool) : Frame X Bool :=
  (parallel f g).step fun neg => .or (.and (.input (.inl false)) (.input (.inr neg)))
    (.and (.input (.inl true)) (.input (.inr (!neg))))

/-- Product law even if both output flags are true. -/
theorem times_value {X : Type*} [Fintype X] (f g : Frame X Bool) (x : X → Bool) :
    value ((times f g).eval x) = value (f.eval x) * value (g.eval x) := by
  simp only [times, value, Frame.step_eval, Expr.eval, parallel_eval, Sum.elim_inl, Sum.elim_inr,
    Bool.not_false, Bool.not_true]
  cases f.eval x false <;> cases f.eval x true <;> cases g.eval x false <;> cases g.eval x true <;> decide

/-- Number of additional gates needed to multiply two signed output pairs. -/
theorem times_size {X : Type*} [Fintype X] (f g : Frame X Bool) :
    (times f g).size ≤ f.size + g.size + 14 := by
  apply (Frame.step_size_le (parallel f g) _ 7 (fun _ => le_rfl)).trans
  simp

/-- A quadratic upper bound for every doubled energy in an `L`-mode Fock space. -/
abbrev cap (L : ℕ) := L * (2*L+1)

/-- Inputs to the scalar circuit, in the order mode, source, output and input masks. -/
abbrev Query (L W : ℕ) := Fin W ⊕ Fin L ⊕ Fin L ⊕ Fin L

/-- The three unary grade/energy indices of a scalar lookup. -/
abbrev Grades (L : ℕ) := Fin (cap L+1) × Fin (cap L+1) × Fin (cap L+1)

/-- Bits required for the scalar multiplicity. -/
abbrev bits (L W : ℕ) := W + cap L + 1

private def sourceWeight (marked : Bool) (i : ℕ) : ℕ := if marked then 2*i+1 else 1

private def grade {L : ℕ} (marked : Bool) (A : Index L) : ℕ :=
  ∑ i ∈ A.val, sourceWeight marked i

private theorem grade_le {L : ℕ} (marked : Bool) (A : Index L) : grade marked A ≤ cap L := by
  calc
    grade marked A ≤ ∑ _ ∈ A.val, (2*L+1) := by
      apply Finset.sum_le_sum
      intro i hi
      have := Finset.mem_range.mp (Finset.mem_powerset.mp A.property hi)
      cases marked
      · simp [sourceWeight]
      · simp [sourceWeight]; omega
    _ ≤ _ := by
      have h := Finset.card_le_card (Finset.mem_powerset.mp A.property)
      simpa [cap] using Nat.mul_le_mul_right (2*L+1) h

private def scalar {L W : ℕ} (marked : Bool) (k : Fin W × Grades L) : ℤ :=
  if (k.2.2.1.val : ℤ) - k.2.2.2.val = (if marked then shift W k.1 else -(shift W k.1)) then
    if marked then markCoefficient W k.2.1.val k.1 else (-1) ^ (k.2.1.val * (k.2.1.val-1) / 2)
  else 0

private theorem scalar_bound {L W : ℕ} (marked : Bool) (k : Fin W × Grades L) :
    (scalar marked k).natAbs ≤ 2 ^ bits L W := by
  cases marked with
  | false =>
    simp only [scalar, Bool.false_eq_true, ite_false]
    split_ifs
    · simpa using (Nat.one_le_two_pow : 1 ≤ 2 ^ bits L W)
    · simp
  | true =>
    simp only [scalar, ite_true]
    split_ifs
    · simp only [markCoefficient, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
        one_pow, one_mul, Int.natAbs_natCast]
      exact (Nat.choose_le_two_pow _ _).trans
        (Nat.pow_le_pow_right (by decide) (by have := k.2.1.isLt; unfold bits; omega))
    · simp

private abbrev Graded (L W : ℕ) := Fin W ⊕ Fin (cap L+1) ⊕ Fin (cap L+1) ⊕ Fin (cap L+1)

private abbrev Bus (L W : ℕ) := Graded L W ⊕ Fin (bits L W)

private noncomputable def energies (L W : ℕ) (marked : Bool) : Frame (Query L W) (Graded L W) := by
  exact parallel (Frame.initial Sum.inl) (parallel
    ((MaskCounter.counters (cap L) (fun i : Fin L => sourceWeight marked i)).subst
      (Frame.initial (fun i => Sum.inr (Sum.inl i)))) (parallel
    ((MaskCounter.energy L).subst (Frame.initial (fun i => Sum.inr (Sum.inr (Sum.inl i)))))
    ((MaskCounter.energy L).subst (Frame.initial (fun i => Sum.inr (Sum.inr (Sum.inr i)))))))

private def chooseAddress {L W : ℕ} (i : (Fin W × Grades L) ⊕ Fin (bits L W)) : Expr (Bus L W) :=
  match i with
  | .inl (r,a,i,j) => .and (.and (.input (.inl (.inl r))) (.input (.inl (.inr (.inl a)))))
      (.and (.input (.inl (.inr (.inr (.inl i))))) (.input (.inl (.inr (.inr (.inr j))))))
  | .inr j => .input (.inr j)

private noncomputable def addresses (L W : ℕ) (marked : Bool) :
    Frame (Query L W ⊕ Fin (bits L W)) ((Fin W × Grades L) ⊕ Fin (bits L W)) :=
  (parallel ((energies L W marked).subst (Frame.initial Sum.inl)) (Frame.initial Sum.inr)).step chooseAddress

/-- The actual signed Boolean program for the scalar multiplying an operator entry. -/
noncomputable def frame (L W : ℕ) (marked : Bool) : Frame (Query L W ⊕ Fin (bits L W)) Bool :=
  (Lookup.frame (scalar (L := L) (W := W) marked) (bits L W)).subst (addresses L W marked)

/-- Assignment describing the selected mode and three Fock-space basis states. -/
def query {L W : ℕ} (r : Fin W) (A I J : Index L) : Query L W → Bool :=
  Sum.elim (fun s => decide (r = s)) (Sum.elim (MaskCounter.mask A)
    (Sum.elim (MaskCounter.mask I) (MaskCounter.mask J)))

private def key {L W : ℕ} (marked : Bool) (r : Fin W) (A I J : Index L) : Fin W × Grades L :=
  (r, ⟨grade marked A, Nat.lt_succ_of_le (grade_le marked A)⟩,
    ⟨doubledEnergy I.val, Nat.lt_succ_of_le (grade_le true I)⟩,
    ⟨doubledEnergy J.val, Nat.lt_succ_of_le (grade_le true J)⟩)

private theorem grade_eval {L W : ℕ} (marked : Bool) (r : Fin W) (A I J : Index L) :
    (energies L W marked).eval (query r A I J) =
      Sum.elim (fun s => decide (r = s)) (Sum.elim (fun a => decide (grade marked A = a.val))
        (Sum.elim (fun i => decide (doubledEnergy I.val = i.val)) (fun j => decide (doubledEnergy J.val = j.val)))) := by
  funext u
  rcases u with s | a | i | j
  · simp [energies, query]
  · simp only [energies, parallel_eval, Sum.elim_inr, Sum.elim_inl, Frame.subst_eval]
    have he : (Frame.initial (fun k : Fin L => Sum.inr (Sum.inl k))).eval (query r A I J) =
        MaskCounter.mask A := funext (fun k => Frame.initial_eval _ _ k)
    rw [he, MaskCounter.counters_eval, MaskCounter.total_index]
    rfl
  · simp only [energies, parallel_eval, Sum.elim_inr, Sum.elim_inl, Frame.subst_eval]
    have he : (Frame.initial (fun k : Fin L => Sum.inr (Sum.inr (Sum.inl k)))).eval (query r A I J) =
        MaskCounter.mask I := funext (fun k => Frame.initial_eval _ _ k)
    rw [he, MaskCounter.energy_eval]
  · simp only [energies, parallel_eval, Sum.elim_inr, Frame.subst_eval]
    have he : (Frame.initial (fun k : Fin L => Sum.inr (Sum.inr (Sum.inr k)))).eval (query r A I J) =
        MaskCounter.mask J := funext (fun k => Frame.initial_eval _ _ k)
    rw [he, MaskCounter.energy_eval]

private theorem addresses_eval {L W : ℕ} (marked : Bool) (r : Fin W) (A I J : Index L)
    (x : Fin (bits L W) → Bool) :
    (addresses L W marked).eval (Sum.elim (query r A I J) x) =
      Sum.elim (fun t => decide (key marked r A I J = t)) x := by
  have he : (Frame.initial (Sum.inl : Query L W → Query L W ⊕ Fin (bits L W))).eval
      (Sum.elim (query r A I J) x) = query r A I J := funext (fun j => Frame.initial_eval _ _ j)
  funext u
  rcases u with ⟨s,a,i,j⟩ | k
  · simp [addresses, chooseAddress, Expr.eval, he, grade_eval, key, Prod.ext_iff, Fin.ext_iff, Bool.and_assoc]
  · simp [addresses, chooseAddress, Expr.eval]

/-- The scalar in the two energy-filtered operator modes. -/
def multiplier {L W : ℕ} (marked : Bool) (r : Fin W) (A I J : Index L) : ℤ :=
  if (doubledEnergy I.val : ℤ) - doubledEnergy J.val = (if marked then shift W r else -shift W r) then
    if marked then markCoefficient W (doubledEnergy A.val) r else dualSign A.val
  else 0

/-- Summing the signed scalar witnesses enforces exactly the energy shift, binomial mark,
or bare-state orientation sign used in the coefficient tables. -/
theorem frame_sum {L W : ℕ} (marked : Bool) (r : Fin W) (A I J : Index L) :
    ∑ x : Fin (bits L W) → Bool, value ((frame L W marked).eval (Sum.elim (query r A I J) x)) =
      multiplier marked r A I J := by
  simp only [frame, value, Frame.subst_eval, addresses_eval]
  rw [Lookup.frame_sum _ _ _ (scalar_bound marked _)]
  cases marked <;> simp [scalar, key, multiplier, grade, sourceWeight, doubledEnergy, dualSign]

/-- Polynomial scalar circuit bound in the three energies, the mode address count and the
binary multiplicity width. -/
theorem frame_size (L W : ℕ) (marked : Bool) :
    (frame L W marked).size ≤
      3*((L+cap L+1) + L*((L+cap L+1)*8)) +
      (W*(cap L+1)^3+bits L W)*7 + 2*(W*(cap L+1)^3*(1+3*bits L W+3)+1) := by
  let c := (L+cap L+1) + L*((L+cap L+1)*8)
  have hs : (energies L W marked).size ≤ 3*c := by
    simp only [energies, parallel_size, Frame.initial_size, Frame.subst_size, Nat.zero_add]
    have h1 := MaskCounter.counters_size (cap L) (fun i : Fin L => sourceWeight marked i)
    have h2 := MaskCounter.counters_size (cap L) (fun i : Fin L => 2*i.val+1)
    change _ + (_ + _) ≤ 3*c
    change (MaskCounter.energy L).size ≤ c at h2
    change (MaskCounter.counters _ _).size ≤ c at h1
    omega
  have hc : Fintype.card (Fin W × Grades L) = W*(cap L+1)^3 := by
    simp only [Grades, Fintype.card_prod, Fintype.card_fin]
    ring
  have ha := Frame.step_size_le
    (parallel ((energies L W marked).subst (Frame.initial Sum.inl)) (Frame.initial Sum.inr))
    chooseAddress 7 (fun i => by cases i with
      | inl p => exact le_rfl
      | inr j => change 1 ≤ 7; decide)
  simp only [parallel_size, Frame.subst_size, Frame.initial_size, Nat.zero_add, Nat.add_zero,
    Fintype.card_sum, Fintype.card_fin, hc] at ha
  have hl := Lookup.frame_size (scalar (L := L) (W := W) marked) (bits L W)
  rw [hc] at hl
  change (addresses L W marked).size ≤ _ at ha
  rw [frame, Frame.subst_size]
  omega

end Crossing.Signed.CoefficientFrame

end BorderVNP
end Computability
end OAI
