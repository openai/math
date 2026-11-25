import OAI.Computability.BorderVNP.CrossingSignedModes
import OAI.Computability.VPVNP.VerifierMachineNetwork
import OAI.Computability.VPVNP.BitSlotIndex

/-!
# Boolean circuits for integer multiplicities on fermion paths

A local choice of a derivative and a mode specifies a binomial coefficient with a sign.
Its magnitude can be large even when the set of coefficient addresses is polynomial.
We compare a guessed binary integer against the selected magnitude, using a formula of
linear size in its bit width for each address. Summing the two signed outputs over the
guesses recovers the integer exactly.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed.Lookup

open VPVNP.VerifierNetwork (Frame)
open VPVNP.Compression (bitWordFinEquiv)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open scoped BigOperators

/-- Most-significant-bit-first numbering of a Boolean guess. -/
def number (b : ℕ) : (Fin b → Bool) ≃ Fin (2^b) :=
  ((Equiv.refl (Fin b)).arrowCongr finTwoEquiv.symm).trans (bitWordFinEquiv b)

private theorem number_succ (b : ℕ) (x : Fin (b+1) → Bool) :
    (number (b+1) x).val = (number b (Fin.tail x)).val + 2^b * (x 0).toNat := by
  have h (y : Bool) : (finTwoEquiv.symm y).val = y.toNat := by cases y <;> rfl
  exact (VPVNP.Compression.bitWordFinEquiv_val b (fun i => finTwoEquiv.symm (x i))).trans
    (congrArg (fun d => (number b (Fin.tail x)).val + 2^b*d) (h (x 0)))

/-- Compare the given guess wires with a fixed natural-number threshold. -/
def less {σ : Type*} : (b : ℕ) → (Fin b → σ) → ℕ → Expr σ
  | 0, _, n => .const (decide (0 < n))
  | b+1, g, n =>
    if n ≤ 2^b then .and (.not (.input (g 0))) (less b (Fin.tail g) n)
    else .or (.not (.input (g 0))) (less b (Fin.tail g) (n - 2^b))

/-- Semantic correctness of the binary comparison, including the top cutoff `2^b`. -/
theorem less_eval {σ : Type*} (b : ℕ) (g : Fin b → σ) (n : ℕ) (x : σ → Bool) :
    (less b g n).eval x = decide ((number b (x ∘ g)).val < n) := by
  induction b generalizing n with
  | zero => rfl
  | succ b ih =>
    rw [less, number_succ]
    have ht : (number b (x ∘ Fin.tail g)).val < 2^b := (number b _).isLt
    change _ = decide ((number b (x ∘ Fin.tail g)).val + 2^b * (x (g 0)).toNat < n)
    split_ifs with hn <;> cases hx : x (g 0) <;>
      simp only [Expr.eval, hx, ih, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and,
        Bool.true_or, Bool.false_or, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
        Nat.add_zero] <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega

/-- The comparator uses at most three expression nodes per guessed bit. -/
theorem less_size {σ : Type*} (b : ℕ) (g : Fin b → σ) (n : ℕ) : (less b g n).size ≤ 3*b + 1 := by
  induction b generalizing n with
  | zero => simp [less, Expr.size]
  | succ b ih =>
    rw [less]
    have hn := ih (Fin.tail g) n
    have hs := ih (Fin.tail g) (n-2^b)
    split_ifs <;> simp only [Expr.size] <;> omega

variable {I σ : Type*} [Fintype I]

private def hasSign (v : ℤ) (neg : Bool) : Prop := if neg then v < 0 else 0 < v

private instance (v : ℤ) (neg : Bool) : Decidable (hasSign v neg) := by unfold hasSign; infer_instance

/-- Positive or negative accepting output of an integer table with one selected address. -/
noncomputable def entry (z : I → ℤ) (sel : I → Expr σ) (b : ℕ) (g : Fin b → σ) (neg : Bool) : Expr σ :=
  Expr.disjoin (Finset.univ.toList.map fun i =>
    if hasSign (z i) neg then .and (sel i) (less b g (z i).natAbs) else .const false)

/-- The chosen integer contributes its requested sign exactly below its magnitude. -/
theorem entry_eval [DecidableEq I] (z : I → ℤ) (sel : I → Expr σ) (b : ℕ) (g : Fin b → σ)
    (x : σ → Bool) (i : I) (hx : ∀ j, (sel j).eval x = decide (i = j)) (neg : Bool) :
    (entry z sel b g neg).eval x = decide ((if neg then z i < 0 else 0 < z i) ∧
      (number b (x ∘ g)).val < (z i).natAbs) := by
  change _ = decide (hasSign (z i) neg ∧ (number b (x ∘ g)).val < (z i).natAbs)
  apply Bool.eq_iff_iff.mpr
  simp only [entry, Expr.eval_disjoin_true, List.mem_map, Finset.mem_toList, Finset.mem_univ,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, hj⟩
    split_ifs at hj with h
    · rw [Expr.eval, hx, less_eval, Bool.and_eq_true] at hj
      obtain ⟨hj, hm⟩ := hj
      obtain rfl := of_decide_eq_true hj
      exact ⟨h, of_decide_eq_true hm⟩
    · contradiction
  · rintro ⟨hz, hn⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    rw [ite_eq_left hz, Expr.eval, hx, less_eval]
    simp [hn]

/-- The table circuit has polynomial size in its address count, selector size and bit width. -/
theorem entry_size (z : I → ℤ) (sel : I → Expr σ) (b : ℕ) (g : Fin b → σ) (neg : Bool) (a : ℕ)
    (hs : ∀ i, (sel i).size ≤ a) :
    (entry z sel b g neg).size ≤ Fintype.card I * (a + 3*b + 3) + 1 := by
  unfold entry
  apply (Expr.size_disjoin_le _ (a+3*b+2) ?_).trans
  · simp [Nat.add_assoc]
  · intro e he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    split_ifs <;> simp only [Expr.size] <;> have := hs i <;> have := less_size b g (z i).natAbs <;> omega

/-- The standalone lookup gate block with Boolean outputs for each sign. -/
noncomputable def frame (z : I → ℤ) (b : ℕ) : Frame (I ⊕ Fin b) Bool :=
  (Frame.initial id).step (entry z (fun i => .input (.inl i)) b Sum.inr)

/-- Number of gates of the signed lookup block. -/
theorem frame_size (z : I → ℤ) (b : ℕ) : (frame z b).size ≤ 2 * (Fintype.card I * (1+3*b+3) + 1) := by
  simpa only [frame, Frame.initial_size, Nat.zero_add, Fintype.card_bool] using
    Frame.step_size_le (Frame.initial id) (entry z (fun i => Expr.input (Sum.inl i)) b Sum.inr) _
      (fun neg => entry_size z _ b _ neg 1 (fun _ => le_rfl))

private theorem sign_difference (v : ℤ) (r : ℕ) :
    ((decide (0 < v ∧ r < v.natAbs)).toNat : ℤ) - (decide (v < 0 ∧ r < v.natAbs)).toNat =
      signedGuess v r := by
  by_cases hr : r < v.natAbs
  · rcases lt_trichotomy v 0 with hv | rfl | hv
    · simp [hr, hv, hv.not_gt, signedGuess, Int.sign_eq_neg_one_of_neg]
    · simp [signedGuess]
    · simp [hr, hv, hv.not_gt, signedGuess, Int.sign_eq_one_of_pos]
  · simp [hr, signedGuess]

/-- Recover the exact integer entry by summing signed acceptances over all bit assignments. -/
theorem frame_sum [DecidableEq I] (z : I → ℤ) (b : ℕ) (i : I) (hb : (z i).natAbs ≤ 2^b) :
    ∑ x : Fin b → Bool,
      ((((frame z b).eval (Sum.elim (fun j => decide (i = j)) x) false).toNat : ℤ) -
        ((frame z b).eval (Sum.elim (fun j => decide (i = j)) x) true).toNat) = z i := by
  have he (x : Fin b → Bool) (neg : Bool) := entry_eval z (fun j => Expr.input (Sum.inl j)) b
    Sum.inr (Sum.elim (fun j => decide (i = j)) x) i (fun _ => rfl) neg
  change _ = z i
  calc
    _ = ∑ x : Fin b → Bool, signedGuess (z i) (number b x).val := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [frame, Frame.step_eval]
      have hi : (Frame.initial (id : I ⊕ Fin b → I ⊕ Fin b)).eval (Sum.elim (fun j => decide (i = j)) x) =
          Sum.elim (fun j => decide (i = j)) x := funext (fun j => Frame.initial_eval _ _ j)
      rw [hi, he x false, he x true]
      exact sign_difference (z i) (number b x).val
    _ = ∑ k : Fin (2^b), signedGuess (z i) k.val := (number b).sum_comp (fun k => signedGuess (z i) k.val)
    _ = z i := by rw [Fin.sum_univ_eq_sum_range, sum_signedGuess hb]

end Crossing.Signed.Lookup

end BorderVNP
end Computability
end OAI
