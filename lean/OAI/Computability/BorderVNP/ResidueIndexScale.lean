import OAI.Computability.BorderVNP.ParseBatchRawWord

/-! # Binary multiplication of the Laurent index fields by the fixed extraction power -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueIndex

open VPVNP.VerifierNetwork ParseBatchSort ParseRecords
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open scoped Classical

variable {I : Type*} [Fintype I] {w : ℕ}

private def digit (q : ℕ) (i : I) : Fin w → Expr ((I × Fin w) ⊕ (I × Fin w)) :=
  let acc : Fin w → Expr ((I × Fin w) ⊕ (I × Fin w)) := fun j => .input (.inr (i,j))
  let src : Fin w → Expr ((I × Fin w) ⊕ (I × Fin w)) := fun j => .input (.inl (i,j))
  if q % 2 = 1 then addWord (doubleWord acc) src else doubleWord acc

/-- Horner multiplication of every word by the same fixed `t`-bit natural number.
Each Horner step has its own gates and shares the preceding accumulator. -/
noncomputable def scale (I : Type*) [Fintype I] (w : ℕ) :
    ℕ → ℕ → Frame (I × Fin w) (I × Fin w)
  | 0, _ => (Frame.initial id).step fun _ => .const false
  | t+1, q => (scale I w t (q / 2)).withInput.step fun (i,j) => digit q i j

/-- Horner multiplication recovers the exact natural product whenever it fits the word. -/
theorem scale_value (t q : ℕ) (x : I × Fin w → Bool) (i : I)
    (hq : q < 2^t) (h : q * value (fun j => x (i,j)) < 2^w) :
    value (fun j => (scale I w t q).eval x (i,j)) = q * value (fun j => x (i,j)) := by
  induction t generalizing q with
  | zero =>
    have : q = 0 := by simpa using hq
    subst q
    simp only [scale, Frame.step_eval, StatementCircuit.Expr.eval, Nat.zero_mul]
    simpa using bigValue_testBit w 0
  | succ t ih =>
    let a := value (fun j => x (i,j))
    let prev := scale I w t (q/2)
    let z := prev.withInput.eval x
    let acc : Fin w → Expr ((I × Fin w) ⊕ (I × Fin w)) := fun j => .input (.inr (i,j))
    let src : Fin w → Expr ((I × Fin w) ⊕ (I × Fin w)) := fun j => .input (.inl (i,j))
    have hm := Nat.mod_add_div q 2
    have he : q / 2 < 2^t := by rw [pow_succ] at hq; omega
    have hsmall : (q/2) * a ≤ q * a := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
    have ha := ih (q/2) he (hsmall.trans_lt h)
    have hacc : wordValue z acc = (q/2) * a := by
      simpa [wordValue,z,acc,prev,StatementCircuit.Expr.eval,a] using ha
    have hsrc : wordValue z src = a := by simp [wordValue,z,src,a,StatementCircuit.Expr.eval]
    have hd : 2 * ((q/2) * a) ≤ q*a := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    have hdouble := doubleWord_value z acc (by rw [hacc]; exact hd.trans_lt h)
    rw [hacc] at hdouble
    change value (fun j => ((prev.withInput.step (fun (k,l) => digit q k l)).eval x (i,j))) = q*a
    simp only [Frame.step_eval, digit]
    split_ifs with hp
    · change wordValue z (addWord (doubleWord acc) src) = q*a
      have heq : 2 * ((q/2)*a) + a = q*a := by
        calc
          _ = (2*(q/2)+1)*a := by ring
          _ = q*a := by congr 1; omega
      rw [addWord_value z _ _ (by rw [hdouble,hsrc,heq]; exact h),hdouble,hsrc,heq]
    · change wordValue z (doubleWord acc) = q*a
      rw [hdouble, ← Nat.mul_assoc]
      congr 1
      omega

omit [Fintype I] in
private theorem digit_size (q : ℕ) (i : I) (j : Fin w) :
    (digit q i j).size ≤ 64*(w+1) := by
  unfold digit
  split
  · exact (sumWord_size_le false _ _ 1 (fun l => doubleWord_size_le _ 1 (fun _ => le_rfl) l)
      (fun _ => le_rfl) j).trans (by omega)
  · exact (doubleWord_size_le _ 1 (fun _ => le_rfl) j).trans (by omega)

/-- All coordinate products use at most a cubic number of gates in word width and a
linear number in the number of input coordinates. -/
theorem scale_size (t q : ℕ) :
    (scale I w t q).size ≤ (t+1) * (Fintype.card I * w * (64*(w+1))) := by
  induction t generalizing q with
  | zero =>
    refine ((Frame.initial (id : I × Fin w → I × Fin w)).step_size_le _ 1
      (fun _ => le_rfl)).trans ?_
    simp only [Frame.initial_size,Fintype.card_prod,Fintype.card_fin,zero_add,one_mul,mul_one]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  | succ t ih =>
    have hh := (scale I w t (q/2)).withInput.step_size_le
      (fun (i,j) => digit q i j) (64*(w+1)) (fun (i,j) => digit_size q i j)
    simp only [Frame.withInput_size,Fintype.card_prod,Fintype.card_fin] at hh
    exact hh.trans ((Nat.add_le_add_right (ih (q/2)) _).trans_eq
      (Nat.succ_mul (t+1) _).symm)

end ResidueIndex

end BorderVNP
end Computability
end OAI
