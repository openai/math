import OAI.Computability.VPVNP.FixedLabelReadback
import OAI.Computability.VPVNP.ParseOracleRun

/-!
# The two counted scalar queries of Section 8.1

The joint reader uses the same fixed counting machine with two choices of
Boolean circuit advice. One circuit counts the incidence words for a parse
histogram, and one counts the zero-padded witnesses of the universal machine.
A grammar exponent too large for the degree of the queried polynomial
returns zero before invoking the counter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointLabelSystem

open MvPolynomial PrimedStackRAM RadicalCertificate.MonomialIndex UniversalCountStack
open RAMTape

/-- The binary output in the count stack of the fixed enumerator. -/
noncomputable def countBits {u w g : ℕ} (c : BooleanTranscript.Circuit (Fin u ⊕ Fin w) g)
    (x : Fin u → Bool) : List Bool :=
  digits (w + 1) (∑ bits, (c.eval (Sum.elim x bits)).toNat)

theorem countBits_runs {u w g : ℕ} (c : BooleanTranscript.Circuit (Fin u ⊕ Fin w) g)
    (x : Fin u → Bool) :
    ∃ t ≤ 2 ^ w * perChoice c, SpaceRun countCircuit.standalone (stackLimit c) t
      (some countCircuit.entry) (bank (scalarInputs c x) (digits w 0) (digits (w + 1) 0) [] []) none
      (bank (scalarInputs c x) (digits w 0) (countBits c x) [] []) := countCircuit_runs c x

/-- The constant coefficient is read from the clocked path-count query. -/
noncomputable def pathScalar {n : ℕ} (x : Fin n → Bool) : ℕ :=
  TapeWord.value (countBits (VerifierMachine.verifierCircuit n) x)

theorem pathScalar_eq {n : ℕ} (x : Fin n → Bool) : pathScalar x = acceptingCount x := by
  unfold pathScalar countBits
  simp only [VerifierMachine.verifierCircuit_eval]
  have h := acceptingCount_eq_sum_witnesses (R := ℕ) x
  simp only [Nat.cast_id] at h
  have hs : (∑ bits, (verifiesInput x bits).toNat) = acceptingCount x := by
    rw [h]
    exact Finset.sum_congr rfl fun bits _ => by cases verifiesInput x bits <;> rfl
  rw [hs, count_digits_value]

/-- The production-counter callback uses `2n` bits per queried exponent.
Larger exponents cannot occur in a degree-`2n-1` parse monomial. -/
noncomputable def parseScalar {n : ℕ} (hn : 2 ≤ n) (c : ℕ) (x : Fin n → Bool)
    (z : Fin (FixedRows.productionCount n c) → ℕ) : ℤ :=
  if ∀ j, z j < 2 ^ (2*n) then
    let checker := ParseOracle.checker (⟨n - 1, by omega⟩ : Fin n)
      (⟨0, pow_pos (by omega) _⟩ : Fin (n ^ (c + 5))) (labelIndex n n _) (2*n)
    TapeWord.value (countBits checker (ParseOracle.query x z (2*n)))
  else 0

theorem parseScalar_eq {n : ℕ} (hn : 2 ≤ n) (c : ℕ) (x : Fin n → Bool)
    (e : Production n c →₀ ℕ) :
    parseScalar hn c x (fun i => e ((labelIndex n n _).symm i)) =
      (labelQuery (⟨n - 1, by omega⟩ : Fin n) (⟨0, pow_pos (by omega) _⟩ : Fin (n ^ (c+5))) x).coeff e := by
  let d : Fin n := ⟨n-1, by omega⟩
  let h : Fin (n^(c+5)) := ⟨0, pow_pos (by omega) _⟩
  let f := labelIndex n n (n^(c+5))
  let z := fun i => e (f.symm i)
  by_cases hz : ∀ i, z i < 2^(2*n)
  · rw [parseScalar, ite_eq_left hz]
    change (TapeWord.value (digits (ParseOracle.Flags n n _ + 1)
      (∑ bits, ((ParseOracle.checker d h f (2*n)).eval (Sum.elim (ParseOracle.query x z (2*n)) bits)).toNat)) : ℤ) = _
    rw [ParseOracle.count_checker d h f x z (fun l => hz (f l)) e (fun l => by simp [z])]
    exact ParseOracle.coefficient_query_value d h x e
  · rw [parseScalar, ite_eq_right hz]
    by_contra he
    apply hz
    intro i
    have hm := monomial_le_degreeOf (f.symm i) (mem_support_iff.mpr (Ne.symm he))
    have hD := (degreeOf_le_totalDegree (labelQuery d h x) (f.symm i)).trans (labelQuery_isHomogeneous d h x).totalDegree_le
    exact (hm.trans (hD.trans (show 2*d.val+1 ≤ 2*n by dsimp [d]; omega))).trans_lt Nat.lt_two_pow_self

namespace FixedRows

variable (V I : Type*) [Fintype V] [Fintype I] (F : I → MvPolynomial V ℤ) {n : ℕ}

/-- Integer coefficient lookup with both counted callbacks instantiated by
the outputs of the fixed circuit enumerator. -/
noncomputable def countedCoeff (hn : 2 ≤ n) (c : ℕ) :
    Fin (2^n + Fintype.card I) → (Fin (labelTotal V n c) → ℕ) → ℤ :=
  readAdvice (orderAdvice V n c) (fixedTable V I F ∘ (Fintype.equivFin _).symm)
    (parseScalar hn c) pathScalar

theorem countedCoeff_eq (hn : 2 ≤ n) (c : ℕ) (i : Fin (2^n + Fintype.card I))
    (a : Fin (labelTotal V n c) → ℕ) :
    countedCoeff V I F hn c i a = (unionEquations (grammarEquation hn c) F (rowIndex I n i)).coeff
      (exponentVector a) :=
  (readAdvice_eq_getCoeff V I F n c _ _ i a).trans (getCoeff_eq V I F n c hn
    (parseScalar hn c) (parseScalar_eq hn c) pathScalar pathScalar_eq i a)

end FixedRows
end JointLabelSystem

end VPVNP
end Computability
end OAI
