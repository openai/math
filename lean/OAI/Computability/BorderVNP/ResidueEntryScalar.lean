import OAI.Computability.BorderVNP.ResidueEntryVerifier

/-!
# Canonical binary encoding of an arbitrary matrix scalar

Lemma 10.1 allows any element of the finite coefficient field in a matrix query.
The input supplies its prime-field basis coordinates in binary. A linear-size
arithmetic circuit reconstructs the scalar, so one reader handles the entire
coefficient field without storing a table of its elements.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryVerifier

open ResiduePins ResidueFourier ResidueBox ResidueIndex ResidueEntryInput ResidueEntryBudget
open ResidueEntryOutput ResidueEntryVerifierCore ResidueEntryField
open VPVNP ExactQuantumFactoring MvPolynomial
open scoped BigOperators Classical

/-- Little-endian base-two reconstruction using ring-valued bits. -/
def binaryValue {R : Type*} [Ring R] : (m : ℕ) → (Fin m → R) → R
  | 0, _ => 0
  | m+1, b => 2 * binaryValue m (b ∘ Fin.succ) + b 0

/-- Reconstruct the natural numeral inside the ring, in any characteristic. -/
theorem binaryValue_bits {R : Type*} [CommRing R] (m n : ℕ) (h : n < 2^m) :
    binaryValue m (fun i => if n.testBit i.val then (1 : R) else 0) = n := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    simp [binaryValue, hn]
  | succ m ih =>
    let k := n >>> 1
    have hk : k < 2 ^ m := by rw [pow_succ] at h; exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h
    have hbits : (fun i : Fin (m+1) => if n.testBit i.val then (1:R) else 0) ∘ Fin.succ =
        (fun i => if k.testBit i.val then 1 else 0) := by
      funext i; simp [k, Nat.testBit_shiftRight, Nat.add_comm]
    have ht := n.bit_testBit_zero_shiftRight_one
    change Nat.bit (n.testBit 0) k = n at ht
    rw [binaryValue, hbits, ih _ hk]
    cases hbit : n.testBit 0 <;> simp [hbit, Nat.bit] at ht ⊢ <;> rw [← ht] <;> push_cast <;> ring

/-- Formal evaluation commutes with binary reconstruction. -/
theorem map_binaryValue {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) (m : ℕ) (b : Fin m → R) :
    φ (binaryValue m b) = binaryValue m (φ ∘ b) := by
  induction m with
  | zero => simp [binaryValue]
  | succ m ih => simp [binaryValue, ih, Function.comp_assoc, map_ofNat]

private theorem size_binaryValue {R σ : Type*} [CommRing R] (m : ℕ) (x : Fin m → σ) :
    circuitSize (binaryValue m (fun i => X (x i) : Fin m → MvPolynomial σ R)) ≤ 2*m := by
  induction m with
  | zero => simpa only [binaryValue, Nat.mul_zero, map_zero] using (circuitSize_C (σ := σ) (0:R)).le
  | succ m ih =>
    rw [binaryValue]
    let V := binaryValue m (fun i => (X (x i.succ) : MvPolynomial σ R))
    have hv : circuitSize V ≤ 2*m := ih (x ∘ Fin.succ)
    have hm := circuitSize_binOp_le .mul (C (2:R)) V
    have ha := circuitSize_binOp_le .add (C (2:R) * V) (X (x 0))
    simp only [BinOp.apply, circuitSize_C, circuitSize_X, Nat.zero_add, Nat.add_zero] at hm ha
    change circuitSize ((2 : MvPolynomial σ R) * V + X (x 0)) ≤ 2*(m+1)
    have bound : circuitSize (C (2:R) * V + X (x 0)) ≤ 2*(m+1) := by omega
    simpa only [map_ofNat] using bound

variable {σ ι E K : Type*} [Fintype σ] [Fintype ι] [Field E] [Field K] [Fintype K]
variable {p idx D d w : ℕ} [Fact p.Prime] [Algebra (ZMod p) E] [Algebra (ZMod p) K]

/-- The input coordinate words, interpreted through the field basis and embedding. -/
noncomputable def scalarPolynomial (σ : Type*) (idx m : ℕ) (BE : Module.Basis (Fin D) (ZMod p) E)
    (φ : E →+* K) : MvPolynomial (GadgetInput σ idx (Fin D) m) K :=
  ∑ j, C (φ (BE j)) * binaryValue m (fun i => X (.inr (j,i)))

omit [Fintype K] [Algebra (ZMod p) K] in
private theorem scalar_size (σ : Type*) (idx m : ℕ) (BE : Module.Basis (Fin D) (ZMod p) E)
    (φ : E →+* K) : circuitSize (scalarPolynomial σ idx m BE φ) ≤ D*(2*m+2) := by
  let term := fun j : Fin D => C (φ (BE j)) * binaryValue m
    (fun i => (X (.inr (j,i)) : MvPolynomial (GadgetInput σ idx (Fin D) m) K))
  have size_term (j : Fin D) : circuitSize (term j) ≤ 2*m+1 := by
    apply (circuitSize_binOp_le .mul ..).trans
    rw [circuitSize_C, Nat.zero_add]
    exact Nat.add_le_add_right (size_binaryValue m _) 1
  have size_sum (s : Finset (Fin D)) : circuitSize (∑ j ∈ s, term j) ≤ s.card*(2*m+2) := by
    induction s using Finset.induction_on with
    | empty => simpa using (circuitSize_C (σ := GadgetInput σ idx (Fin D) m) (0:K)).le
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.card_insert_of_notMem hj, Nat.add_mul, one_mul]
      have := size_term j
      exact (circuitSize_binOp_le .add ..).trans (by omega)
  simpa only [scalarPolynomial, term, Finset.card_univ, Fintype.card_fin] using size_sum Finset.univ

omit [Fintype σ] [Fintype K] [Algebra (ZMod p) K] in
private theorem scalar_eval (idx m : ℕ) (BE : Module.Basis (Fin D) (ZMod p) E) (φ : E →+* K)
    (a : E) (hm : p ≤ 2^m) (z : GadgetInput σ idx (Fin D) m → K)
    (hz : ∀ j i, z (.inr (j,i)) = if (BE.coord j a).val.testBit i.val then 1 else 0) :
    eval z (scalarPolynomial σ idx m BE φ) = φ a := by
  rw [scalarPolynomial, map_sum]
  conv_rhs => rw [← BE.sum_repr a, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, eval_C, map_binaryValue]
  have e : eval z ∘ (fun i : Fin m => X (.inr (j,i))) =
      (fun i => if (BE.coord j a).val.testBit i.val then 1 else 0) := by
    funext i; rw [Function.comp_apply, eval_X, hz]
  rw [e, binaryValue_bits m _ ((ZMod.val_lt _).trans_le hm)]
  change φ (BE j) * ((BE.coord j a).val : K) = φ (BE.coord j a • BE j)
  have hs : BE.coord j a • BE j = ((BE.coord j a).val : E) * BE j := by
    rw [Algebra.smul_def, ← map_natCast (algebraMap (ZMod p) E), ZMod.natCast_zmod_val]
  rw [hs, map_mul, map_natCast, mul_comm]

omit [Algebra (ZMod p) K] in
/-- One shared field circuit works for all additive-coordinate encodings of a coefficient,
all basis rows and all exponents. -/
theorem exists_scalar_dag (BE : Module.Basis (Fin D) (ZMod p) E) (φ : E →+* K)
    (q H width idx s m : ℕ) (hq : 0 < q) (hm : p ≤ 2^m)
    (hw : 2*H*q+3*H+q+width+1 < 2^idx) (g : ι → MvPolynomial (Option σ) E)
    (hwidth : width = (q-1) * ∑ t, (g t).totalDegree) (hg : ∀ t, circuitSize (g t) ≤ s) :
    ∃ n ≤ entryGateBudget (Fintype.card ι) (Fintype.card (Option σ)) s (q-1).size
        (Fintype.card Kˣ-1).size idx + D*(2*m+2)+1,
      ∃ c : Circuit K (GadgetInput σ idx (Fin D) m) n, ∀ a b : E, ∀ e μ k : Exponent σ,
        Fits H e → Fits H μ → Fits H k → ∀ x : Option σ → Kˣ,
        c.eval id (Sum.elim (queryAssignment q H width idx x (encode idx H e μ k) 1 (φ b))
          (fun (j,i) => if (BE.coord j a).val.testBit i.val then 1 else 0)) =
          pathSummand φ q g a b e μ k x := by
  let A := GadgetInput σ idx (Fin D) m
  let S := scalarPolynomial σ idx m BE φ
  obtain ⟨n, hn, c, hc⟩ := exists_rawEntryCircuit φ q H width idx s hq hw g hwidth hg
  let c' := c.subst (fun i => Sum.inl (Sum.inl i : A)) id
  obtain ⟨r, hr⟩ := circuitSize_spec S
  refine ⟨n+circuitSize S+1, Nat.add_le_add_right (Nat.add_le_add hn (scalar_size σ idx m BE φ)) _,
    c'.combine .mul r, ?_⟩
  intro a b e μ k he hμ hk x
  let y := queryAssignment q H width idx x (encode idx H e μ k) (1:K) (φ b)
  let z := Sum.elim y (fun j : Fin D × Fin m => if (BE.coord j.1 a).val.testBit j.2.val then (1:K) else 0)
  have hbase : c'.eval id z = pathSummand φ q g 1 b e μ k x := by
    simp only [c', Circuit.eval_subst, Sum.elim_inl]
    change c.eval id (queryAssignment q H width idx x (encode idx H e μ k) (1:K) (φ b)) = _
    simpa only [map_one] using hc 1 b e μ k he hμ hk x
  have hscalar : r.eval id z = φ a := by
    trans eval z r.polynomial
    · rw [Circuit.polynomial, Circuit.eval_hom]
      congr 1 <;> funext i <;> simp
    · rw [hr]
      exact scalar_eval idx m BE φ a hm z (fun _ _ => rfl)
  change (c'.combine .mul r).eval id z = _
  rw [Circuit.eval_combine, hbase, hscalar]
  simp only [BinOp.apply, pathSummand, map_one, one_mul]
  split_ifs <;> ring

end ResidueEntryVerifier

end BorderVNP
end Computability
end OAI
