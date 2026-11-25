import OAI.Computability.BorderVNP.ResidueEntryCircuitPower
import OAI.Computability.BorderVNP.ResidueFourierCount
import Mathlib.Algebra.MvPolynomial.Rename

/-! # One field circuit for the variable residue-matrix entry

On a valid query, subtracting the test exponent from the extraction index
gives a nonnegative integer in each coordinate. The circuit takes the bits
of those differences, the validity flag, the two field scalars and the
guessed multiplicative-grid tuple as inputs. Neither its wiring nor its
constants depend on the pin indices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueFourier

open VPVNP Homogenize ResidueBox MvPolynomial
open scoped BigOperators Classical

/-- The three scalar inputs at the end are the validity bit, the monomial
coefficient, and the row basis element, respectively. -/
abbrev EntryInput (σ : Type*) (w : ℕ) := Option σ ⊕ (Option σ × Fin w) ⊕ Fin 3

/-- Field assignment to the variable entry circuit, with zero/one encoding of bits. -/
def entryAssignment {σ K : Type*} [Field K] {w : ℕ} (x : Option σ → Kˣ)
    (bits : Option σ → Fin w → Bool) (valid : Bool) (a b : K) : EntryInput σ w → K :=
  Sum.elim (fun i => (x i : K)) (Sum.elim (fun z => if bits z.1 z.2 then 1 else 0)
    ![if valid then 1 else 0, a, b])

variable {σ ι E K : Type*} [Field E] [Field K] [Fintype K] [Fintype ι] [Fintype σ]

/-- The ordinary polynomial evaluated on guessed field tuples and binary query data.
Inverse powers on the grid use the Fermat exponent `card Kˣ - 1`. -/
noncomputable def entryPolynomial (φ : E →+* K) (q w : ℕ)
    (g : ι → MvPolynomial (Option σ) E) : MvPolynomial (EntryInput σ w) K :=
  C (((Fintype.card Kˣ : K)^Fintype.card (Option σ))⁻¹) *
    X (.inr (.inr 0)) * X (.inr (.inr 1)) * X (.inr (.inr 2)) *
    (∏ t, (rename Sum.inl (map φ (g t))) ^ (q-1)) *
    ∏ i, binaryPower (X (.inl i) ^ (Fintype.card Kˣ-1)) w (fun j => X (.inr (.inl (i,j))))

private theorem unit_inverse_power (x : Kˣ) : (x : K) ^ (Fintype.card Kˣ - 1) = (x : K)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, Nat.sub_add_cancel (Fintype.card_pos (α := Kˣ))]
  exact congrArg Units.val (pow_card_eq_one (x := x))

/-- One fixed polynomial gives the actual summand for every row, column, weight,
and grid tuple. Only valid query words need to encode the difference exponent. -/
theorem eval_entryPolynomial (φ : E →+* K) (q w : ℕ) (g : ι → MvPolynomial (Option σ) E)
    (a b : E) (e μ k : Exponent σ) (x : Option σ → Kˣ) (bits : Option σ → Fin w → Bool)
    (valid : Bool) (hv : valid = true ↔
      inShiftedBox e (sourceIndex q (k-μ)) ((q-1) * ∑ t, (g t).totalDegree))
    (hbits : valid = true → ∀ i j, bits i j = ((sourceIndex q (k-μ) i - e i).toNat).testBit j.val)
    (hwidth : (q-1) * ∑ t, (g t).totalDegree < 2^w) :
    eval (entryAssignment x bits valid (φ a) (φ b)) (entryPolynomial φ q w g) =
      pathSummand φ q g a b e μ k x := by
  let j := sourceIndex q (k-μ)
  let z := entryAssignment x bits valid (φ a) (φ b)
  have hx : z ∘ Sum.inl = fun i => (x i : K) := rfl
  have bit_eval (i : Option σ) : (eval z ∘ (fun r : Fin w => X (Sum.inr (Sum.inl (i,r))))) =
      fun r => if bits i r then 1 else 0 := by
    funext r
    rw [Function.comp_apply, eval_X]
    rfl
  change eval z _ = _
  simp only [entryPolynomial, map_mul, map_prod, map_pow, eval_C, eval_X, eval_rename,
    ← eval₂_eq_eval_map, map_binaryPower, bit_eval]
  change _ * (if valid then 1 else 0) * φ a * φ b *
    (∏ t, eval₂ φ (z ∘ Sum.inl) (g t) ^ (q-1)) *
    (∏ i, binaryPower ((x i : K)^(Fintype.card Kˣ-1)) w (fun r => if bits i r then 1 else 0)) = _
  rw [hx]
  by_cases h : valid = true
  · have he := hv.mp h
    have hpow (i : Option σ) :
        binaryPower ((x i : K)^(Fintype.card Kˣ-1)) w (fun r => if bits i r then 1 else 0) =
        (x i : K) ^ ((e - j) i) := by
      let d := (j i - e i).toNat
      have hd : (d : ℤ) = j i - e i := Int.toNat_of_nonneg (sub_nonneg.mpr (he i).1)
      have hbound : d < 2^w := by
        have hh := (he i).2
        change j i ≤ _ at hh
        omega
      rw [unit_inverse_power, show (fun r : Fin w => if bits i r then (1 : K) else 0) =
        fun r => if d.testBit r.val then 1 else 0 from by simp only [d, j, hbits h],
        binaryPower_testBit _ _ d hbound, inv_pow, ← zpow_natCast, hd, ← zpow_neg]
      congr 1
      change -(j i - e i) = e i - j i
      omega
    simp only [hpow, h, ite_true, mul_one, pathSummand, he]
    have hm := monomialValue_mul_neg x e j
    change _ * _ * _ * _ * monomialValue x (e-j) =
      _ * (_ * monomialValue x e * _ * monomialValue x (-j))
    rw [← hm]
    ring
  · simp [h, pathSummand, mt hv.mpr h]

omit [Fintype K] in
private theorem size_product {τ J : Type*} (s : Finset J) (p : J → MvPolynomial τ K) (t : ℕ)
    (h : ∀ i ∈ s, circuitSize (p i) ≤ t) :
    circuitSize (∏ i ∈ s, p i) ≤ s.card*(t+1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (circuitSize_C (σ := τ) (1 : K)).le
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, one_mul]
    have hs := ih fun j hj => h j (by simp [hj])
    have hh := h i (Finset.mem_insert_self ..)
    exact (circuitSize_binOp_le .mul ..).trans (by omega)

/-- Gate budget of the joint evaluator. It is polynomial in the chart gate
bound, the two coordinate counts and the bit widths of the field and the powers. -/
def entryGateBudget (charts coords chartSize qBits fieldBits w : ℕ) : ℕ :=
  5 + charts*(chartSize+5*qBits+1) + coords*(5*fieldBits+5*w+1)

/-- Gate count for one circuit with all exponents, both scalar factors, and the
grid point as variable inputs. -/
theorem circuitSize_entryPolynomial (φ : E →+* K) (q w s : ℕ)
    (g : ι → MvPolynomial (Option σ) E) (hg : ∀ t, circuitSize (g t) ≤ s) :
    circuitSize (entryPolynomial φ q w g) ≤ entryGateBudget
      (Fintype.card ι) (Fintype.card (Option σ)) s (q-1).size (Fintype.card Kˣ-1).size w := by
  let A := EntryInput σ w
  have gc (t : ι) : circuitSize ((rename (Sum.inl : Option σ → A) (map φ (g t)))^(q-1)) ≤
      s+5*(q-1).size := by
    apply (circuitSize_power_le ..).trans
    apply Nat.add_le_add_right
    rw [rename_eq_aeval]
    exact (circuitSize_projection_le (fun i => Sum.inl (Sum.inl i)) _).trans
      ((circuitSize_map_le φ _).trans (hg t))
  let gprod : MvPolynomial A K := ∏ t, (rename Sum.inl (map φ (g t))) ^ (q-1)
  have hgp : circuitSize gprod ≤ Fintype.card ι * (s+5*(q-1).size+1) :=
    size_product Finset.univ _ _ (fun i _ => gc i)
  let term (i : Option σ) : MvPolynomial A K := binaryPower (X (.inl i)^(Fintype.card Kˣ-1)) w
    fun r => X (.inr (.inl (i,r)))
  have tc (i : Option σ) : circuitSize (term i) ≤ 5*(Fintype.card Kˣ-1).size+5*w := by
    let y : MvPolynomial A K := X (.inl i)^(Fintype.card Kˣ-1)
    obtain ⟨c,hc⟩ := circuitSize_spec y
    have hy : HasWire c.program y := ⟨c.output,hc⟩
    obtain ⟨u, _, v, h⟩ := binaryPower_wires c.program y hy w
      (fun r => X (.inr (.inl (i,r)))) (fun _ => hasWire_var c.program _)
    have := circuitSize_le_iff.mpr ⟨_, le_rfl, ⟨u,v⟩, h⟩
    refine this.trans (Nat.add_le_add_right ?_ _)
    simpa only [circuitSize_X, Nat.zero_add] using
      circuitSize_power_le (X (.inl i) : MvPolynomial A K) (Fintype.card Kˣ-1)
  have htp : circuitSize (∏ i, term i) ≤
      Fintype.card (Option σ) * (5*(Fintype.card Kˣ-1).size+5*w+1) :=
    size_product Finset.univ term _ (fun i _ => tc i)
  have hm (f g : MvPolynomial A K) : circuitSize (f*g) ≤ circuitSize f+circuitSize g+1 :=
    circuitSize_binOp_le .mul _ _
  change circuitSize (C _ * X _ * X _ * X _ * gprod * ∏ i, term i) ≤ _
  calc
    _ ≤ circuitSize (C _ * X _ * X _ * X _) + circuitSize gprod + 1 +
        circuitSize (∏ i, term i) + 1 := (hm ..).trans (by gcongr; exact hm ..)
    _ ≤ 3 + circuitSize gprod + 1 + circuitSize (∏ i, term i) + 1 := by
      gcongr
      apply (hm ..).trans
      simp only [circuitSize_X, Nat.add_zero]
      have h₂ := hm (C (((Fintype.card Kˣ : K)^Fintype.card (Option σ))⁻¹) * X (.inr (.inr 0)))
          (X (.inr (.inr 1)))
      have h₁ := hm (C (((Fintype.card Kˣ : K)^Fintype.card (Option σ))⁻¹)) (X (.inr (.inr 0)))
      simp only [circuitSize_C, circuitSize_X, Nat.add_zero] at h₁ h₂
      omega
    _ ≤ _ := by unfold entryGateBudget; omega

/-- The circuit selected before the row, column, or grid tuple is known computes all
their summands within the same gate bound. -/
theorem exists_entryCircuit (φ : E →+* K) (q w s : ℕ)
    (g : ι → MvPolynomial (Option σ) E) (hg : ∀ t, circuitSize (g t) ≤ s)
    (hwidth : (q-1) * ∑ t, (g t).totalDegree < 2^w) :
    ∃ n ≤ entryGateBudget (Fintype.card ι) (Fintype.card (Option σ)) s
        (q-1).size (Fintype.card Kˣ-1).size w, ∃ c : Circuit K (EntryInput σ w) n,
      ∀ (a b : E) (e μ k : Exponent σ) (x : Option σ → Kˣ) (bits : Option σ → Fin w → Bool)
        (valid : Bool),
        (valid = true ↔ inShiftedBox e (sourceIndex q (k-μ)) ((q-1)*∑ t, (g t).totalDegree)) →
        (valid = true → ∀ i j, bits i j = ((sourceIndex q (k-μ) i - e i).toNat).testBit j.val) →
        c.eval id (entryAssignment x bits valid (φ a) (φ b)) =
          pathSummand φ q g a b e μ k x := by
  obtain ⟨c, hc⟩ := circuitSize_spec (entryPolynomial φ q w g)
  refine ⟨_, circuitSize_entryPolynomial φ q w s g hg, c, ?_⟩
  intro a b e μ k x bits valid hv hb
  let z := entryAssignment x bits valid (φ a) (φ b)
  have he : eval z c.polynomial = c.eval id z := by
    rw [Circuit.polynomial, Circuit.eval_hom]
    congr 1 <;> funext i <;> simp
  rw [← he, hc]
  exact eval_entryPolynomial φ q w g a b e μ k x bits valid hv hb hwidth

end ResidueFourier

end BorderVNP
end Computability
end OAI
