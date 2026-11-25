import OAI.Computability.BorderVNP.Diagonal
import OAI.Computability.BorderVNP.ParseTable
import OAI.Computability.BorderVNP.SignedFamily

/-!
# Substitution in the signed contraction

The two physical contractions in (11.1) have the same topology. A link has a
single summation index, a literal has its prescribed value, and a pin bit is
read at its prescribed processor position. The full degree-component table
is kept until the substitution into the query polynomial.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open MvPolynomial
open scoped BigOperators Classical

/-- A physical bit position holds a literal, a bit from the extra pin field,
or a link shared with another processor. -/
inductive InputSlot (Pin Wire : Type*) where
  | literal (bit : Bool)
  | pin (index : Pin)
  | link (index : Wire)

/-- Read one physical input position for a fixed pin and link assignment. -/
def InputSlot.read {Pin Wire : Type*} (pins : Pin → Bool) (links : Wire → Bool) :
    InputSlot Pin Wire → Bool
  | .literal bit => bit
  | .pin i => pins i
  | .link i => links i

variable {Pin Wire Proc : Type*} [Fintype Wire] [Fintype Proc] {n : ℕ}

/-- A link assignment and pin value address one coefficient of the full
degree-`n` table at each processor. -/
noncomputable def pairedQuery (layout : Proc → Fin n → InputSlot Pin Wire)
    (pins : Pin → Bool) (links : Wire → Bool) (proc : Proc) :
    DegreeMonomial (Fin n × Bool) n :=
  ⟨VPVNP.pairedExponent (fun j => (layout proc j).read pins links),
    by simp [VPVNP.pairedExponent, Finsupp.degree_single]⟩

/-- The integer live value `Z` includes the signs and the actual clock in
each processor's universal machine. -/
noncomputable def signedContraction (layout : Proc → Fin n → InputSlot Pin Wire)
    (pins : Pin → Bool) : ℤ :=
  ∑ links, ∏ proc, signedCount (fun j => (layout proc j).read pins links)

/-- Expanding each processor into its canonical choices recovers the signed
sum over the physical links and independent local machine paths. -/
theorem signedContraction_eq_paths (layout : Proc → Fin n → InputSlot Pin Wire)
    (pins : Pin → Bool) :
    signedContraction layout pins =
      ∑ links, ∑ w : Proc → Fin (n ^ 100) → Bool,
        ∏ proc, signedWitness (fun j => (layout proc j).read pins links) (w proc) := by
  simp only [signedContraction, signedCount_eq_sum_witnesses, Fintype.prod_sum]

/-- The live contraction is the evaluation of exactly the polynomial used
for substitution, at the coefficients of the signed universal family. -/
theorem live_eq_eval {K : Type*} [CommRing K]
    (layout : Proc → Fin n → InputSlot Pin Wire) (pins : Pin → Bool) :
    (signedContraction layout pins : K) =
      eval (coeffVector n (map (Int.castRingHom K) (Pstar n)))
        (queryPolynomial K (pairedQuery layout pins)) := by
  rw [eval_queryPolynomial]
  simp [signedContraction, coeffVector, pairedQuery, coeff_map]

/-- For each pin, compose its query polynomial with the universal integral
parse table and then take coefficients in the chosen characteristic. -/
noncomputable def substituted (K : Type*) [CommRing K] (k s : ℕ)
    (layout : Proc → Fin (k + 1) → InputSlot Pin Wire) (pins : Pin → Bool) :
    MvPolynomial
      (VPVNP.GrammarLabel (Fin (k + 1) × Bool) (ParseTable.State (Fin (k + 1) × Bool) s) (k + 1)) K :=
  ∑ links, ∏ proc,
    map (Int.castRingHom K) (ParseTable.table _ k s (pairedQuery layout pins links proc))

/-- Each processor contributes one coordinate of degree at most `2n−1`,
where `n=k+1`, before the links are summed. -/
theorem substituted_degree_le (K : Type*) [CommRing K] (k s : ℕ)
    (layout : Proc → Fin (k+1) → InputSlot Pin Wire) (pins : Pin → Bool) :
    (substituted K k s layout pins).totalDegree ≤ Fintype.card Proc * (2*k+1) := by
  apply totalDegree_finsetSum_le
  intro links _
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _proc : Proc, (2*k+1) := by
      apply Finset.sum_le_sum
      intro proc _
      let f := ParseTable.table _ k s (pairedQuery layout pins links proc)
      have hmap : (map (Int.castRingHom K) f).totalDegree ≤ f.totalDegree :=
        Finset.sup_mono (support_map_subset _ _)
      exact hmap.trans (ParseTable.coordinate_degree ..)
    _ = _ := by simp

/-- The bound `L = R h (2^b−1)` chosen in Section 11 covers each full row
polynomial using the prescribed exponent width. -/
theorem substituted_degree_budget (K : Type*) [CommRing K] (k s r R h : ℕ) (hh : 1 ≤ h)
    (layout : (Fin R × Fin r) → Fin (k+1) → InputSlot Pin Wire) (pins : Pin → Bool) :
    (substituted K k s layout pins).totalDegree ≤
      R * h * (2 ^ Nat.clog 2 (r * (2*k+1) + 1) - 1) := by
  apply (substituted_degree_le ..).trans
  have hclog := Nat.le_pow_clog (by decide : 1 < 2) (r * (2*k+1) + 1)
  have hw : r * (2*k+1) ≤ 2 ^ Nat.clog 2 (r * (2*k+1) + 1) - 1 := by omega
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_assoc]
  exact (Nat.mul_le_mul_left _ hw).trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hh))

/-- Evaluating a substituted contraction at one assignment of the table
parameters gives the evaluation of its query polynomial on the table output. -/
theorem eval_substituted {K : Type*} [CommRing K] (k s : ℕ)
    (layout : Proc → Fin (k + 1) → InputSlot Pin Wire) (pins : Pin → Bool)
    (v : VPVNP.GrammarLabel (Fin (k + 1) × Bool)
      (ParseTable.State (Fin (k + 1) × Bool) s) (k + 1) → K) :
    eval v (substituted K k s layout pins) =
      eval (fun e => eval₂ (Int.castRingHom K) v (ParseTable.table _ k s e))
        (queryPolynomial K (pairedQuery layout pins)) := by
  simp only [substituted, map_sum, map_prod, eval_map, eval_queryPolynomial]

/-- If the signed polynomial is in the border image, all live pin values
belong *jointly* to the closure of the substituted contractions. One common
parameter assignment supplies every coordinate of that image. -/
theorem live_mem_substitutedClosure {K : Type*} [Field K] {k s : ℕ}
    (layout : Proc → Fin (k + 1) → InputSlot Pin Wire)
    (h : geometricApprox (k + 1) s (map (Int.castRingHom K) (Pstar (k + 1)))) :
    (fun pins => (signedContraction layout pins : K)) ∈
      imageClosure (Set.range (fun v pins => eval v (substituted K k s layout pins))) := by
  have htable := ParseTable.geometricApprox_mem_tableClosure _ h
  have hjoint := imageClosure_polynomial htable
    (fun pins => queryPolynomial K (pairedQuery layout pins))
  simp_rw [← live_eq_eval] at hjoint
  apply imageClosure_mono _ hjoint
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  exact ⟨v, funext (eval_substituted k s layout · v)⟩

end Diagonal

end BorderVNP
end Computability
end OAI
