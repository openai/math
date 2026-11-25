import OAI.Computability.BorderVNP.ResidueEntryField
import OAI.Computability.QuantumFactoring.ArithmeticPredicates
import OAI.Computability.QuantumFactoring.BooleanFold
import OAI.Computability.VPVNP.PolynomialBounds

/-! # Binary selection of residue basis elements and linear projections

The row index chooses one advised basis element and the column index chooses one
prime-field coordinate functional. Both indices are ordinary little-endian words.
Selection scans only the basis dimension, irrespective of the field cardinality.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryBasis

open ExactQuantumFactoring BooleanNetwork BitArithmetic BorderVNP.ResidueEntryField

variable {n r m D d w p : ℕ}

private def addressMatch (addr : Fin r → Fin n) (i : Fin D) : BooleanNetwork n 1 :=
  ((select addr).pair (literal n r i.val)).comp (wordEq r)

private theorem matches_eval (hr : D ≤ 2^r) (addr : Fin r → Fin n) (x : Fin n → Bool) (i : Fin D) :
    (addressMatch addr i).eval x 0 = true ↔ value (x ∘ addr) = i.val := by
  rw [addressMatch,eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq,eval_select]
  change bitsValue (x ∘ addr) = bitsValue ((wordConstant (.ofNat r i.val)).eval x) ↔ _
  rw [wordConstant_eval]
  change bitsValue (x ∘ addr) = BitVec.ofNat r i.val ↔ (bitsValue (x ∘ addr)).toNat = i.val
  have hi := i.isLt.trans_le hr
  constructor
  · intro e; rw [e,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hi]
  · intro e; exact BitVec.eq_of_toNat_eq (by rw [e,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hi])

private theorem matches_count (addr : Fin r → Fin n) (i : Fin D) :
    (addressMatch addr i).net.count ≤ 97*r+21 := by
  have h := wordEq_count r
  simp only [addressMatch,count_comp,count_pair,count_select,literal,wordConstant_count]
  omega

/-- Scan all `D` possible binary indices and select the matching supplied output word.
Every bit is zero when the input index exceeds the last row. -/
def indexed (addr : Fin r → Fin n) (rows : Fin D → BooleanNetwork n m) : BooleanNetwork n m :=
  vector fun b => any (List.ofFn fun i =>
    (addressMatch addr i).band ((rows i).rewire fun _ => b))

/-- Precise bitwise semantics, valid even on an out-of-range row. -/
theorem indexed_eval (hr : D ≤ 2^r) (addr : Fin r → Fin n) (rows : Fin D → BooleanNetwork n m)
    (x : Fin n → Bool) (b : Fin m) :
    (indexed addr rows).eval x b = true ↔ ∃ i : Fin D, value (x ∘ addr) = i.val ∧
      (rows i).eval x b = true := by
  simp only [indexed,eval_vector,any_eval,List.mem_ofFn,exists_exists_eq_and,eval_band,
    Bool.and_eq_true,matches_eval hr,eval_rewire,Function.comp_apply]

/-- At a given in-range index the whole selected word equals the corresponding row. -/
theorem indexed_at (hr : D ≤ 2^r) (addr : Fin r → Fin n) (rows : Fin D → BooleanNetwork n m)
    (x : Fin n → Bool) (i : Fin D) (hi : value (x ∘ addr) = i.val) :
    (indexed addr rows).eval x = (rows i).eval x := by
  funext b
  apply Bool.eq_iff_iff.mpr
  rw [indexed_eval hr,hi]
  constructor
  · rintro ⟨j,h,hb⟩
    exact Fin.ext h ▸ hb
  · intro h; exact ⟨i,rfl,h⟩

/-- The lookup gate cost is polynomial in both table dimensions, the address width,
and the maximum gate count of a supplied row. -/
def lookupBudget (D m r s : ℕ) := m*(D*(97*r+s+26)+1)

/-- Polynomially many rows of polynomial width and cost give polynomial lookup size. -/
theorem polynomiallyBounded_lookupBudget {D m r s : ℕ → ℕ}
    (hD : VPVNP.PolynomiallyBounded D) (hm : VPVNP.PolynomiallyBounded m)
    (hr : VPVNP.PolynomiallyBounded r) (hs : VPVNP.PolynomiallyBounded s) :
    VPVNP.PolynomiallyBounded fun n => lookupBudget (D n) (m n) (r n) (s n) :=
  let c := VPVNP.PolynomiallyBounded.const
  hm.mul ((hD.mul ((((c 97).mul hr).add hs).add (c 26))).add (c 1))

/-- The gate count of the complete word selector. -/
theorem indexed_count (addr : Fin r → Fin n) (rows : Fin D → BooleanNetwork n m) (s : ℕ)
    (hs : ∀ i, (rows i).net.count ≤ s) : (indexed addr rows).net.count ≤ lookupBudget D m r s := by
  apply count_vector_le
  intro b
  let cs := List.ofFn fun i => (addressMatch addr i).band ((rows i).rewire fun _ : Fin 1 => b)
  have h := any_count (c := 97*r+s+22) cs (by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    simp only [count_band,count_rewire]
    have := matches_count addr i
    have := hs i
    omega)
  simpa only [cs,List.length_ofFn,Nat.add_assoc] using h

/-- Lookup of an arbitrary advised bit table with the minimal binary address width. -/
def adviceLookup (tab : Fin D → Fin m → Bool) : BooleanNetwork (Nat.clog 2 D) m :=
  indexed id fun i => vector fun b => constant (tab i b)

/-- The advised lookup returns exactly the addressed row. -/
theorem adviceLookup_at (tab : Fin D → Fin m → Bool) (x : Fin (Nat.clog 2 D) → Bool)
    (i : Fin D) (hi : value x = i.val) : (adviceLookup tab).eval x = tab i := by
  unfold adviceLookup
  rw [indexed_at (Nat.le_pow_clog Nat.one_lt_two D) _ _ _ i (by simpa using hi)]
  funext b
  simp

/-- Out-of-range addresses return the zero word. -/
theorem adviceLookup_outside (tab : Fin D → Fin m → Bool) (x : Fin (Nat.clog 2 D) → Bool)
    (hi : D ≤ value x) : (adviceLookup tab).eval x = fun _ => false := by
  funext b
  apply Bool.eq_false_iff.mpr
  intro hx
  rw [adviceLookup,indexed_eval (Nat.le_pow_clog Nat.one_lt_two D)] at hx
  obtain ⟨i,h,_⟩ := hx
  change value x = i.val at h
  exact (Nat.not_lt_of_ge hi) (h ▸ i.isLt)

/-- The advised table of width-`m` bit strings uses polynomially many gates. -/
theorem adviceLookup_count (tab : Fin D → Fin m → Bool) :
    (adviceLookup tab).net.count ≤ lookupBudget D m (Nat.clog 2 D) m :=
  indexed_count _ _ _ (fun _ => by simp)

variable {K : Type*} [Field K] [Fact p.Prime] [Algebra (ZMod p) K]

/-- Select a supplied basis element or its image in the interpolation extension. -/
noncomputable def basisLookup (w : ℕ) (B : Module.Basis (Fin d) (ZMod p) K) (u : Fin D → K) :
    BooleanNetwork (Nat.clog 2 D) (d*w) :=
  adviceLookup fun i => (fieldConst 0 w B (u i)).eval Fin.elim0

/-- An addressed row really represents its supplied element in the interpolation-field basis. -/
theorem basisLookup_at (hp : p < 2^w) (B : Module.Basis (Fin d) (ZMod p) K) (u : Fin D → K)
    (x : Fin (Nat.clog 2 D) → Bool) (i : Fin D) (hi : value x = i.val) :
    Represents B ((basisLookup w B u).eval x) (u i) := by
  rw [basisLookup,adviceLookup_at _ x i hi]
  exact fieldConst_value hp B (u i) Fin.elim0

/-- Basis-word advice has polynomial size in both basis dimensions and the prime limb width. -/
theorem basisLookup_count (B : Module.Basis (Fin d) (ZMod p) K) (u : Fin D → K) :
    (basisLookup w B u).net.count ≤ lookupBudget D (d*w) (Nat.clog 2 D) (d*w) :=
  adviceLookup_count _

/-- Select the column's prime-field linear functional using its binary index. The input
is the column index followed by the interpolation-field element. -/
noncomputable def projectionLookup (r w : ℕ) (B : Module.Basis (Fin d) (ZMod p) K)
    (π : Fin D → K →ₗ[ZMod p] ZMod p) : BooleanNetwork (r+d*w) w :=
  indexed (Fin.castAdd (d*w)) fun i => (select (Fin.natAdd r)).comp (linearLimb B (π i))

/-- The selected linear form yields the actual prime-field value of the column. -/
theorem projectionLookup_at (hr : D ≤ 2^r) (hp : p < 2^w) (B : Module.Basis (Fin d) (ZMod p) K)
    (π : Fin D → K →ₗ[ZMod p] ZMod p) (idx : Fin r → Bool) (i : Fin D) (hi : value idx = i.val)
    (x : Fin (d*w) → Bool) (a : K) (hx : Represents B x a) :
    value ((projectionLookup r w B π).eval (Fin.append idx x)) = (π i a).val := by
  have hl : Fin.append idx x ∘ Fin.castAdd (d*w) = idx := by ext; simp
  have hh : Fin.append idx x ∘ Fin.natAdd r = x := by ext; simp
  rw [projectionLookup,indexed_at hr _ _ _ i (by rw [hl]; exact hi),eval_comp,eval_select,hh]
  exact linearLimb_value hp B (π i) a x hx

/-- Cost of the binary-indexed coordinate projection over the prime field. -/
theorem projectionLookup_count (B : Module.Basis (Fin d) (ZMod p) K)
    (π : Fin D → K →ₗ[ZMod p] ZMod p) :
    (projectionLookup r w B π).net.count ≤
      lookupBudget D w r (w+d*(w+limbCost w+limbCost w)) :=
  indexed_count _ _ _ fun i => by
    simpa only [count_comp,count_select,zero_add] using linearLimb_count (w := w) B (π i)

end ResidueEntryBasis

end BorderVNP
end Computability
end OAI
