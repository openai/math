import OAI.Computability.VPVNP.JointLabelSystem
import OAI.Computability.VPVNP.GradedMonomialIndex
import OAI.Computability.VPVNP.PrimedStackRAMLayout
import OAI.Computability.VPVNP.RAMSerialization

/-!
# Reading a scalar from the joint integer label system

Equation addresses first enumerate input words by their binary digits, then
the fixed motif rows. The exponent vector is read in the arithmetic production
order used by the primed parser. A permutation encoded in polynomially many
advice bits reconciles this order with the finite coordinates of the joint
system. For a motif row it suffices to scan the fixed sparse coefficient table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointLabelSystem.FixedRows

open MvPolynomial PrimedStackRAM RadicalCertificate.MonomialIndex

variable (V I : Type*) [Fintype V] [Fintype I] (F : I → MvPolynomial V ℤ) (n c : ℕ)

/-- Number of formal labels, including all grammar productions and the compressor labels. -/
abbrev labelTotal := Fintype.card (Production n c ⊕ V)
/-- Number of terminal and binary production labels for a grammar with n input positions, n
degree indices and n^(c+5) nonterminal states. -/
abbrev productionCount := labelCount n n (n ^ (c + 5))

/-- The row address is an input word or a fixed motif equation. -/
noncomputable def rowIndex :
    Fin (2 ^ n + Fintype.card I) ≃ (Fin n → Bool) ⊕ I :=
  finSumFinEquiv.symm.trans ((RAMSerialization.wordBits n).sumCongr (Fintype.equivFin _).symm)

/-- The production block uses the dense triangular split index and the three
row-major state indices of the primed parser. The motif block follows it. -/
noncomputable def labelOrder : Fin (productionCount n c + Fintype.card V) ≃ Fin (labelTotal V n c) :=
  finSumFinEquiv.symm.trans
    (((labelIndex n n (n ^ (c + 5))).symm.sumCongr (Fintype.equivFin V).symm).trans
      (Fintype.equivFin _))

theorem labelOrder_left (j : Production n c) :
    labelOrder V n c ((labelIndex n n _ j).castAdd (Fintype.card V)) =
      leftIndex (Production n c) V j := by
  simp [labelOrder, leftIndex]

theorem labelOrder_right (j : V) :
    labelOrder V n c ((Fintype.equivFin _ j).natAdd (productionCount n c)) =
      rightIndex (Production n c) V j := by
  simp [labelOrder, rightIndex]

theorem labelOrder_length : productionCount n c + Fintype.card V = labelTotal V n c := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (labelOrder V n c)

/-- Bits occupied by the table of label ordinals, with a fixed-width word for each grammar or
compressor label. -/
abbrev orderBits :=
  (productionCount n c + Fintype.card V) * Nat.clog 2 (labelTotal V n c)

/-- The advice contains one fixed-width formal coordinate per dense label. -/
noncomputable def orderAdvice : Fin (orderBits V n c) → Bool :=
  RAMSerialization.arrayBits _ _ fun j =>
    ⟨(labelOrder V n c j).val, (labelOrder V n c j).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩

theorem orderAdvice_lookup (j : Fin (productionCount n c + Fintype.card V)) :
    ((RAMSerialization.arrayBits _ _).symm (orderAdvice V n c) j).val = (labelOrder V n c j).val := by
  simp [orderAdvice]

theorem labelTotal_polynomiallyBounded : PolynomiallyBounded (fun n => labelTotal V n c) := by
  have hw := PolynomiallyBounded.id.pow (c + 5)
  refine (((hw.mul (PolynomiallyBounded.id.mul (.const 2))).add
    ((PolynomiallyBounded.id.pow 2).mul (hw.pow 3))).add (.const (Fintype.card V))).of_le fun n => ?_
  rw [labelTotal, Fintype.card_sum]
  apply Nat.add_le_add_right
  simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] using
    card_grammarLabel_le (Fin n × Bool) (Fin (n ^ (c + 5))) n

theorem orderBits_polynomiallyBounded : PolynomiallyBounded (fun n => orderBits V n c) := by
  have h := labelTotal_polynomiallyBounded V c
  refine (h.mul h).of_le fun n => ?_
  rw [orderBits, labelOrder_length]
  apply Nat.mul_le_mul_left
  exact Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

/-- A renaming by a coordinate block preserves the coefficient if the
complementary block has only zero exponents. -/
theorem coeff_of_rename_blocks {V W T R : Type*} [Fintype W] [CommSemiring R]
    (f : V ↪ T) (g : W → T) (hd : ∀ v w, f v ≠ g w) (hc : ∀ k, k ∈ Set.range f ∨ k ∈ Set.range g)
    (p : MvPolynomial V R) (e : T →₀ ℕ) :
    (rename f p).coeff e =
      if ∀ j, e (g j) = 0 then p.coeff (e.comapDomain f f.injective.injOn) else 0 := by
  classical
  have hs : ↑e.support ⊆ Set.range f ↔ ∀ j, e (g j) = 0 := by
    constructor
    · intro h j
      by_contra hn
      obtain ⟨v, hv⟩ := h (Finsupp.mem_support_iff.mpr hn)
      exact hd v j hv
    · intro h k hk
      obtain hmem | ⟨w, rfl⟩ := hc k
      · exact hmem
      · exact False.elim ((Finsupp.mem_support_iff.mp hk) (h w))
  split_ifs with h
  · exact (congrArg (fun u => (rename f p).coeff u) (Finsupp.embDomain_comapDomain (hs.mpr h)).symm).trans
      (coeff_rename_embDomain ..)
  · apply coeff_rename_eq_zero
    intro a ha
    exact False.elim (h (hs.mp (by
      rw [← ha, ← Finsupp.embDomain_eq_mapDomain f]
      exact (Finsupp.mem_range_embDomain_iff ..).mp ⟨a, rfl⟩)))

theorem index_disjoint {V W : Type*} [Fintype V] [Fintype W] (v : V) (w : W) :
    leftIndex V W v ≠ rightIndex V W w :=
  fun h => Sum.inl_ne_inr ((Fintype.equivFin (V ⊕ W)).injective h)

theorem index_cover {V W : Type*} [Fintype V] [Fintype W] (k : Fin (Fintype.card (V ⊕ W))) :
    k ∈ Set.range (leftIndex V W) ∨ k ∈ Set.range (rightIndex V W) := by
  obtain ⟨(v | w), rfl⟩ := (Fintype.equivFin (V ⊕ W)).surjective k
  · exact Or.inl ⟨v, rfl⟩
  · exact Or.inr ⟨w, rfl⟩

/-- A fixed sparse table gives the motif coefficient by exponent comparison.
The size of this table depends only on the chosen motif data. -/
noncomputable def fixedTable (o : I) :
    List ((Fin (Fintype.card V) → ℕ) × ℤ) := by
  classical
  let p := F o
  exact p.support.toList.map fun a => (fun i => a ((Fintype.equivFin V).symm i), p.coeff a)

/-- Recover the integer coefficient of an exponent vector by summing all matching sparse table
rows. -/
def tableLookup {m : ℕ} (table : List ((Fin m → ℕ) × ℤ)) (a : Fin m → ℕ) : ℤ :=
  table.foldl (fun z row => if row.1 = a then z + row.2 else z) 0

private theorem tableLookup_eq_sum {m : ℕ} (table : List ((Fin m → ℕ) × ℤ)) (a : Fin m → ℕ) :
    tableLookup table a = (table.map (fun row => if row.1 = a then row.2 else 0)).sum := by
  let f (row : (Fin m → ℕ) × ℤ) := if row.1 = a then row.2 else 0
  have h (l : List ((Fin m → ℕ) × ℤ)) (z : ℤ) :
      l.foldl (fun z row => if row.1 = a then z + row.2 else z) z = z + (l.map f).sum := by
    induction l generalizing z with
    | nil => simp
    | cons b l ih =>
      simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, f]
      split_ifs <;> simp [add_assoc]
  exact (h table 0).trans (zero_add _)

omit [Fintype I] in
theorem tableLookup_fixedTable (o : I) (a : V →₀ ℕ) :
    tableLookup (fixedTable V I F o) (fun i => a ((Fintype.equivFin V).symm i)) =
      (F o).coeff a := by
  classical
  have he (b : V →₀ ℕ) : (fun i => b ((Fintype.equivFin V).symm i)) =
      (fun i => a ((Fintype.equivFin V).symm i)) ↔ b = a := by
    refine ⟨fun h => Finsupp.ext fun v => ?_, fun h => h ▸ rfl⟩
    simpa using congrFun h (Fintype.equivFin V v)
  rw [tableLookup_eq_sum]
  simp only [fixedTable, List.map_map, Function.comp_def, he, Finset.sum_map_toList]
  by_cases ha : a ∈ (F o).support
  · simp [ha]
  · simp [ha, notMem_support_iff.mp ha]

/-- Combine the two counted predicates and the fixed motif table. The `parse`
argument receives the input word and its exponent vector in dense production
order. The clocked path count is requested only for the constant coefficient. -/
def readDense {Output : Type*} {n g m : ℕ} (parse : (Fin n → Bool) → (Fin g → ℕ) → ℤ)
    (paths : (Fin n → Bool) → ℕ) (table : Output → List ((Fin m → ℕ) × ℤ))
    (row : (Fin n → Bool) ⊕ Output) (e : Fin (g + m) → ℕ) : ℤ :=
  let l := fun j : Fin g => e (j.castAdd m)
  let r := fun j : Fin m => e (j.natAdd g)
  match row with
  | .inl x => if ∀ j, r j = 0 then parse x l - (if ∀ j, l j = 0 then paths x else 0 : ℕ) else 0
  | .inr o => if ∀ j, l j = 0 then tableLookup (table o) r else 0

omit [Fintype I] in
/-- At every equation and monomial, the block reader returns the exact signed
integer coefficient. The two scalar callbacks can be replaced independently
by any implementations returning the parse and canonical path counts. -/
theorem readDense_correct (hn : 2 ≤ n)
    (parse : (Fin n → Bool) → (Fin (productionCount n c) → ℕ) → ℤ)
    (hparse : ∀ (x : Fin n → Bool) (b : Production n c →₀ ℕ),
      parse x (fun i => b ((labelIndex n n _).symm i)) =
        (labelQuery (⟨n - 1, by omega⟩ : Fin n) (⟨0, pow_pos (by omega) _⟩ : Fin (n ^ (c + 5))) x).coeff b)
    (paths : (Fin n → Bool) → ℕ) (hpaths : ∀ x, paths x = acceptingCount x)
    (row : (Fin n → Bool) ⊕ I) (e : Fin (labelTotal V n c) →₀ ℕ) :
    readDense parse paths (fixedTable V I F) row (e ∘ labelOrder V n c) =
      (unionEquations (grammarEquation hn c) F row).coeff e := by
  classical
  let l := leftIndex (Production n c) V
  let r := rightIndex (Production n c) V
  let le := e.comapDomain l l.injective.injOn
  let re := e.comapDomain r r.injective.injOn
  let f := labelIndex n n (n ^ (c + 5))
  let g := Fintype.equivFin V
  have hl (j : Fin (productionCount n c)) :
      e (labelOrder V n c (j.castAdd (Fintype.card V))) = le (f.symm j) := by
    obtain ⟨a, rfl⟩ := f.surjective j
    change e (labelOrder V n c ((labelIndex n n _ a).castAdd _)) = e (l (f.symm (f a)))
    rw [labelOrder_left, f.symm_apply_apply]
  have hr (j : Fin (Fintype.card V)) :
      e (labelOrder V n c (j.natAdd (productionCount n c))) = re (g.symm j) := by
    obtain ⟨a, rfl⟩ := g.surjective j
    change e (labelOrder V n c ((Fintype.equivFin _ a).natAdd _)) = e (r (g.symm (g a)))
    rw [labelOrder_right, g.symm_apply_apply]
  have hlz : (∀ j, le (f.symm j) = 0) ↔ ∀ v, e (l v) = 0 := by
    change (∀ j, le (f.symm j) = 0) ↔ ∀ v, le v = 0
    constructor
    · intro h v
      simpa using h (f v)
    · exact fun h j => h (f.symm j)
  have hrz : (∀ j, re (g.symm j) = 0) ↔ ∀ w, e (r w) = 0 := by
    change (∀ j, re (g.symm j) = 0) ↔ ∀ w, re w = 0
    constructor
    · intro h w
      simpa using h (g w)
    · exact fun h j => h (g.symm j)
  have he0 : (0 : Production n c →₀ ℕ) = le ↔ ∀ v, e (l v) = 0 := by
    constructor
    · intro h v
      change le v = 0
      rw [← h, Finsupp.zero_apply]
    · intro h
      exact Finsupp.ext fun v => (h v).symm
  cases row with
  | inl x =>
    change readDense _ _ _ (.inl x) _ = (rename l (grammarEquation hn c x)).coeff e
    rw [coeff_of_rename_blocks l r index_disjoint index_cover]
    simp only [readDense, Function.comp_apply, hl, hr, hlz, hrz, grammarEquation, coeff_sub,
      coeff_C, he0, hpaths, hparse, Nat.cast_ite, Nat.cast_zero, le, f]
  | inr o =>
    change readDense _ _ _ (.inr o) _ = (rename r (F o)).coeff e
    rw [coeff_of_rename_blocks r l (fun w v => (index_disjoint v w).symm)
      (fun k => (index_cover k).symm)]
    simp only [readDense, Function.comp_apply, hl, hr, hlz, tableLookup_fixedTable, g, re]

/-- The scalar accessor on the `Fin` equation addresses and plain exponent
arrays used by the indexed Macaulay matrix. -/
noncomputable def getCoeff
    (parse : (Fin n → Bool) → (Fin (productionCount n c) → ℕ) → ℤ)
    (paths : (Fin n → Bool) → ℕ) (i : Fin (2 ^ n + Fintype.card I))
    (a : Fin (labelTotal V n c) → ℕ) : ℤ :=
  readDense parse paths (fixedTable V I F) (rowIndex I n i) (a ∘ labelOrder V n c)

theorem getCoeff_eq (hn : 2 ≤ n)
    (parse : (Fin n → Bool) → (Fin (productionCount n c) → ℕ) → ℤ)
    (hparse : ∀ (x : Fin n → Bool) (b : Production n c →₀ ℕ),
      parse x (fun i => b ((labelIndex n n _).symm i)) =
        (labelQuery (⟨n - 1, by omega⟩ : Fin n) (⟨0, pow_pos (by omega) _⟩ : Fin (n ^ (c + 5))) x).coeff b)
    (paths : (Fin n → Bool) → ℕ) (hpaths : ∀ x, paths x = acceptingCount x)
    (i : Fin (2 ^ n + Fintype.card I)) (a : Fin (labelTotal V n c) → ℕ) :
    getCoeff V I F n c parse paths i a = (unionEquations (grammarEquation hn c) F (rowIndex I n i)).coeff (exponentVector a) :=
  readDense_correct V I F n c hn parse hparse paths hpaths (rowIndex I n i) (exponentVector a)

/-- Decode an address by binary arithmetic and fetch each exponent using the
fixed-width order advice. Unused motif coefficients are read as zero by the
sparse table. The entire reader apart from its supplied tables and callbacks
is uniform in the four dimensions. -/
def readAdvice {n g m t q : ℕ} (advice : Fin ((g + m) * Nat.clog 2 t) → Bool)
    (table : Fin q → List ((Fin m → ℕ) × ℤ))
    (parse : (Fin n → Bool) → (Fin g → ℕ) → ℤ) (paths : (Fin n → Bool) → ℕ)
    (i : Fin (2 ^ n + q)) (a : Fin t → ℕ) : ℤ :=
  let words := (RAMSerialization.arrayBits (g + m) (Nat.clog 2 t)).symm advice
  let dense (j : Fin (g + m)) := if h : (words j).val < t then a ⟨(words j).val, h⟩ else 0
  let row := (finSumFinEquiv.symm i).map (RAMSerialization.wordBits n) id
  readDense parse paths table row dense

/-- The fixed motif table and the polynomial-size index advice suffice to
implement the indexed joint coefficient accessor. -/
theorem readAdvice_eq_getCoeff
    (parse : (Fin n → Bool) → (Fin (productionCount n c) → ℕ) → ℤ)
    (paths : (Fin n → Bool) → ℕ) (i : Fin (2 ^ n + Fintype.card I))
    (a : Fin (labelTotal V n c) → ℕ) :
    readAdvice (orderAdvice V n c) (fixedTable V I F ∘ (Fintype.equivFin _).symm) parse paths i a =
      getCoeff V I F n c parse paths i a := by
  simp only [readAdvice, orderAdvice_lookup, dite_true, Fin.is_lt, Fin.eta]
  obtain ⟨(b | o), rfl⟩ := (finSumFinEquiv (m := 2 ^ n) (n := Fintype.card I)).surjective i
  · simp [getCoeff, rowIndex, readDense]
  · simp [getCoeff, rowIndex, readDense]

end JointLabelSystem.FixedRows

end VPVNP
end Computability
end OAI
