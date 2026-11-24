import OAI.Computability.VPVNP.JointScalarCount
import OAI.Computability.VPVNP.GrammarCoefficientBounds

/-!
# Physical signed coefficient read for the joint integer system

The same finite bit-stack control executes all original row reads. Its
gate-stream advice specifies the two verifier circuits and the fixed motif
tables. The public query is one sign bit, the binary equation address and
the array of formal exponents. The returned unsigned integer is the selected
positive or negative part of the formal coefficient.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar

open MvPolynomial ParseGrammar VerifierNetwork JointLabelSystem UniversalCountStack
open RadicalCertificate.MonomialIndex
open scoped Classical

variable (V I : Type*) [Fintype V] [Fintype I] (F : I → MvPolynomial V ℤ) {n : ℕ} (c : ℕ)

/-- Sparse integer coefficient tables of the fixed equations, indexed in their finite row
order. -/
noncomputable abbrev sparseRows := FixedRows.fixedTable V I F ∘ (Fintype.equivFin I).symm
/-- Number of bits reserved above the low input word to address the fixed equations following
the grammar rows. -/
abbrev highWidth := Nat.clog 2 (Fintype.card I + 1) + 1
/-- Width of the witness word that counts each signed part of a coefficient in the fixed
equations. -/
noncomputable abbrev motifWidth := Motif.witnessBits (sparseRows V I F)
/-- Formal variable index of a grammar production in the joint grammar and motif system. -/
noncomputable abbrev productionAddress := leftIndex (Production n c) V
/-- Translate a production number from the primed parser's order into its formal variable
index. -/
noncomputable abbrev denseProduction := productionAddress V (n := n) c ∘ (PrimedStackRAM.labelIndex n n _).symm
/-- Translate a finite motif-entry number into its formal variable index in the joint system. -/
noncomputable abbrev denseLocal := rightIndex (Production n c) V ∘ (Fintype.equivFin V).symm
/-- Final grammar layer `n - 1`, from which the coefficient verifier starts a parse. -/
abbrev rootLayer (hn : 2 ≤ n) : Fin n := ⟨n-1, by omega⟩
/-- State zero at the root of the grammar used for the joint coefficient query. -/
abbrev rootState (hn : 2 ≤ n) : Fin (n^(c+5)) := ⟨0, pow_pos (by omega) _⟩

/-- Grammar verifier frame rooted at the final layer and state zero, with label exponents
addressed in the joint system. -/
noncomputable abbrev parseBlock (hn : 2 ≤ n) (W : ℕ) :=
  ParseOracle.frame (parseOracleMetadata (Fin n × Bool) (Fin (n^(c+5))) n
    (rootLayer hn) (rootState c hn)) (productionAddress V c) W

/-- The exact advised checker. Its input wiring uses the formal coordinate
number of each grammar and motif label. -/
noncomputable abbrev rowFrame (hn : 2 ≤ n) (W : ℕ) :=
  frame (high := highWidth I) (motif := motifWidth V I F)
    (denseProduction V c) (denseLocal V c) (sparseRows V I F) (parseBlock V c hn W) (VerifierMachine.verifierFrame n)

/-- Single-output Boolean circuit for counting the selected sign of a joint equation
coefficient. -/
noncomputable abbrev checker (hn : 2 ≤ n) (W : ℕ) := (rowFrame V I F c hn W).circuit ()

private theorem row_fits (o : Fin (2^n + Fintype.card I)) : o.val < 2^(n + highWidth I) := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card I + 1)
  have h₁ := Nat.one_le_two_pow (n := n)
  have h₂ := Nat.one_le_two_pow (n := Nat.clog 2 (Fintype.card I + 1))
  rw [highWidth, pow_add, pow_succ]
  apply o.isLt.trans_le
  nlinarith [Nat.mul_le_mul_left (2^n) h, Nat.mul_le_mul_right (Fintype.card I + 1) h₁]

private theorem part_grammar (p u : ℕ) (neg : Bool) (inBlock constant : Prop)
    [Decidable inBlock] [Decidable constant] (hz : constant → p = 0) :
    (if neg then (if inBlock ∧ constant then u else 0) else (if inBlock then p else 0)) =
      Motif.part neg (if inBlock then (p : ℤ) - (if constant then (u : ℤ) else 0) else 0) := by
  by_cases hi : inBlock <;> by_cases hc : constant <;> cases neg <;>
    simp [hi, hc, Motif.part, show constant → p = 0 from hz] at *

private theorem count_clock (x : Fin n → Bool) :
    (∑ u, ((VerifierMachine.verifierFrame n).eval (Sum.elim x u) ()).toNat) = acceptingCount x := by
  have hc := acceptingCount_eq_sum_witnesses (R := ℕ) x
  simp only [Nat.cast_id] at hc
  rw [hc]
  exact Finset.sum_congr rfl fun u _ => by rw [VerifierMachine.verifierFrame_eval]; cases verifiesInput x u <;> rfl

private theorem wordBits_eq (j : Fin (2^n)) :
    (fun b : Fin n => j.val.testBit b.val) = RAMSerialization.wordBits n j :=
  funext (LiveHeader.testBit_wordBits j)

/-- Count the checker witnesses at a grammar row. -/
private theorem checker_grammar (hn : 2 ≤ n) (W : ℕ) (j : Fin (2^n)) (neg : Bool)
    (a : Fin (FixedRows.labelTotal V n c) → ℕ) (ha : ∀ v, a v < 2^W) :
    (∑ w, ((checker V I F c hn W).eval (Sum.elim (query neg j.val a) w)).toNat) =
      Motif.part neg ((unionEquations (grammarEquation hn c) F (.inl (RAMSerialization.wordBits n j))).coeff
        (exponentVector a)) := by
  let l := leftIndex (Production n c) V
  let r := rightIndex (Production n c) V
  let b := (exponentVector a).comapDomain l l.injective.injOn
  let x := RAMSerialization.wordBits n j
  let B := labelQuery (rootLayer hn) (rootState c hn) x
  have hnonneg := (coeff_labelQuery_bounds (rootLayer hn) (rootState c hn) x b).1
  have hₚ : (∑ w, ((parseBlock V c hn W).eval (Sum.elim (ParseOracle.query x a W) w) ()).toNat) =
      (B.coeff b).toNat := by
    have h := ParseOracle.count_checker (rootLayer hn) (rootState c hn) l x a (W := W)
      (fun z => ha (l z)) b (fun _ => rfl)
    simpa only [ParseOracle.checker, Frame.circuit_eval] using h
  have hz : b = 0 → (B.coeff b).toNat = 0 := by
    rintro hb
    rw [hb]
    have h0 : B.coeff 0 = 0 := (labelQuery_isHomogeneous ..).coeff_eq_zero (by simp)
    simp [h0]
  have htotal : (∀ j, a j = 0) ↔ (∀ v, a (r v) = 0) ∧ b = 0 := by
    constructor
    · intro h
      exact ⟨fun _ => h _, Finsupp.ext fun v => h (l v)⟩
    · rintro ⟨h,hb⟩ i
      rcases FixedRows.index_cover (V := Production n c) (W := V) i with ⟨v,rfl⟩ | ⟨v,rfl⟩
      · change b v = 0
        rw [hb, Finsupp.zero_apply]
      · exact h v
  have hlocal : (∀ i, a (denseLocal V c i) = 0) ↔ ∀ v, a (r v) = 0 := by
    exact ((Fintype.equivFin V).symm.surjective.forall (p := fun v => a (r v) = 0)).symm
  change (∑ w, (((rowFrame V I F c hn W).circuit ()).eval _).toNat) = Motif.part neg
    ((rename l (grammarEquation hn c x)).coeff (exponentVector a))
  rw [rowFrame, count_grammar _ _ _ _ _ neg j.val j.isLt a ha, wordBits_eq, hₚ, count_clock]
  rw [FixedRows.coeff_of_rename_blocks l r FixedRows.index_disjoint FixedRows.index_cover]
  change _ = Motif.part neg (if ∀ v, a (r v) = 0 then (grammarEquation hn c x).coeff b else 0)
  simp only [grammarEquation, coeff_sub, coeff_C, eq_comm (a := (0 : Production n c →₀ ℕ)) (b := b)]
  simp only [hlocal, htotal]
  exact (part_grammar (B.coeff b).toNat (acceptingCount x) neg (∀ v, a (r v) = 0) (b = 0) hz).trans
    (by rw [Int.toNat_of_nonneg hnonneg])

/-- Count the checker witnesses at a motif row. -/
private theorem checker_motif (hn : 2 ≤ n) (W : ℕ) (o : Fin (Fintype.card I)) (neg : Bool)
    (a : Fin (FixedRows.labelTotal V n c) → ℕ) (ha : ∀ v, a v < 2^W) :
    (∑ w, ((checker V I F c hn W).eval (Sum.elim (query neg (2^n+o.val) a) w)).toNat) =
      Motif.part neg ((unionEquations (grammarEquation hn c) F (.inr ((Fintype.equivFin I).symm o))).coeff
        (exponentVector a)) := by
  let l := leftIndex (Production n c) V
  let r := rightIndex (Production n c) V
  let b := (exponentVector a).comapDomain r r.injective.injOn
  have hprod : (∀ i, a (denseProduction V c i) = 0) ↔ ∀ v, a (l v) = 0 :=
    ((PrimedStackRAM.labelIndex n n _).symm.surjective.forall (p := fun v => a (l v) = 0)).symm
  have htable : FixedRows.tableLookup (sparseRows V I F o) (a ∘ denseLocal V c) =
      (F ((Fintype.equivFin I).symm o)).coeff b :=
    FixedRows.tableLookup_fixedTable V I F _ b
  change (∑ w, (((rowFrame V I F c hn W).circuit ()).eval _).toNat) = Motif.part neg
    ((rename r (F ((Fintype.equivFin I).symm o))).coeff (exponentVector a))
  rw [rowFrame, count_motif _ _ _ _ _ neg o (row_fits I (o.natAdd (2^n))) a ha (Motif.part_fits ..)]
  rw [FixedRows.coeff_of_rename_blocks r l (fun w v => (FixedRows.index_disjoint v w).symm)
      (fun i => (FixedRows.index_cover i).symm)]
  simp only [hprod, htable]
  change (if ∀ v, a (l v) = 0 then Motif.part neg _ else 0) =
    Motif.part neg (if ∀ v, a (l v) = 0 then _ else 0)
  split_ifs <;> cases neg <;> simp [Motif.part, b]

/-- One bit-stack count gives the selected part of the actual integer row. -/
theorem checker_count (hn : 2 ≤ n) (W : ℕ) (row : Fin (2^n+Fintype.card I)) (negative : Bool)
    (a : Fin (FixedRows.labelTotal V n c) → ℕ) (ha : ∀ v, a v < 2^W) :
    (∑ w, ((checker V I F c hn W).eval (Sum.elim (query negative row.val a) w)).toNat) =
      Motif.part negative ((unionEquations (grammarEquation hn c) F (FixedRows.rowIndex I n row)).coeff
        (exponentVector a)) := by
  obtain ⟨(j | o), rfl⟩ := (finSumFinEquiv (m := 2^n) (n := Fintype.card I)).surjective row
  · simpa [FixedRows.rowIndex] using checker_grammar V I F c hn W j negative a ha
  · simpa [FixedRows.rowIndex] using checker_motif V I F c hn W o negative a ha

/-- Execution of the fixed finite routine from its concrete port bank. The
signed part of the formal coefficient appears as a little-endian word on
the `.total` stack. The circuit advice depends only on the dimensions and
the fixed equation family. -/
theorem scalar_runs (hn : 2 ≤ n) (W : ℕ) (row : Fin (2^n+Fintype.card I)) (negative : Bool)
    (a : Fin (FixedRows.labelTotal V n c) → ℕ) (ha : ∀ v, a v < 2^W) :
    let C := checker V I F c hn W
    let x := query negative row.val a
    let aux := scalarInputs C x
    let w := witnessWidth (ParseOracle.Flags n n (Fin (n^(c+5)))) (n^clockExponent) (motifWidth V I F)
    let value := ((unionEquations (grammarEquation hn c) F (FixedRows.rowIndex I n row)).coeff (exponentVector a))
    ∃ ticks ≤ 2^w * perChoice C, SpaceRun countCircuit.standalone (stackLimit C) ticks (some countCircuit.entry)
      (bank aux (digits w 0) (digits (w+1) 0) [] []) none
      (bank aux (digits w 0) (digits (w+1) (Motif.part negative value)) [] []) := by
  dsimp only
  simpa only [checker_count V I F c hn W row negative a ha] using
    countCircuit_runs (checker V I F c hn W) (query negative row.val a)

/-- The count is at most the number of full witness strings. -/
theorem scalar_part_lt (hn : 2 ≤ n) (W : ℕ) (row : Fin (2^n+Fintype.card I)) (negative : Bool)
    (a : Fin (FixedRows.labelTotal V n c) → ℕ) (ha : ∀ v, a v < 2^W) :
    let w := witnessWidth (ParseOracle.Flags n n (Fin (n^(c+5)))) (n^clockExponent) (motifWidth V I F)
    let z := ((unionEquations (grammarEquation hn c) F (FixedRows.rowIndex I n row)).coeff (exponentVector a))
    Motif.part negative z < 2^(w+1) := by
  intro w z
  have h := checker_count V I F c hn W row negative a ha
  have hb : Motif.part negative z ≤ 2^w := by
    rw [← h]
    calc
      _ ≤ ∑ _ : Fin w → Bool, 1 := Finset.sum_le_sum fun _ _ => Bool.toNat_le _
      _ = 2^w := by simp
  exact hb.trans_lt (by rw [pow_succ]; have := Nat.two_pow_pos w; omega)

/-- Reading the returned count word retains the selected part in full. -/
theorem scalar_digits_value (hn : 2 ≤ n) (W : ℕ) (row : Fin (2^n+Fintype.card I)) (negative : Bool)
    (a : Fin (FixedRows.labelTotal V n c) → ℕ) (ha : ∀ v, a v < 2^W) :
    let w := witnessWidth (ParseOracle.Flags n n (Fin (n^(c+5)))) (n^clockExponent) (motifWidth V I F)
    let z := ((unionEquations (grammarEquation hn c) F (FixedRows.rowIndex I n row)).coeff (exponentVector a))
    TapeWord.value (digits (w+1) (Motif.part negative z)) = Motif.part negative z := by
  exact (value_digits ..).trans (Nat.mod_eq_of_lt (scalar_part_lt V I F c hn W row negative a ha))

theorem signedParts_sub (z : ℤ) : (Motif.part false z : ℤ) - (Motif.part true z : ℤ) = z := by
  cases z <;> simp [Motif.part]
  omega

theorem signedParts_cast {R : Type*} [CommRing R] (z : ℤ) :
    (Motif.part false z : R) - (Motif.part true z : R) = (z : R) := by
  exact_mod_cast congrArg (Int.castRingHom R) (signedParts_sub z)

end JointScalar

end VPVNP
end Computability
end OAI
