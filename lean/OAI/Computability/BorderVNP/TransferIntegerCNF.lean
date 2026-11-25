import OAI.Computability.BorderVNP.SignedFamily
import OAI.Computability.BorderVNP.SignedVerifier
import OAI.Computability.BorderVNP.UnsignedTranscript

/-!
# An integral weighted CNF for the signed universal polynomial

A satisfying payload contains the input, its complementary bits, a private path,
the two sign-verifier gate transcripts, and the negative-output tag. The input and
complement select one variable per position. The tag contributes the integer
minus one. All other positions have weight one. Each nonzero path has exactly one
such payload, so the same clauses and indices work after arbitrary base change.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace SignedCNF

open VPVNP VPVNP.BooleanTranscript VPVNP.HardnessCNF MvPolynomial
open TranscriptCNF
open scoped Classical

variable {n : ℕ}

private abbrev Inputs (n : ℕ) := Fin n ⊕ Fin (n ^ 100)
private abbrev Slots (n : ℕ) :=
  Bool ⊕ Fin n ⊕ Fin n ⊕ Fin (n ^ 100) ⊕ Fin (SignedVerifier.size false n) ⊕
    Fin (SignedVerifier.size true n) ⊕ Unit
private noncomputable abbrev width (n : ℕ) := Fintype.card (Slots n)
private noncomputable def slots (n : ℕ) := Fintype.equivFin (Slots n)

private noncomputable def constSlot (n : ℕ) (b : Bool) := slots n (.inl b)
private noncomputable def wordSlot (n : ℕ) (i : Fin n) := slots n (.inr (.inl i))
private noncomputable def negatedSlot (n : ℕ) (i : Fin n) := slots n (.inr (.inr (.inl i)))
private noncomputable def guessSlot (n : ℕ) (i : Fin (n ^ 100)) := slots n (.inr (.inr (.inr (.inl i))))
private noncomputable def plusSlot (n : ℕ) (i : Fin (SignedVerifier.size false n)) :=
  slots n (.inr (.inr (.inr (.inr (.inl i)))))
private noncomputable def minusSlot (n : ℕ) (i : Fin (SignedVerifier.size true n)) :=
  slots n (.inr (.inr (.inr (.inr (.inr (.inl i))))))
private noncomputable def tag (n : ℕ) := slots n (.inr (.inr (.inr (.inr (.inr (.inr ()))))))
private noncomputable def inputs (n : ℕ) : Inputs n → Fin (width n) :=
  Sum.elim (wordSlot n) (guessSlot n)

private noncomputable def plusAddr (n : ℕ) :=
  address (constSlot n) (inputs n) (plusSlot n) (SignedVerifier.circuit false n).output
private noncomputable def minusAddr (n : ℕ) :=
  address (constSlot n) (inputs n) (minusSlot n) (SignedVerifier.circuit true n).output

private noncomputable def link {k : ℕ} (a b : Fin k) (pol : Bool) :=
  matchClauses a (fun _ : Unit => b) (fun _ => pol)

private theorem satisfies_link {k : ℕ} (a b : Fin k) (pol : Bool) (z : Fin k → Bool) :
    Satisfies (link a b pol) z ↔ z a = (if pol then z b else !(z b)) := by
  rw [link, satisfies_matchClauses]
  cases pol <;> cases z a <;> cases z b <;> simp

private def pins {k : ℕ} (a : Bool → Fin k) : CNF k := [[(a false, false)], [(a true, true)]]

private theorem satisfies_pins {k : ℕ} (a : Bool → Fin k) (z : Fin k → Bool) :
    Satisfies (pins a) z ↔ ∀ b, z (a b) = b := by
  simp only [pins, Satisfies, List.forall_mem_cons, List.exists_mem_cons_iff, List.not_mem_nil,
    false_and, exists_false, or_false, Bool.forall_bool]
  simp

private noncomputable def clauses (n : ℕ) : CNF (width n) :=
  pins (constSlot n) ++
  meetCNF (fun i => link (negatedSlot n i) (wordSlot n i) false) ++
  programClauses (constSlot n) (inputs n) (SignedVerifier.circuit false n).program (plusSlot n) ++
  programClauses (constSlot n) (inputs n) (SignedVerifier.circuit true n).program (minusSlot n) ++
  link (tag n) (minusAddr n) true ++ link (plusAddr n) (minusAddr n) false

private noncomputable def weight (n : ℕ) : Projection ℤ (Fin (width n)) (Fin n × Bool) :=
  fun i => match (slots n).symm i with
  | .inr (.inl j) => .inl (j,true)
  | .inr (.inr (.inl j)) => .inl (j,false)
  | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .inr (-1)
  | _ => .inr 1

private noncomputable def fill (x : Fin n → Bool) (w : Fin (n ^ 100) → Bool) :
    Fin (width n) → Bool :=
  fun i => match (slots n).symm i with
  | .inl b => b
  | .inr (.inl j) => x j
  | .inr (.inr (.inl j)) => !(x j)
  | .inr (.inr (.inr (.inl j))) => w j
  | .inr (.inr (.inr (.inr (.inl j)))) => (SignedVerifier.circuit false n).program.run (Sum.elim x w) j
  | .inr (.inr (.inr (.inr (.inr (.inl j))))) =>
      (SignedVerifier.circuit true n).program.run (Sum.elim x w) j
  | .inr (.inr (.inr (.inr (.inr (.inr _))))) => (SignedVerifier.circuit true n).eval (Sum.elim x w)

private theorem readInputs (z : Fin (width n) → Bool) :
    z ∘ inputs n = Sum.elim (z ∘ wordSlot n) (z ∘ guessSlot n) := by
  funext j
  cases j <;> rfl

private theorem signs (x : Fin n → Bool) (w : Fin (n ^ 100) → Bool) :
    ((SignedVerifier.circuit false n).eval (Sum.elim x w) =
       !((SignedVerifier.circuit true n).eval (Sum.elim x w))) ↔ signedWitness x w ≠ 0 := by
  rw [SignedVerifier.circuit_eval, SignedVerifier.circuit_eval]
  rcases signedWitness_values x w with h | h | h <;> simp [h]

private theorem satisfies_clauses (z : Fin (width n) → Bool) :
    Satisfies (clauses n) z ↔
      z = fill (z ∘ wordSlot n) (z ∘ guessSlot n) ∧
      signedWitness (z ∘ wordSlot n) (z ∘ guessSlot n) ≠ 0 := by
  simp only [clauses, satisfies_append, satisfies_meetCNF, satisfies_pins, satisfies_link,
    Bool.false_eq_true, ite_false, ite_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨hc, hcopy⟩, hp⟩, hm⟩, htag⟩, he⟩
    have hp' := (satisfies_programClauses _ _ _ _ z hc).mp hp
    have hm' := (satisfies_programClauses _ _ _ _ z hc).mp hm
    have p : z (plusAddr n) = (SignedVerifier.circuit false n).eval (z ∘ inputs n) := by
      rw [plusAddr, address_read _ _ _ _ hc, hp']; rfl
    have m : z (minusAddr n) = (SignedVerifier.circuit true n).eval (z ∘ inputs n) := by
      rw [minusAddr, address_read _ _ _ _ hc, hm']; rfl
    rw [readInputs] at hp' hm' p m
    refine ⟨?_, (signs _ _).mp (by simpa only [← p, ← m] using he)⟩
    funext i
    obtain ⟨s, rfl⟩ := (slots n).surjective i
    rcases s with b | j | j | j | j | j | ⟨⟩ <;> simp only [fill, Equiv.symm_apply_apply]
    · exact hc b
    · rfl
    · exact hcopy j
    · rfl
    · exact congrFun hp' j
    · exact congrFun hm' j
    · exact htag.trans m
  · rintro ⟨hz, hs⟩
    let x := z ∘ wordSlot n
    let w := z ∘ guessSlot n
    have zslot (i : Slots n) := congrFun hz (slots n i)
    simp only [fill, Equiv.symm_apply_apply] at zslot
    have hc (b : Bool) : z (constSlot n b) = b := zslot (.inl b)
    have hp : z ∘ plusSlot n = (SignedVerifier.circuit false n).program.run (Sum.elim x w) :=
      funext fun j => zslot (.inr (.inr (.inr (.inr (.inl j)))))
    have hm : z ∘ minusSlot n = (SignedVerifier.circuit true n).program.run (Sum.elim x w) :=
      funext fun j => zslot (.inr (.inr (.inr (.inr (.inr (.inl j))))))
    have p : z (plusAddr n) = (SignedVerifier.circuit false n).eval (Sum.elim x w) := by
      rw [plusAddr, address_read _ _ _ _ hc, hp, readInputs]; rfl
    have m : z (minusAddr n) = (SignedVerifier.circuit true n).eval (Sum.elim x w) := by
      rw [minusAddr, address_read _ _ _ _ hc, hm, readInputs]; rfl
    refine ⟨⟨⟨⟨⟨hc, fun j => zslot (.inr (.inr (.inl j)))⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · apply (satisfies_programClauses _ _ _ _ z hc).mpr
      rwa [readInputs]
    · apply (satisfies_programClauses _ _ _ _ z hc).mpr
      rwa [readInputs]
    · rw [m]
      exact zslot (.inr (.inr (.inr (.inr (.inr (.inr ()))))))
    · rw [p,m]
      exact (signs _ _).mpr hs

private abbrev Path (n : ℕ) := (Fin n → Bool) × (Fin (n ^ 100) → Bool)

private noncomputable def pathEquiv (n : ℕ) :
    {v : Path n // signedWitness v.1 v.2 ≠ 0} ≃ {z // Satisfies (clauses n) z} where
  toFun v := ⟨fill v.val.1 v.val.2, (satisfies_clauses _).mpr (by
    have hx : fill v.val.1 v.val.2 ∘ wordSlot n = v.val.1 := by
      ext i; simp [fill, wordSlot]
    have hw : fill v.val.1 v.val.2 ∘ guessSlot n = v.val.2 := by
      ext i; simp [fill, guessSlot]
    rw [hx,hw]
    exact ⟨rfl, v.property⟩)⟩
  invFun z := ⟨(z.val ∘ wordSlot n, z.val ∘ guessSlot n), ((satisfies_clauses z.val).mp z.property).2⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext <;> funext i <;> simp [Function.comp_apply, fill, wordSlot, guessSlot]
  right_inv z := Subtype.ext ((satisfies_clauses z.val).mp z.property).1.symm

private theorem prod_fill (x : Fin n → Bool) (w : Fin (n ^ 100) → Bool) (hs : signedWitness x w ≠ 0) :
    (∏ i, if fill x w i then (weight n i).elim X C else 1) =
      C (signedWitness x w) * ∏ j, X (j,x j) := by
  rw [← (slots n).prod_comp (fun i => if fill x w i then (weight n i).elim X C else 1)]
  simp only [Fintype.prod_sum_type, fill, weight, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr, map_one, ite_self, Finset.prod_const_one,
    Fintype.prod_unique, one_mul]
  have hpair : (∏ j : Fin n, if x j then X (j,true) else (1 : MvPolynomial (Fin n × Bool) ℤ)) *
      (∏ j : Fin n, if !(x j) then X (j,false) else 1) = ∏ j, X (j,x j) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    cases x j <;> simp
  rw [← hpair, SignedVerifier.circuit_eval]
  rcases signedWitness_values x w with h | h | h
  · exact False.elim (hs h)
  · simp [h]
  · simp [h, mul_comm]

private theorem sum_clauses (n : ℕ) :
    weightedCNF (clauses n) (fun i => (weight n i).elim X C) = Pstar n := by
  let f (v : Path n) : MvPolynomial (Fin n × Bool) ℤ :=
    C (signedWitness v.1 v.2) * ∏ j, X (j, v.1 j)
  rw [weightedCNF, ← Finset.sum_filter]
  rw [Finset.sum_subtype (p := Satisfies (clauses n)) _ (fun _ => by simp) _, ← (pathEquiv n).sum_comp]
  change (∑ v : {v : Path n // signedWitness v.1 v.2 ≠ 0},
    ∏ i, if fill v.val.1 v.val.2 i then (weight n i).elim X C else 1) = _
  simp_rw [fun (v : {v : Path n // signedWitness v.1 v.2 ≠ 0}) => prod_fill v.val.1 v.val.2 v.property]
  change (∑ v : {v : Path n // signedWitness v.1 v.2 ≠ 0}, f v.val) = _
  have hsum : (∑ v : {v : Path n // signedWitness v.1 v.2 ≠ 0}, f v.val) = ∑ v : Path n, f v := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun v : Path n => signedWitness v.1 v.2 ≠ 0))
      (fun _ => by simp) f]
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro v _ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv
    simp [f,hv]
  rw [hsum, Fintype.sum_prod_type, Pstar, pairedPolynomial]
  simp [f, signedCount_eq_sum_witnesses, Finset.sum_mul]

private theorem width_bound : PolynomiallyBounded width := by
  have hp := SignedVerifier.size_polynomiallyBounded false
  have hm := SignedVerifier.size_polynomiallyBounded true
  have hw := PolynomiallyBounded.id.pow 100
  apply ((PolynomiallyBounded.const 2).add (PolynomiallyBounded.id.add (PolynomiallyBounded.id.add
      (hw.add (hp.add (hm.add (.const 1))))))).of_le
  intro n
  simp [width, Slots]

private theorem clauses_bound : PolynomiallyBounded (fun n => literalCount (clauses n)) := by
  have hp := (PolynomiallyBounded.const 7).mul (SignedVerifier.size_polynomiallyBounded false)
  have hm := (PolynomiallyBounded.const 7).mul (SignedVerifier.size_polynomiallyBounded true)
  apply ((((((PolynomiallyBounded.const 2).add (PolynomiallyBounded.id.mul (.const 4))).add hp).add hm).add
    (.const 4)).add (.const 4)).of_le
  intro n
  have h₁ := literalCount_programClauses_le (constSlot n) (inputs n)
    (SignedVerifier.circuit false n).program (plusSlot n)
  have h₂ := literalCount_programClauses_le (constSlot n) (inputs n)
    (SignedVerifier.circuit true n).program (minusSlot n)
  have hlink (a b : Fin (width n)) (pol : Bool) : literalCount (link a b pol) = 4 := by
    simp [link, literalCount_matchClauses]
  have hmeet := literalCount_meetCNF_const (fun i => link (negatedSlot n i) (wordSlot n i) false) 4
    (fun i => hlink _ _ _)
  have hpin : literalCount (pins (constSlot n)) = 2 := rfl
  simp only [clauses, literalCount_append, hpin, hmeet, Fintype.card_fin, hlink]
  omega

end SignedCNF

section

open VPVNP VPVNP.HardnessCNF MvPolynomial SignedCNF

/-- The same Boolean formula uses only one, minus one, and individual paired variables
as unary weights. This restriction lets §13.3 realize its weights by signed-variable
matrix substitutions. -/
theorem signed_weightedCNF_units :
    ∃ (k : ℕ → ℕ) (φ : ∀ n, CNF (k n)) (weights : ∀ n, Projection ℤ (Fin (k n)) (Fin n × Bool)),
      PolynomiallyBounded k ∧ PolynomiallyBounded (fun n => literalCount (φ n)) ∧
      (∀ n i, weights n i = .inr 1 ∨ weights n i = .inr (-1) ∨ ∃ z, weights n i = .inl z) ∧
      ∀ n, weightedCNF (φ n) (fun i => (weights n i).elim X C) = Pstar n := by
  refine ⟨width, clauses, weight, width_bound, clauses_bound, ?_, sum_clauses⟩
  intro n i
  obtain ⟨s, rfl⟩ := (slots n).surjective i
  rcases s with b | j | j | j | j | j | ⟨⟩ <;> simp [weight]

/-- A single polynomial-size system of Boolean clauses gives equation (2.1) over
the integers. Its weights select variables and the scalar sign tag before any
coefficient-field choice. -/
theorem signed_weightedCNF :
    ∃ (k : ℕ → ℕ) (φ : ∀ n, CNF (k n)) (weights : ∀ n, Projection ℤ (Fin (k n)) (Fin n × Bool)),
      PolynomiallyBounded k ∧ PolynomiallyBounded (fun n => literalCount (φ n)) ∧
      ∀ n, weightedCNF (φ n) (fun i => (weights n i).elim X C) = Pstar n :=
  ⟨width, clauses, weight, width_bound, clauses_bound, sum_clauses⟩

end

end BorderVNP
end Computability
end OAI
