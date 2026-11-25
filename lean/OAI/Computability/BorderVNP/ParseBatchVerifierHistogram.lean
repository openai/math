import OAI.Computability.BorderVNP.CrossingParallelFrame
import OAI.Computability.BorderVNP.ParseBatchVerifierMarkerSort
import OAI.Computability.BorderVNP.ParseBatchVerifierCountEquations

/-!
# Physical verification of the occurrence histogram

A use row exposes only its label bits. Each possible label has a rank word and a count word.
Sorting the end markers verifies all ranks. One binary arithmetic scan verifies all the
counts. Thus for fixed use labels there is exactly one accepting assignment to the extra bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchCounts

open VPVNP.VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {U P : Type*} {a b : ℕ}

/-- Input labels of all occurrences, followed by both guessed words for every label. -/
abbrev HistogramPin (U : Type*) (a b : ℕ) := (U × Fin a) ⊕ ArithmeticPin (2 ^ a) b

/-- Decode a bit string for each occurrence as its numerical label. -/
noncomputable def useLabel (x : U × Fin a → Bool) (u : U) : Fin (2 ^ a) :=
  numberWords a (fun j => x (u, j))

private def rankPin : MarkerPins U a b → HistogramPin U a b
  | .inl x => .inl x
  | .inr (i, j) => .inr (i, false, j)

variable [Fintype U] [Fintype P]

/-- Conjoin the sorting and nonwrapping arithmetic circuits on the same guessed rank words. -/
noncomputable def histogramFrame (layout : Fin (2 ^ b) ≃ Rows U (2 ^ a) P) :
    Frame (HistogramPin U a b) Unit :=
  (Crossing.parallelFrame ((markerFrame layout).subst (Frame.initial rankPin))
    ((countArithmeticFrame (2 ^ a) b).subst (Frame.initial Sum.inr))).step
      fun _ => .and (.input (.inl ())) (.input (.inr ()))

/-- The physical histogram test accepts exactly the true ranks and counts of the input labels. -/
theorem histogramFrame_eval (layout : Fin (2 ^ b) ≃ Rows U (2 ^ a) P)
    (z : HistogramPin U a b → Bool) :
    (histogramFrame layout).eval z () = true ↔
      (∀ i, pinValue (z ∘ Sum.inr) i false = markerRank (useLabel (z ∘ Sum.inl)) i) ∧
      (∀ i, pinValue (z ∘ Sum.inr) i true = useCount (useLabel (z ∘ Sum.inl)) i) := by
  have h₁ : (Frame.initial (rankPin : MarkerPins U a b → HistogramPin U a b)).eval z = z ∘ rankPin :=
    funext fun i => Frame.initial_eval rankPin z i
  have h₂ : (Frame.initial (Sum.inr : ArithmeticPin (2 ^ a) b → HistogramPin U a b)).eval z =
      z ∘ Sum.inr := funext fun i => Frame.initial_eval Sum.inr z i
  rw [histogramFrame, Frame.step_eval]
  simp only [StatementCircuit.Expr.eval, Bool.and_eq_true, Crossing.parallelFrame_eval_inl,
    Crossing.parallelFrame_eval_inr, Frame.subst_eval, h₁, h₂, markerFrame_eval, countArithmeticFrame_eval]
  change ((∀ i, pinValue (z ∘ Sum.inr) i false = markerRank (useLabel (z ∘ Sum.inl)) i) ∧
    RankEquations (fun i => pinValue (z ∘ Sum.inr) i false) (fun i => pinValue (z ∘ Sum.inr) i true)) ↔ _
  apply and_congr_right
  intro h
  rw [funext h, rankEquations_markerRank_iff, funext_iff]

omit [Fintype P] in
/-- Explicit gate budget for one sort, one arithmetic pass, and the final conjunction. -/
theorem histogramFrame_size (layout : Fin (2 ^ b) ≃ Rows U (2 ^ a) P) :
    (histogramFrame layout).size ≤
      2 ^ b * ((b+1+a+1) + b^2*(24*(b+1+a+1)+1) + (3*b+4)+2) +
        1300 * (2 ^ a + 1) * (b + 1) ^ 2 + 4 := by
  unfold histogramFrame
  apply (Frame.step_size_le _ _ 3 (fun _ => le_rfl)).trans
  simp only [Frame.subst_size, Frame.initial_size, zero_add, Crossing.parallelFrame_size,
    Fintype.card_unit, one_mul]
  have h₁ := markerFrame_size layout
  have h₂ := countArithmeticFrame_size (2 ^ a) b
  omega

private theorem capacity (layout : Fin (2 ^ b) ≃ Rows U (2 ^ a) P) :
    Fintype.card U + 2 ^ a ≤ 2 ^ b := by
  have h := Fintype.card_congr layout
  simp only [Rows, Fintype.card_fin, Fintype.card_sum] at h
  omega

/-- In a valid padded layout there are at least as many slots as distinct labels.
Consequently the gate count is linear in the padded length times the cube of its bit width. -/
theorem histogramFrame_size_per_row (layout : Fin (2 ^ b) ≃ Rows U (2 ^ a) P) :
    (histogramFrame layout).size ≤ 3000 * 2 ^ b * (b + 2) ^ 3 := by
  have hcap := capacity layout
  have hpow : 2 ^ a ≤ 2 ^ b := by omega
  have hab := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  have hrows := Nat.two_pow_pos b
  have htwice : 2 ^ a + 1 ≤ 2 * 2 ^ b := by omega
  apply (histogramFrame_size layout).trans
  calc
    _ ≤ 2 ^ b * ((b+1+b+1) + b^2*(24*(b+1+b+1)+1) + (3*b+4)+2) +
        1300 * (2 * 2 ^ b) * (b+1)^2 + 4 := by gcongr
    _ ≤ _ := by ring_nf; omega

private theorem fits (layout : Fin (2 ^ b) ≃ Rows U (2 ^ a) P) (label : U → Fin (2 ^ a))
    (i : Fin (2 ^ a)) (isCount : Bool) :
    (if isCount then useCount label i else markerRank label i) < 2 ^ b := by
  have h := capacity layout
  have rank : (Finset.univ.filter fun u => label u ≤ i).card ≤ Fintype.card U :=
    (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have count : (Finset.univ.filter fun u => label u = i).card ≤ Fintype.card U :=
    (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have := i.isLt
  cases isCount <;> simp only [Bool.false_eq_true, ite_false, ite_true, useCount, markerRank] <;> omega

/-- Unique numerical guess for fixed use-label pins, written in the same MSB-first
encoding read by the verifier. -/
noncomputable def canonicalGuess (layout : Fin (2 ^ b) ≃ Rows U (2 ^ a) P)
    (x : U × Fin a → Bool) : ArithmeticPin (2 ^ a) b → Bool :=
  fun (i, isCount, j) => (numberWords b).symm
    ⟨if isCount then useCount (useLabel x) i else markerRank (useLabel x) i,
      fits layout (useLabel x) i isCount⟩ j

/-- Decoding either word of the canonical guess recovers the prescribed natural number. -/
theorem canonicalGuess_value (layout : Fin (2 ^ b) ≃ Rows U (2 ^ a) P) (x : U × Fin a → Bool)
    (i : Fin (2 ^ a)) (isCount : Bool) :
    pinValue (canonicalGuess layout x) i isCount =
      if isCount then useCount (useLabel x) i else markerRank (useLabel x) i := by
  unfold pinValue canonicalGuess
  exact value_encode _

/-- Once the occurrence label bits are fixed, the whole circuit accepts precisely one
assignment to the guessed rank and count bits. -/
theorem histogramFrame_eval_iff_eq_canonicalGuess (layout : Fin (2 ^ b) ≃ Rows U (2 ^ a) P)
    (x : U × Fin a → Bool) (g : ArithmeticPin (2 ^ a) b → Bool) :
    (histogramFrame layout).eval (Sum.elim x g) () = true ↔ g = canonicalGuess layout x := by
  rw [histogramFrame_eval]
  change ((∀ i, pinValue g i false = markerRank (useLabel x) i) ∧
    (∀ i, pinValue g i true = useCount (useLabel x) i)) ↔ _
  constructor
  · rintro ⟨hr, hc⟩
    funext ⟨i, s, j⟩
    have hv : pinValue g i s = pinValue (canonicalGuess layout x) i s := by
      rw [canonicalGuess_value]
      cases s
      · exact hr i
      · exact hc i
    exact congrFun (value_injective b hv) j
  · rintro rfl
    exact ⟨fun i => canonicalGuess_value layout x i false, fun i => canonicalGuess_value layout x i true⟩

/-- The certificate multiplicity for each batch of fixed labels is exactly one. -/
theorem histogramFrame_uniqueGuess (layout : Fin (2 ^ b) ≃ Rows U (2 ^ a) P)
    (x : U × Fin a → Bool) :
    ∃! g : ArithmeticPin (2 ^ a) b → Bool, (histogramFrame layout).eval (Sum.elim x g) () = true :=
  ⟨canonicalGuess layout x, (histogramFrame_eval_iff_eq_canonicalGuess layout x _).mpr rfl,
    fun g hg => (histogramFrame_eval_iff_eq_canonicalGuess layout x g).mp hg⟩

end ParseBatchCounts

end BorderVNP
end Computability
end OAI
