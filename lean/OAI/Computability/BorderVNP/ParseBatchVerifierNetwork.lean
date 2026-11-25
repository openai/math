import OAI.Computability.BorderVNP.ParseBatchVerifierJoined
import OAI.Computability.BorderVNP.ParseBatchVerifierWeightedSum
import OAI.Computability.BorderVNP.ParseBatchVerifierBudget
import OAI.Computability.BorderVNP.ParseBooleanNetwork

/-!
# The batched query network and its near-linear cost

The physical pin of each parameter/count-bit pair carries a single unary
weight. All other gates, all consistency checks and all fanout tensors have
Boolean entries. Both the exact contraction and the gate budget refer to the
same shared circuit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier

open VPVNP VPVNP.ParseGrammar VPVNP.VerifierNetwork
open ParseBatchTrees ParseBatch ParseBatchCounts MvPolynomial


variable {m g n r : ℕ}

/-- One and only one unary site for each parameter and each significant exponent bit. -/
abbrev WeightSites (m g r : ℕ) {n : ℕ} (d : Fin n) :=
  GrammarLabel (Fin m × Bool) (Fin g) n × Fin (Nat.clog 2 (r*(2*d.val+1)+1))

/-- Feed the physical guess carrying each exponent bit into its unary site. -/
noncomputable def weightedPin {d : Fin n} (j : WeightSites m g r d) :
    RawPin m g r d ⊕ AuxPin m g r d := .inr (weightPin d j.1 j.2)

/-- The two entries at a weighted vertex are exactly `1` and `X_t^(2^j)`. -/
noncomputable def unaryWeight {d : Fin n} (j : WeightSites m g r d) (b : Bool) :
    MvPolynomial (GrammarLabel (Fin m × Bool) (Fin g) n) ℤ :=
  if b then X j.1 ^ (2^j.2.val) else 1

/-- All external bits and private guesses enter one shared binary-gate table. -/
noncomputable def verifier (d : Fin n) (trees : Frame (BatchPins m g n r d) Unit) :=
  (joined d trees).circuit ()

/-- The physical, degree-three network for a verified parse circuit. -/
noncomputable abbrev queryLayout (d : Fin n) (trees : Frame (BatchPins m g n r d) Unit) :=
  BooleanLayout.layout (verifier d trees) (weightedPin (d := d))

/-- Contracting all of the internal wires gives the original product over all `r`
paired-monomial queries as a formal polynomial in the grammar parameters. -/
theorem queryLayout_value (d : Fin n) (h : Fin g) (trees : Frame (BatchPins m g n r d) Unit)
    (he : ∀ x bs, trees.eval (batchInput d x bs) () = true ↔ Accepted d h x bs)
    (x : Fin r → Fin m → Bool) :
    let L := queryLayout d trees
    L.network.value (L.tables (BooleanLayout.factor (verifier d trees) unaryWeight))
      (fun ij _ => x ij.1 ij.2) = ∏ i, labelQuery d h (x i) := by
  apply (BooleanLayout.value_eq (verifier d trees) (weightedPin (d := d)) unaryWeight (fun ij => x ij.1 ij.2)).trans
  have accept (raw : RawPin m g r d → Bool) (aux : AuxPin m g r d → Bool) :
      (verifier d trees).eval (Sum.elim (fun ij => x ij.1 ij.2) (Sum.elim raw aux)) = true ↔
        Accepted d h x (decodeRaw d raw) ∧
          aux = canonicalGuess (histogramLayout m g r d) (occurrenceBits (decodeRaw d raw)) := by
    rw [verifier, Frame.circuit_eval]
    exact joined_eval d h trees he x raw aux
  classical
  trans ∑ w : RawPin m g r d ⊕ AuxPin m g r d → Bool,
    if (verifier d trees).eval (Sum.elim (fun ij => x ij.1 ij.2) w) then guessedWeight d (w ∘ Sum.inr) else 0
  · apply Finset.sum_congr (Finset.ext fun w => by simp)
    intro w _
    by_cases hw : (verifier d trees).eval (Sum.elim (fun ij => x ij.1 ij.2) w) = true
    · simp only [hw, ite_true, Fintype.prod_prod_type, WeightSites, guessedWeight, unaryWeight, weightedPin, Function.comp_apply]
      apply Finset.prod_congr (Finset.ext fun t => by simp)
      intro t _
      apply Finset.prod_congr (Finset.ext fun j => by simp)
      intro j _
      rfl
    · simp [hw]
  · exact weighted_sum_of_accept d h x (verifier d trees).eval accept

/-- The budget for the compiled query network includes all gate, histogram, fanout,
input and unary sites. Constants are absolute. -/
theorem queryLayout_volume (d : Fin m) (trees : Frame (BatchPins m g m r d) Unit)
    (hb : HistogramBudget m g r d) (hr : 0 < r)
    (ht : trees.size ≤ 1000607 * (m*r) * (Nat.clog 2 (2*m*r)+3)^3) :
    let L := queryLayout d trees
    Fintype.card L.Site + Fintype.card L.Edge + Fintype.card (Fin r × Fin m) ≤
      180000000 * (m*r) * (Nat.clog 2 (2*m*r)+3)^3 := by
  let l := Nat.clog 2 (2*m*r)+3
  let T := m*r*l^3
  have hT : 1 ≤ T := Nat.mul_pos (Nat.mul_pos ((Nat.zero_le d.val).trans_lt d.isLt) hr) (Nat.pow_pos (by dsimp [l]; omega : 0 < l))
  have bound := BooleanLayout.volume_bound (verifier d trees) (weightedPin (d := d))
  apply bound.trans
  have hgate : (joined d trees).size ≤ trees.size + (histogramFrame (histogramLayout m g r d)).size + 3 := by
    unfold joined
    apply (Frame.step_size_le _ _ 3 (fun _ => le_rfl)).trans
    simp only [Crossing.parallelFrame_size, Frame.subst_size, Frame.initial_size, zero_add,
      Fintype.card_unit, one_mul, le_refl]
  have hh := hb.gates
  have lift : (Nat.clog 2 (2*m*r)+1)^3 ≤ l^3 := Nat.pow_le_pow_left (by dsimp [l]; omega) 3
  have hhist : (histogramFrame (histogramLayout m g r d)).size ≤ 1152000*T := by
    exact hh.trans ((Nat.mul_le_mul_left _ lift).trans_eq (by dsimp [T]; ring))
  have htree : trees.size ≤ 1000607*T := ht.trans_eq (by dsimp [T,l]; ring)
  have hc := Frame.circuitSize_le (joined d trees) ()
  have hw := hb.wires
  have hw' : Fintype.card (Fin r × Fin m) + Fintype.card (RawPin m g r d ⊕ AuxPin m g r d) +
      Fintype.card (WeightSites m g r d) ≤ 20*T := by
    have hl : Nat.clog 2 (2*m*r)+1 ≤ l^3 := (show Nat.clog 2 (2*m*r)+1 ≤ l by dsimp [l]; omega).trans
      (Nat.le_self_pow (by decide : 3 ≠ 0) l)
    calc
      _ = m*r + r*(2*d.val+1)*labelWidth m g m + 2*2^labelWidth m g m*histogramWidth m g r d +
          Fintype.card (GrammarLabel (Fin m × Bool) (Fin g) m)*Nat.clog 2 (r*(2*d.val+1)+1)  := by
          simp only [RawPin, AuxPin, ArithmeticPin, WeightSites, Fintype.card_prod, Fintype.card_sum,
            Fintype.card_fin, Fintype.card_bool, labelWidth, ParseRecords.BitSlot]
          ring
      _ ≤ _ := hw.trans ((Nat.mul_le_mul_left _ hl).trans_eq (by dsimp [T]; ring))
  change 20 * (_ + (joined d trees).circuitSize () + 1) ≤ _
  rw [Nat.mul_assoc 180000000 (m*r)]
  change Fintype.card (Fin r × Fin m) + Fintype.card (Fin r × RowPins m g m d ⊕
    ArithmeticPin (2^labelWidth m g m) (histogramWidth m g r d)) + Fintype.card (WeightSites m g r d) ≤ 20*T at hw'
  change _ ≤ 180000000*T
  omega

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI
