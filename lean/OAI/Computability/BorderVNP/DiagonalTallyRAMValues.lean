import OAI.Computability.BorderVNP.DiagonalTallyRAMTotals
import OAI.Computability.BorderVNP.DiagonalEvaluator

/-! # Natural exponents in the global tally array

On bounded inputs the native column scans compute the natural exponents of the
assigned monomial. The first coordinates store parameter exponents, followed by
the multiplicities of the fixed list of gadget entries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

/-- Inside the written slice, each coordinate has precisely its designated total. -/
theorem writeTotals_at {w : ℕ} (f : TotalsFrame) (a : ℕ → Word w) (m : Memory w)
    (j len c : ℕ) (hl : j ≤ c) (hu : c < j+len) :
    writeTotals f a m j len (f.totals+c) = a c := by
  have outside (m : Memory w) (i l d : ℕ) (hd : d < i ∨ i+l ≤ d) :
      writeTotals f a m i l (f.totals+d) = m (f.totals+d) := by
    induction l generalizing i m with
    | zero => rfl
    | succ l ih =>
      rw [writeTotals, ih _ _ (by omega)]
      exact Function.update_of_ne (by omega) ..
  induction len generalizing j m with
  | zero => omega
  | succ l ih =>
    rw [writeTotals]
    rcases Nat.eq_or_lt_of_le hl with rfl | hlt
    · rw [outside _ _ _ _ (.inl (by omega)), Function.update_self]
    · exact ih _ _ (by omega) (by omega)

/-- Casting the natural subtotal sum into a machine word agrees with word addition. -/
theorem word_sum {w R : ℕ} (f : Fin R → ℕ) :
    (∑ i, word w (f i)) = word w (∑ i, f i) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Fin.sum_univ_succ (fun i => word w (f i)), Fin.sum_univ_succ f, ih, word_add]

/-- The emitted word can be read as the natural sum when that sum fits the selected width. -/
theorem totals_nat {w : ℕ} (f : TotalsFrame) (a : ℕ → ℕ → ℕ) (m : Memory w)
    (c : ℕ) (hc : c < f.dim) (hfit : (∑ i : Fin f.teams, a i.val c) < 2^w) :
    (writeTotals f (fun j => ∑ i : Fin f.teams, word w (a i.val j)) m 0 f.dim (f.totals+c)).val =
      ∑ i : Fin f.teams, a i.val c := by
  rw [writeTotals_at _ _ _ _ _ _ (by omega) (by omega),word_sum,word_val _ _ hfit]

/-- Natural tally row associated to one fully specified team's unary bits and
gadget counts. This is the precise data used by the final residue entry. -/
noncomputable def tallyRow {R h u b : ℕ} (t : Diagonal.Tally (Fin R) (Fin h) (Fin u) b)
    (i : Fin R) (j : Fin (h+u)) : ℕ :=
  Fin.append (fun p => ∑ k : Fin b, if t.powers i p k then 2^k.val else 0) (t.counts i) j

/-- The parameter part of the column sum is the exponent of the actual formal monomial. -/
theorem tallyRow_parameter {R h u b : ℕ} (t : Diagonal.Tally (Fin R) (Fin h) (Fin u) b)
    (p : Fin h) : (∑ i, tallyRow t i (Fin.castAdd u p)) = t.exponents p := by
  classical
  simp [tallyRow, Fin.append_left, Diagonal.Tally.exponents, Diagonal.batchExponent,
    Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- Each chosen gadget entry contributes its multiplicity even if that entry has value zero. -/
theorem tallyRow_gadget {R h u b : ℕ} (t : Diagonal.Tally (Fin R) (Fin h) (Fin u) b)
    (g : Fin u) : (∑ i, tallyRow t i (Fin.natAdd h g)) = ∑ i, t.counts i g := by
  simp only [tallyRow, Fin.append_right]

/-- Verifying every team's own broadcast row forces the entire array. -/
theorem unique_claims {R d : ℕ} (a : Fin R → Fin d → ℕ) :
    ∃! claim : Fin R → Fin d → ℕ, ∀ team coord, claim team coord = a team coord :=
  ⟨a, fun _ _ => rfl, fun _ h => funext fun i => funext fun j => h i j⟩

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
