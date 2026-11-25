import OAI.Computability.BorderVNP.PackedDeckChoice
import OAI.Computability.BorderVNP.PackedDeckCandidateWord

/-! # Comparing signed numerators by cross-adding nonnegative score channels -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckCandidate

open ParseBatchSort ParseBatchVerifier VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {m s : ℕ}

/-- The positive and negative score words at each original candidate ordinal. -/
abbrev ScorePin (m s : ℕ) := Fin m × Bool × Fin s

/-- Value of a score channel. The false tag is positive and the true tag is negative. -/
def channel (x : ScorePin m s → Bool) (i : Fin m) (neg : Bool) : ℕ := value fun j => x (i,neg,j)

private def field (i : Fin m) (neg : Bool) : Fin (s+1) → Expr (ScorePin m s) :=
  Fin.cons (.const false) (fun j => .input (i,neg,j))

private theorem field_value (x : ScorePin m s → Bool) (i : Fin m) (neg : Bool) :
    wordValue x (field i neg) = channel x i neg := by
  simp [wordValue, field, value, channel, StatementCircuit.Expr.eval]

private theorem field_size (i : Fin m) (neg : Bool) (j : Fin (s+1)) : (field i neg j).size = 1 := by
  exact Fin.cases rfl (fun _ => rfl) j

private noncomputable def cross (m s : ℕ) : Frame (ScorePin m s) ((Fin m × Fin m) × Fin (s+1)) :=
  (Frame.initial id).step fun ijb => addWord (field ijb.1.1 false) (field ijb.1.2 true) ijb.2

private theorem cross_value (x : ScorePin m s → Bool) (i j : Fin m) :
    value (fun b => (cross m s).eval x ((i,j),b)) = channel x i false + channel x j true := by
  have hid : (Frame.initial (id : ScorePin m s → _)).eval x = x := funext (Frame.initial_eval id x)
  simp only [cross, Frame.step_eval, hid]
  change wordValue x (addWord _ _) = _
  have h₁ := value_lt (fun j : Fin s => x (i,false,j))
  have h₂ := value_lt (fun b : Fin s => x (j,true,b))
  rw [addWord_value, field_value, field_value]
  simp only [field_value, channel, pow_succ]
  omega

private def before (i : Fin m) : Expr ((Fin m × Fin m) × Fin (s+1)) :=
  every fun j : Fin m => if j < i then .not (leExpr (fun k => ((j,i),k)) (fun k => ((i,j),k)))
    else leExpr (fun k => ((i,j),k)) (fun k => ((j,i),k))

/-- One-hot first minimum with exact comparisons of signed channels, including ties. -/
noncomputable def compare (m s : ℕ) : Frame (ScorePin m s) (Fin m) := (cross m s).step before

theorem compare_size (m s : ℕ) : (compare m s).size ≤
    m*m*(s+1)*(16*(s+1)+22) + m*((15*(s+1)+3)*m+1) := by
  have hs := Frame.step_size_le (Frame.initial (id : ScorePin m s → _))
    (fun ijb : (Fin m × Fin m) × Fin (s+1) => addWord (field ijb.1.1 false) (field ijb.1.2 true) ijb.2)
    (16*(s+1)+22) (fun ijb => sumWord_size_le false _ _ 1 (fun j => (field_size ..).le) (fun j => (field_size ..).le) ijb.2)
  change (cross m s).size ≤ _ at hs
  simp only [Frame.initial_size, zero_add, Fintype.card_fin, Fintype.card_prod] at hs
  have hb (i : Fin m) : (before (s := s) i).size ≤ (15*(s+1)+3)*m+1 := by
    apply every_size _ (15*(s+1)+2)
    intro j
    split <;> simp [StatementCircuit.Expr.size, leExpr_size]
  have hc := Frame.step_size_le (cross m s) before _ hb
  simpa only [compare, Fintype.card_fin] using hc.trans (Nat.add_le_add_right hs _)

/-- The hardware comparison agrees with the actual first minimum of any score function whose
weak order is that of the cross sums. -/
theorem compare_eval {S : Type*} [LinearOrder S] (x : ScorePin m s → Bool) (f : Fin m → S)
    (order : ∀ i j, channel x i false + channel x j true ≤ channel x j false + channel x i true ↔ f i ≤ f j)
    (i : Fin m) : (compare m s).eval x i = true ↔ (List.finRange m).argmin f = some i := by
  let z := (cross m s).eval x
  have val (i j : Fin m) : value (z ∘ (fun b => ((i,j),b))) = channel x i false + channel x j true := cross_value x i j
  have one (j : Fin m) : ((if j < i then StatementCircuit.Expr.not (leExpr (fun k => ((j,i),k)) (fun k => ((i,j),k)))
        else leExpr (fun k => ((i,j),k)) (fun k => ((j,i),k)))).eval z = true ↔
      if j < i then f i < f j else f i ≤ f j := by
    by_cases h : j < i <;> simp [h, StatementCircuit.Expr.eval, leExpr_eval, val, order]
  rw [compare, Frame.step_eval]
  change (before i).eval z = true ↔ _
  simp only [before, every_eval, one, List.argmin_eq_some_iff, List.mem_finRange, true_and,
    true_implies, List.idxOf_finRange]
  constructor
  · intro h
    constructor
    · intro j
      by_cases hji : j < i
      · exact (show f i < f j by simpa [hji] using h j).le
      · simpa [hji] using h j
    · intro j hj
      by_contra! hji
      have hlt : j < i := hji
      exact (not_lt_of_ge hj) (by simpa [hlt] using h j)
  · rintro ⟨hm,ht⟩ j
    by_cases hji : j < i
    · rw [ite_eq_left hji]
      exact lt_of_not_ge (fun h => hji.not_ge (ht j h))
    · simpa [hji] using hm j

end PackedDeckCandidate

end BorderVNP
end Computability
end OAI
