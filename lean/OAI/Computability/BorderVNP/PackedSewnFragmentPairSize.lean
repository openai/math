import OAI.Computability.BorderVNP.PackedSewnFragmentPairGate

/-! # Size of a two-fragment coalescing frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open VPVNP.VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private eqWord_size from OAI.Computability.BorderVNP.ParseBatchRowFrame

namespace PairGate

private theorem load_size {w : ℕ} (p : Mid w) :
    (loadBit p).size ≤ 16*w+22 := by
  rcases p with p | ⟨k,j⟩
  · change 1 ≤ _; omega
  · exact sumWord_size_le false (inputWord false k.succ) (inputWord (decide (k = 1)) 2) 1
      (fun _ => le_rfl) (fun _ => le_rfl) j

private theorem merge_size (w : ℕ) : (merge (w := w)).size ≤ 90*w+25 := by
  have site := eqWord_size (rawWord (w := w) false 0) (rawWord true 0) (fun _ => le_rfl) (fun _ => le_rfl)
  have old := eqWord_size (sumWord (w := w) 0) (rawWord true 1) (fun _ => le_rfl) (fun _ => le_rfl)
  have source := eqWord_size (sumWord (w := w) 2) (rawWord true 3) (fun _ => le_rfl) (fun _ => le_rfl)
  simp only [merge,sameSource,flag,StatementCircuit.Expr.size]
  omega

private theorem output_size {w : ℕ} (p : Raw w) : (outputBit p).size ≤ 180*w+56 := by
  have hm := merge_size w
  rcases p with ⟨b,t | ⟨k,j⟩⟩
  · cases b <;> cases t <;> simp only [outputBit,flag,StatementCircuit.Expr.size] <;> omega
  · cases b
    · by_cases hk : k = 2 <;> simp [outputBit,hk,mux,rawWord,sumWord,StatementCircuit.Expr.size]
      omega
    · change 1 ≤ _; omega

end PairGate

/-- Gate count of both batches, including all the address adders and every output bit. -/
theorem pair_size_quadratic (w : ℕ) : (pair w).size ≤ 2000*(w+1)^2 := by
  open PairGate in
  have h := Frame.step_size_le (Frame.initial (id : Raw w → _)) loadBit _ load_size
  open PairGate in
  have hout := Frame.step_size_le (loaded w) outputBit _ output_size
  simp only [PairGate.Mid,PairGate.Raw,Column,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,
    Fintype.card_bool,Frame.initial_size,zero_add] at h hout
  change (PairGate.loaded w).size ≤ _ at h
  change (pair w).size ≤ _ at hout
  exact hout.trans ((Nat.add_le_add_right h _).trans (by nlinarith))

/-- The per-pair bound used for the sparse multi-row folding network. -/
theorem pair_size (w : ℕ) : (pair w).size ≤ 20000*(w+1)^3 := by
  exact (pair_size_quadratic w).trans (Nat.mul_le_mul (by decide)
    (Nat.pow_le_pow_right (Nat.succ_pos w) (by decide)))

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
