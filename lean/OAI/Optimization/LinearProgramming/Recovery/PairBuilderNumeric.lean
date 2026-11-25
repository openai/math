import OAI.Optimization.LinearProgramming.Recovery.PackedRows
import OAI.Optimization.LinearProgramming.Recovery.ResidualROM
import OAI.Optimization.LinearProgramming.Geometry.ResidualBitsCommon
import Init.Data.List.OfFn

/-! Normal-entry numerical row-packing and kernel-projection workers for the principal LP ROM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder
open RAM RAM.Block Matrix Elimination Compression
open _root_.OAI.Optimization.LinearProgramming.Geometry
open scoped Matrix

abbrev Within (B : ℕ) (m : Memory ℚ) := m.AllData (fun x => ratBits x ≤ B)
def rowROM : Program := RowPack.program.compile 0 ++ [.halt 0]
def rowTime (h n : ℕ) := rowBasisTime h n + RowPack.packTime h n + 1
def rowWidth (h n e : ℕ) := rowBasisBits h n (max 3 e)
def residualWidth (h n e : ℕ) := max (max 3 e) (max (gramWorkspaceBits h n e) (ResidualBitsCommon.residualEntryBits h n e))

theorem encoded_width {h n e : ℕ} (D : Matrix (Fin h) (Fin n) ℚ) (data : ∀ i j,ratBits (D i j) ≤ e) (j : ℕ) :
    ratBits ((encodedGramInput D)[j]?.getD 0) ≤ max 3 e := by
  by_cases valid : j < h*n
  · simpa only [encodedGramInput,List.getElem?_ofFn,valid,↓reduceDIte,Option.getD_some] using
      (data (finProdFinEquiv.symm (⟨j,valid⟩ : Fin (h*n))).1 (finProdFinEquiv.symm (⟨j,valid⟩ : Fin (h*n))).2).trans (le_max_right 3 e)
  · rw [List.getElem?_eq_none (by simpa only [length_encodedGramInput] using Nat.le_of_not_lt valid)]
    exact le_max_left 3 e

/-- The rank, packed independent span and local bit bound all describe the same actual execution. -/
theorem row_run {h n : ℕ} (D : Matrix (Fin h) (Fin n) ℚ) (e : ℕ) (data : ∀ i j,ratBits (D i j) ≤ e) :
    ∃ t c k, c+1 ≤ rowTime h n ∧ Eval (Within (rowWidth h n e)) RowPack.program
      (start [h,n] (encodedGramInput D)).memory c t ∧ t.index 165=k ∧ k ≤ h ∧ k ≤ n ∧
      PacksRows D (uniformRect k n (t.index 57) t) := by
  let B := max 3 e
  let M := rowWidth h n e
  let g := dotBitBound n B B
  have hB : B ≤ M := le_max_left _ _
  have hg : g ≤ M := (le_max_left g _).trans (le_max_right _ _)
  have hr : detRegisterBits h g ≤ M := (le_max_right g _).trans (le_max_right _ _)
  have h3 : 3 ≤ g := Nat.le_add_right _ _
  let A := rectangularTape h n (encodedGramInput D)
  have eq : A=D := gramInputMatrix_encoded D
  have ha (i : Fin h) (j : Fin n) : ratBits (A i j) ≤ B := encoded_width D data _
  obtain ⟨t,c,k,clock,ev,rank,le,rows,addr⟩:=RowPack.public_spec h n (encodedGramInput D) (fun x=>ratBits x ≤ M)
    (fun j=>(encoded_width D data j).trans hB) (h3.trans hg) (h3.trans hg)
    (fun q hq=>by simpa only [PrimalDual.ratBits_neg] using hq)
    (fun i j u=>(dotProduct_partial_bits (A i) (A j) (ha i) (ha j) u).trans hg)
    (fun S=>masked_bird_bits (A*Aᵀ) S (matrix_product_bits A Aᵀ ha (fun i j=>ha j i)) h3 hr)
  change PacksRows A _ at rows
  have cols : k ≤ n := by simpa using rows.independent.fintype_card_le_finrank
  rw [eq,←addr] at rows
  exact ⟨t,c,k,by unfold rowTime; omega,ev,rank,le,cols,rows⟩

/-- The exact residual for the second pack has a local bit bound independent of other caller cells. -/
theorem residual_run {h n : ℕ} (D : Matrix (Fin h) (Fin n) ℚ) (e : ℕ)
    (data : ∀ i j,ratBits (D i j) ≤ e) (independent : LinearIndependent ℚ D.row) :
    ∃ t c, c+1 ≤ ResidualROM.time h n ∧ Eval (Within (residualWidth h n e)) ResidualROM.block
      (start [h,n] (encodedGramInput D)).memory c t ∧ uniformRect n n (t.index 58) t=kernelRows D := by
  let W := residualWidth h n e
  have input : max 3 e ≤ W := le_max_left _ _
  have gram : gramWorkspaceBits h n e ≤ W := (le_max_left _ _).trans (le_max_right _ _)
  have residual : ResidualBitsCommon.residualEntryBits h n e ≤ W := (le_max_right _ _).trans (le_max_right _ _)
  have v := ResidualBitsCommon.weaken (uniformGramValues_ratBits D data) (fun _ hx => hx.trans gram)
    (fun x hx => by simpa only [PrimalDual.ratBits_neg] using hx)
  obtain ⟨t,c,clock,run,rows,addr,_⟩ := ResidualROM.block_spec D (fun x => ratBits x ≤ W)
    (fun j => (encoded_width D data j).trans input) independent v (fun i j => (ResidualBitsCommon.residual_unitBits D e data i j).trans residual)
  exact ⟨t,c,clock,run,by rw [addr]; exact rows⟩
end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
