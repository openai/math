import OAI.Computability.BorderVNP.ParseBatchVerifierLeavesQuery
import OAI.Computability.BorderVNP.ParseBatchVerifierLeavesBatch
import OAI.Computability.BorderVNP.ParseBatchVerifierConjunction
import OAI.Computability.BorderVNP.ParseBatchBitSum

/-!
# Composing the structure and leaf verifiers

The root, interval and child-read checks have only raw records as inputs.
The leaf check also reads the external query. The conjunction rejects malformed
records before using any implication about the leaf labels on decoded records.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchTrees

open VPVNP VPVNP.VerifierNetwork BorderVNP.ParseRecords
open BorderVNP.ParseBatchLeaves (Inputs)
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {m g n r : ℕ}

/-- Free bits of the structure verifier for one block. -/
abbrev RowPins (m g n : ℕ) (d : Fin n) := Fin (2*d.val+1) × BitSlot (recordWidth m g n)

/-- A single query and its raw preorder guesses. -/
abbrev TreePins (m g n : ℕ) (d : Fin n) := Inputs m g n (2*d.val+1)

/-- Apply the record-only verifier and the leaf multiset circuit to the same raw
bits, and conjoin their Boolean results. -/
noncomputable def checkTree (d : Fin n) (shape : Frame (RowPins m g n d) Unit) :
    Frame (TreePins m g n d) Unit :=
  (Crossing.parallelFrame (shape.subst (Frame.initial Sum.inr))
    (ParseBatchLeaves.frame m g n (2*d.val+1) (Nat.clog 2 (2*d.val+1)))).step
      fun _ => .and (.input (.inl ())) (.input (.inr ()))

/-- A raw assignment is structure-valid when its fields decode to a valid preorder block. -/
def Structure (d : Fin n) (h : Fin g) (bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool) :
    Prop := ∃ rs, readBlock m g n (List.ofFn bs) = some rs ∧ Valid d h rs

/-- The entire one-tree test on arbitrary raw guesses. -/
theorem checkTree_eval (d : Fin n) (h : Fin g) (hm : m = d.val+1)
    (shape : Frame (RowPins m g n d) Unit)
    (hs : ∀ bs, shape.eval (fun ij => bs ij.1 ij.2) () = true ↔ Structure d h bs)
    (x : Fin m → Bool) (bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool) :
    (checkTree d shape).eval (Sum.elim x (fun ij => bs ij.1 ij.2)) () = true ↔ CheckedBits d h x bs := by
  let z : TreePins m g n d → Bool := Sum.elim x (fun ij => bs ij.1 ij.2)
  have hz : (Frame.initial (Sum.inr : RowPins m g n d → TreePins m g n d)).eval z =
      fun ij => bs ij.1 ij.2 := by funext ij; simp [z]
  change (checkTree d shape).eval z () = true ↔ _
  simp only [checkTree, Frame.step_eval, StatementCircuit.Expr.eval, Bool.and_eq_true,
    Crossing.parallelFrame_eval_inl, Crossing.parallelFrame_eval_inr, Frame.subst_eval, hz, hs]
  constructor
  · rintro ⟨⟨rs, hd, hv⟩, hleaf⟩
    exact ⟨rs, hd, hv, (ParseBatchLeaves.frame_eval_of_readBlock d x bs hd hm
      (Nat.le_pow_clog (by decide) _)).mp hleaf⟩
  · rintro ⟨rs, hd, hv, hl⟩
    exact ⟨⟨rs, hd, hv⟩, (ParseBatchLeaves.frame_eval_of_readBlock d x bs hd hm
      (Nat.le_pow_clog (by decide) _)).mpr hl⟩

/-- The shared gates of the structure and leaf circuits are each charged once. -/
theorem checkTree_size (d : Fin n) (shape : Frame (RowPins m g n d) Unit) :
    (checkTree d shape).size ≤ shape.size +
      (ParseBatchLeaves.frame m g n (2*d.val+1) (Nat.clog 2 (2*d.val+1))).size + 3 := by
  unfold checkTree
  apply (Frame.step_size_le _ _ 3 (by intro i; exact le_rfl)).trans
  simp

/-- External query ports and private raw record ports of the whole batch. -/
abbrev BatchPins (m g n r : ℕ) (d : Fin n) :=
  (Fin r × Fin m) ⊕ (Fin r × RowPins m g n d)

/-- Boolean assignment to all external and private ports. -/
def batchInput (d : Fin n) (x : Fin r → Fin m → Bool) (bs : ParseBatch.Guess m g n r d) :
    BatchPins m g n r d → Bool :=
  Sum.elim (fun ij => x ij.1 ij.2) (fun ij => bs ij.1 ij.2.1 ij.2.2)

private def treeWire (d : Fin n) (i : Fin r) : TreePins m g n d → BatchPins m g n r d :=
  Sum.elim (fun j => .inl (i,j)) (fun j => .inr (i,j))

/-- Assemble one copy of the verifier per tree and conjoin all result bits. No new
private guesses are introduced. -/
theorem exists_batch_of_tree (d : Fin n) (h : Fin g)
    (tree : Frame (TreePins m g n d) Unit)
    (he : ∀ x bs, tree.eval (Sum.elim x (fun ij => bs ij.1 ij.2)) () = true ↔ CheckedBits d h x bs) :
    ∃ f : Frame (BatchPins m g n r d) Unit,
      f.size ≤ 2 + r*(tree.size+2) ∧
      ∀ x bs, f.eval (batchInput d x bs) () = true ↔ ParseBatch.Accepted d h x bs := by
  let one (i : Fin r) := tree.subst (Frame.initial (treeWire d i))
  obtain ⟨p, hp, hv⟩ := Crossing.exists_parallelFrames (out := fun _ : Fin r => Unit) one
  let all (_ : Unit) := ParseBatchVerifier.every fun i : Fin r =>
    (.input ⟨i,()⟩ : Expr (Σ _ : Fin r, Unit))
  refine ⟨p.step all, ?_, ?_⟩
  · have ha : ∀ i, (all i).size ≤ 2*r+1 := fun _ =>
      ParseBatchVerifier.every_size _ 1 (fun _ => le_rfl)
    have ht := Frame.step_size_le p all (2*r+1) ha
    simp only [one, Frame.subst_size, Frame.initial_size, zero_add, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hp
    simp only [Fintype.card_unit, one_mul] at ht
    rw [Nat.mul_add, Nat.mul_comm r 2]
    omega
  · intro x bs
    simp only [Frame.step_eval, all, ParseBatchVerifier.every_eval]
    change (∀ i, p.eval (batchInput d x bs) ⟨i,()⟩ = true) ↔ _
    simp_rw [hv]
    have hraw (i : Fin r) : (Frame.initial (treeWire (m := m) (g := g) d i)).eval (batchInput d x bs) =
        Sum.elim (x i) (fun ij => bs i ij.1 ij.2) := by
      funext j; cases j <;> simp [treeWire, batchInput]
    simp only [one, Frame.subst_eval, hraw, he, ParseBatch.Accepted]

end ParseBatchTrees

end BorderVNP
end Computability
end OAI
