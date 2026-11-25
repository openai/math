import OAI.ThreeFlat.Diagonal.NetworkDiagonal
import OAI.ThreeFlat.Diagonal.ApproximateImage

namespace OAI
/-! # The rank gap on the shared row-major folding input

The folding estimate is stated on a linear tape of `chunks*a` dirty
bits. The machine's inactive half is a two-dimensional chunk/bit array.
The physical catalyst is the reindexed folding operator for exactly the
genuine chronological pin assignment of the block.
-/

namespace ThreeFlat.Diagonal.ApproximateImage

open ApproximatePort
open scoped BigOperators Classical

variable {F : Type*} [Field F] {chunks a n ns nt np d teams t : ℕ}

/-- Concatenate the fixed-size dirty words in increasing chunk-number order. -/
def halfBits : (Fin chunks → Fin a → Bool) ≃ (Fin (chunks*a) → Bool) where
  toFun x j := x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  invFun b i j := b (finProdFinEquiv (i,j))
  left_inv x := by funext i j; simp
  right_inv b := by funext j; exact congrArg b (finProdFinEquiv.apply_symm_apply j)

/-- Matrix of the trivalent evaluator with arbitrary fixed team/tick pins. -/
def foldMatrix {L p B : ℕ} (X : BitNetwork F (L*teams*p+2*B))
    (pins : Fin L → Fin teams → Fin p → Bool) : Matrix (Fin B → Bool) (Fin B → Bool) F := fun x y =>
  X.eval (fun i => match FoldInput.rowMajor.symm i with
    | .inl ((j,k),b) => pins j k b
    | .inr (side,b) => if side then y b else x b)

theorem catalyst_eq_fold (D : Fin d → Bool) (block : ℕ) (params : Fin np → Bool)
    (X : BitNetwork F ((n+1)*teams*pinCount d nt ns np a+2*(chunks*a)))
    (f : BlockFixing (n+1) (BitString a) (BitString a)) :
    catalyst X (select (nt:=nt) (ns:=ns) block params) D f =
      (foldMatrix X (fixingPins (tickPins D block params) f)).submatrix halfBits halfBits := by
  ext l r
  apply congrArg X.eval
  funext i
  obtain ⟨j,rfl⟩ := FoldInput.rowMajor.surjective i
  rcases j with ⟨⟨time,team⟩,bit⟩ | ⟨b,idx⟩
  · simp [select_tick]
  · obtain ⟨⟨chunk,bit⟩,rfl⟩ := finProdFinEquiv.surjective idx
    have eqn := @Equiv.symm_apply_apply _ _ (finProdFinEquiv (m:=chunks) (n:=a)) (chunk,bit)
    have h₁ := congrArg Prod.fst eqn
    have h₂ := congrArg Prod.snd eqn
    change (finProdFinEquiv (chunk,bit)).divNat=chunk at h₁
    change (finProdFinEquiv (chunk,bit)).modNat=bit at h₂
    simp [select_boundary, halfBits,h₁,h₂]

/-- Transfer the folding guarantee, with no physical pin consistency
assumptions, to the finite collection of chronological block fixings. -/
theorem fixing_defect (D : Fin d → Bool) (block : ℕ) (params : Fin np → Bool)
    (N : BitNetwork F (pinCount d nt ns np a))
    (X : BitNetwork F ((n+1)*teams*pinCount d nt ns np a+2*(chunks*a))) {R : ℕ}
    (hr : ∀ pins : Fin (n+1) → Fin teams → Fin (pinCount d nt ns np a) → Bool,
      (foldMatrix X pins - (∏ j, ∏ k, N.eval (pins j k)) • 1).rank ≤ R)
    (f : BlockFixing (n+1) (BitString a) (BitString a)) :
    (catalyst X (select (nt:=nt) (ns:=ns) block params) D f -
      ((∏ j : Fin (n+1), ∏ k : Fin teams, N.eval (fixingPins (tickPins D block params) f j k))) • 1).rank ≤ R := by
  let e := halfBits (chunks:=chunks) (a:=a)
  let pins : Fin (n+1) → Fin teams → Fin (pinCount d nt ns np a) → Bool := fixingPins (tickPins D block params) f
  let c := ∏ j, ∏ k, N.eval (pins j k)
  rw [catalyst_eq_fold]
  change ((foldMatrix X pins).submatrix e e - c • 1).rank ≤ R
  have eqn : (foldMatrix X pins).submatrix e e - c • 1 = (foldMatrix X pins - c • 1).submatrix e e := by
    ext l r
    simp [Matrix.submatrix_apply,Matrix.one_apply,e.injective.eq_iff]
  rw [eqn,Matrix.rank_submatrix]
  exact hr pins

end ThreeFlat.Diagonal.ApproximateImage

end OAI
