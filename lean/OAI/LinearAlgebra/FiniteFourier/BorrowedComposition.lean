import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization

/-! # Composition of additive operations on borrowed registers

A word adding a matrix may use arbitrary occupied workspace. Four signed updates
through an occupied intermediate array add the product of two matrices and restore
both the intermediate array and the workspace.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K : Type*} [CommRing K]
variable {X Y Z W : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W]

/-- A word for `(x,y,w) ↦ (x,y+Ax,w)`, allowing the workspace `w` to be occupied. -/
abbrev AdditiveWord (W : Type) [Fintype W] [DecidableEq W] (d : ℕ) (A : Matrix Y X K) : Prop :=
  LayerWord d (fromBlocks (fromBlocks 1 0 A 1) 0 0 (1 : Matrix W W K))

private theorem addIntermediate {d : ℕ} {A : Matrix Z X K} (h : AdditiveWord W d A) :
    LayerWord d (fromBlocks (1 : Matrix (X ⊕ Y) (X ⊕ Y) K) 0
      (fromBlocks A 0 0 (0 : Matrix W Y K)) 1) := by
  have h' := (LayerWord.enlargeWorkspace h (V := Y ⊕ W) (by simp)).relabel
    (Equiv.sumSumSumComm X Z Y W)
  convert h' using 1
  ext i j
  rcases i with ((x | y) | (z | w)) <;> rcases j with ((x' | y') | (z' | w')) <;>
    simp [submatrix, fromBlocks, Matrix.one_apply]

private theorem addOutput {d : ℕ} {B : Matrix Y Z K} (h : AdditiveWord W d B) :
    LayerWord d (fromBlocks (1 : Matrix (X ⊕ Y) (X ⊕ Y) K)
      (fromBlocks (0 : Matrix X Z K) 0 B (0 : Matrix Y W K)) 0 1) := by
  let e := (((Equiv.sumComm Z Y).sumCongr (Equiv.refl (X ⊕ W))).trans
      (Equiv.sumSumSumComm Y Z X W)).trans
      ((Equiv.sumComm Y X).sumCongr (Equiv.refl (Z ⊕ W)))
  have h' := (LayerWord.enlargeWorkspace h (V := X ⊕ W) (by simp)).relabel e
  convert h' using 1
  ext i j
  rcases i with ((x | y) | (z | w)) <;> rcases j with ((x' | y') | (z' | w')) <;>
    simp [e, submatrix, fromBlocks, Matrix.one_apply]

/-- Four signed updates add `B * A` and restore the occupied intermediate array `Z`. -/
theorem AdditiveWord.mul {d e : ℕ} {A : Matrix Z X K} {B : Matrix Y Z K}
    (hA : AdditiveWord W d A) (hnA : AdditiveWord W d (-A))
    (hB : AdditiveWord W e B) (hnB : AdditiveWord W e (-B)) :
    AdditiveWord (Z ⊕ W) (2 * (d + e)) (B * A) := by
  let a := fromBlocks A 0 0 (0 : Matrix W Y K)
  let b := fromBlocks (0 : Matrix X Z K) 0 B (0 : Matrix Y W K)
  have hab : a * b = 0 := by simp [a, b, fromBlocks_multiply]
  have hna : LayerWord d (fromBlocks 1 0 (-a) 1) := by
    simpa only [a, fromBlocks_neg, neg_zero] using addIntermediate (Y := Y) hnA
  have hnb : LayerWord e (fromBlocks 1 (-b) 0 1) := by
    simpa only [b, fromBlocks_neg, neg_zero] using addOutput (X := X) hnB
  have h := layerWord_mul hnb (layerWord_mul hna
    (layerWord_mul (addOutput (X := X) hB) (addIntermediate (Y := Y) hA)))
  change LayerWord (e + (d + (e + d)))
    (fromBlocks 1 (-b) 0 1 * (fromBlocks 1 0 (-a) 1 * (fromBlocks 1 b 0 1 * fromBlocks 1 0 a 1))) at h
  rw [show e + (d + (e + d)) = 2 * (d + e) by omega] at h
  unfold AdditiveWord
  convert h using 1
  simp [fromBlocks_multiply, Matrix.mul_add, ← Matrix.mul_assoc, hab, a, b]
  rw [← fromBlocks_one (l := X) (m := Y), fromBlocks_add]
  simp

/-- Applying the four updates twice realizes a three-factor product on arbitrary
occupied intermediate arrays. -/
theorem AdditiveWord.mul_three {V : Type} [Fintype V] [DecidableEq V] {d e f : ℕ}
    {A : Matrix Z X K} {B : Matrix V Z K} {C : Matrix Y V K}
    (hA : AdditiveWord W d A) (hnA : AdditiveWord W d (-A))
    (hB : AdditiveWord W e B) (hnB : AdditiveWord W e (-B))
    (hC : AdditiveWord W f C) (hnC : AdditiveWord W f (-C)) :
    AdditiveWord (V ⊕ (Z ⊕ W)) (2 * (2 * (d + e) + f)) (C * B * A) := by
  have hBA := AdditiveWord.mul hA hnA hB hnB
  have hnBA : AdditiveWord (Z ⊕ W) (2 * (d + e)) (-(B * A)) := by
    rw [← Matrix.neg_mul]
    exact AdditiveWord.mul hA hnA hnB (by simpa using hB)
  rw [Matrix.mul_assoc]
  exact AdditiveWord.mul hBA hnBA
    (LayerWord.enlargeWorkspace hC (by simp)) (LayerWord.enlargeWorkspace hnC (by simp))

end FiniteFourier
end LinearAlgebra
end OAI
