import OAI.Computability.NearSquareRoot.SynchronizedPermutationActual

/-! # Reading a native batched switch through the declared operand width -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader
open IntegerMultiplication Adic Controlled Controlled.PermutationLayout BoxFin

/-- Change only the declared number of address bits; the underlying word and rank stay fixed. -/
def castWord {a k : ℕ} (e : a=k) : Block 2 a ≃ Block 2 k := Equiv.cast (congrArg (Block 2) e)

theorem castWord_rank {a k : ℕ} (e : a=k) (y : Block 2 a) :
    flatAddress 2 k (castWord e y) = Fin.cast (congrArg (2^·) e) (flatAddress 2 a y) := by
  cases e
  rfl

variable {k L p b G low : ℕ} {box : List (ℕ × ℕ)} [∀ i, NeZero (modulus box i)]
variable (hb : BoxShape.Valid k L box) (hd : 4 ≤ box.length)

/-- Natural physical ranks read as the fields of the factor box. -/
noncomputable def recordAddress : Block 2 k ≃ PackedAddress Unit (physicalWidth (box:=box)) :=
  (flatAddress 2 k).trans (packedRecord hb hd)

noncomputable def declaredStage (e : maskWidth p b G low=k) (π : Equiv.Perm (Fin (maskWidth p b G low)))
    (ctrl : Block 2 p → Fin b → Bool) (y : Block 2 k) :=
  castWord e (naturalStage π ctrl ((castWord e).symm y))

variable {out : Staging} {tables : Fin (box.length/4) → RawTable} {which : Fin (box.length/4) → ℕ}
  {stage : Bool × ℕ} {batch : ℕ}

universe u

/-- The literal sparse-mask program pulls arbitrary payloads through the same permutation
that the batched switch scatters. Both the layout-width and declared-width forms are given. -/
theorem RealizesBatch.pull (h : RealizesBatch (p:=p) (b:=b) (G:=G) (low:=low) hb hd out tables which stage batch) :
    let net := batchStage which (physicalWidth (box:=box)) (fun _ : Unit => tables) stage batch
    ∃ e : maskWidth p b G low=k, ∃ π : Equiv.Perm (Fin (maskWidth p b G low)), ∃ ctrl : Block 2 p → Fin b → Bool,
      out.1 = (Reflections.table π,Reflections.table π.symm) ∧
      (∀ z, maskBits (out,List.ofFn (Controlled.prefixBit z)) = List.ofFn (ctrl z)) ∧
      Function.Involutive (naturalStage π ctrl) ∧
      (∀ {V : Type u} (f : PackedAddress Unit (physicalWidth (box:=box)) → V) y,
        f (recordAddress hb hd (castWord e (naturalStage π ctrl y))) =
          scatter net f (recordAddress hb hd (castWord e y))) ∧
      ∀ {V : Type u} (f : PackedAddress Unit (physicalWidth (box:=box)) → V) y,
        f (recordAddress hb hd (declaredStage e π ctrl y)) = scatter net f (recordAddress hb hd y) := by
  intro net
  obtain ⟨e,π,ctrl,emitted,mask,act⟩ := h
  have comm (y) : recordAddress hb hd (castWord e (naturalStage π ctrl y)) =
      net (recordAddress hb hd (castWord e y)) := by
    simpa only [recordAddress,Equiv.trans_apply,castWord_rank] using act y
  have inv : net.symm = net := batchStage_selfInverse ..
  have pull {V : Type u} (f : PackedAddress Unit (physicalWidth (box:=box)) → V) y :
      f (recordAddress hb hd (castWord e (naturalStage π ctrl y))) =
        scatter net f (recordAddress hb hd (castWord e y)) := by
    change _ = f (net.symm _)
    rw [inv,comm]
  refine ⟨e,π,ctrl,emitted,mask,?_,@pull,?_⟩
  · intro y
    apply (castWord e).injective
    apply (recordAddress hb hd).injective
    rw [comm,comm]
    simpa only [inv] using net.symm_apply_apply (recordAddress hb hd (castWord e y))
  · intro V f y
    simpa only [declaredStage,Equiv.apply_symm_apply] using pull f ((castWord e).symm y)

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI
