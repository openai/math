import OAI.Computability.NearSquareRoot.SynchronizedNumberedBits
import OAI.Computability.NearSquareRoot.CRTControlledBenesParallel
import OAI.Computability.NearSquareRoot.CRTTableWordEquiv

/-! # Effect of the grouped Beneš execution on the original register array -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open Matrix SynchronizedBlocks ShortFourier
noncomputable section

variable {box : List (ℕ × ℕ)} {k L : ℕ} (hb : BoxShape.Valid k L box)
  [∀ i, NeZero (modulus box i)] (hd : 4 ≤ box.length)

/-- Serialize each contiguous block as a most-significant-first Beneš word. -/
def blockWord (j : Fin (box.length/4)) :
    BlockAddress (BoxAxis box) j ≃ Benes.Word (physicalWidth j) :=
  (blockBitRank hb j).trans (CRTTable.wordEquiv _)

/-- The single outer control lane and all grouped binary words of one tape array address. -/
def packedRecord : Fin (2^k) ≃ Benes.PackedAddress Unit (physicalWidth (box := box)) :=
  (recordIndex hb).symm.trans ((regroup hd _).trans
    ((Equiv.piCongrRight (blockWord hb)).trans (Equiv.uniqueProd (∀ j, Benes.Word (physicalWidth (box := box) j)) Unit).symm))

/-- The physical word in a group is its source tape field in most-significant-first order. -/
theorem packedRecord_field (t : Fin (2^k)) (j : Fin (box.length/4)) :
    List.ofFn ((packedRecord hb hd t).2 j) =
      (IntegerMultiplication.Bits.phrase (physicalWidth j)
        ((blockAddressRank hb j) ((regroup hd _ ((recordIndex hb).symm t)) j)).val).reverse :=
  CRTTable.ofFn_wordEquiv _ _

/-- Row destination is the source read by the tensor-stage permutation matrix. -/
def permutationSource (p : ∀ j, Equiv.Perm (BlockAddress (BoxAxis box) j)) : Equiv.Perm (Fin (2^k)) :=
  let e := (recordIndex hb).symm.trans (regroup hd _)
  e.trans ((Equiv.piCongrRight p).trans e.symm)

/-- A physical Beneš network scatters. To read the source specified by the
permutation matrix, scatter according to the inverse per-block table. -/
theorem packedPermutation_reads {V : Type} (p : ∀ j, Equiv.Perm (BlockAddress (BoxAxis box) j))
    (tables : Fin (box.length/4) → Benes.RawTable)
    (rep : ∀ j, let e := blockWord hb j
      Benes.RawRepresents (e.symm.trans ((p j).symm.trans e)) (tables j))
    (D : ℕ) (hD : ∀ j, physicalWidth (box := box) j ≤ D) (v : Fin (2^k) → V) (t : Fin (2^k)) :
    let packed := packedRecord hb hd
    let run := (Benes.executionOrder D).foldl (fun arr step =>
      Benes.scatter (Benes.packedStage (physicalWidth (box := box)) (fun _ : Unit => tables) step) arr)
      (v ∘ packed.symm)
    run (packed t) = v (permutationSource hb hd p t) := by
  let bits := blockWord hb
  let p' (_ : Unit) j := (bits j).symm.trans ((p j).symm.trans (bits j))
  have H := Benes.packedData_run (physicalWidth (box := box)) (fun _ : Unit => tables) p'
    (fun _ j => rep j) D hD (v ∘ (packedRecord hb hd).symm)
  dsimp only
  rw [H]
  change v ((packedRecord hb hd).symm ((Benes.controlledPerm p').symm (packedRecord hb hd t))) = _
  congr 1
  apply (packedRecord hb hd).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact Subsingleton.elim ..
  · funext j
    let a := regroup hd _ ((recordIndex hb).symm t)
    change (p' () j).symm (bits j (a j)) = bits j ((regroup hd _ ((recordIndex hb).symm (permutationSource hb hd p t))) j)
    simp only [p',Equiv.symm_trans_apply,Equiv.symm_symm,Equiv.symm_apply_apply]
    congr 1
    change _ = (regroup hd _ ((recordIndex hb).symm ((recordIndex hb)
      ((regroup hd _).symm ((Equiv.piCongrRight p) a))))) j
    rw [Equiv.symm_apply_apply,Equiv.apply_symm_apply]
    rfl

/-- The global slot matrix flattened in tape order is the actual source permutation matrix. -/
theorem permutationSource_matrix (p : ∀ j, Equiv.Perm (BlockAddress (BoxAxis box) j)) :
    let e := (recordIndex hb).symm.trans (regroup hd _)
    ((Equiv.piCongrRight p).toPEquiv.toMatrix : Matrix _ _ ℂ).submatrix e e =
      (permutationSource hb hd p).toPEquiv.toMatrix := by
  let e := (recordIndex hb).symm.trans (regroup hd _)
  ext x y
  change (if e y ∈ (Equiv.piCongrRight p).toPEquiv (e x) then (1 : ℂ) else 0) =
    (if y ∈ (permutationSource hb hd p).toPEquiv x then 1 else 0)
  simp only [Equiv.toPEquiv_apply,Option.mem_some_iff]
  apply if_congr _ rfl rfl
  change (Equiv.piCongrRight p) (e x) = e y ↔ e.symm ((Equiv.piCongrRight p) (e x)) = y
  constructor
  · intro he
    rw [he, Equiv.symm_apply_apply]
  · intro he
    rw [← he, Equiv.apply_symm_apply]

/-- Equality to the complex permutation matrix at every physical tape rank. -/
theorem permutationSource_mulVec (p : ∀ j, Equiv.Perm (BlockAddress (BoxAxis box) j))
    (x : Fin (2^k) → ℂ) :
    (permutationSource hb hd p).toPEquiv.toMatrix *ᵥ x = x ∘ permutationSource hb hd p :=
  PEquiv.toMatrix_toPEquiv_mulVec _ _

end
end BoxFin

end NearSquareRoot
end Computability
end OAI
