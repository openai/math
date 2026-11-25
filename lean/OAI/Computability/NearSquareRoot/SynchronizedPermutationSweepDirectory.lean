import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepFFT
import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectoryCorrect

/-! # Permutation of the generated Fourier row in physical tape order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord.PermDirectory

open Matrix IntegerMultiplication.Code SynchronizedBlocks SynchronizedPadding SynchronizedLayers
open SynchronizedLayers.ScheduleProgram BoxFin
open scoped Matrix

noncomputable section

variable {k L : ℕ} (h : BoxShape.Valid k L (CoprimeBox.box k))
  [∀ i, NeZero (modulus (CoprimeBox.box k) i)]

/-- Physical switch table read from one numbered directory entry. -/
def switchTable (dir : Bool) (s : ℕ) (b : Fin ((CoprimeBox.box k).length/4)) : Benes.RawTable :=
  ((directory (dir,tally k,tally s))[b.val]?.getD ([],[])).2

private def slotPermutation {A : Type} : Slot A → Equiv.Perm A
  | .permutation p => p
  | _ => Equiv.refl _

/-- Undirected local permutation in the indexed Fourier row, including idle blocks. -/
def localPermutation (r : Directed) (b : Fin ((CoprimeBox.box k).length/4)) :
    Equiv.Perm (BlockAddress (BoxAxis (CoprimeBox.box k)) b) :=
  slotPermutation ((readBlock r.2 b.val).elim (.permutation (Equiv.refl _)) (boxSlot (physicalLayout h) b))

/-- Source read by the directed permutation matrix. -/
def localSource (r : Directed) (b : Fin ((CoprimeBox.box k).length/4)) :=
  (push r.1 (localPermutation h r b)).symm

theorem switchTable_spec (dir : Bool) (s : Fin (directedPlan (dir,tally k)).length)
    (hp : (directedPlan (dir,tally k))[s.val].2.1 = kindCode .permutation)
    (b : Fin ((CoprimeBox.box k).length/4)) :
    let r := (directedPlan (dir,tally k))[s.val]
    let e := blockWord h b
    (readBlock r.2 b.val).elim (.permutation (Equiv.refl _)) (boxSlot (physicalLayout h) b) =
        .permutation (localPermutation h r b) ∧
      Benes.RawRepresents (e.symm.trans ((localSource h r b).symm.trans e)) (switchTable dir s.val b) := by
  obtain ⟨p,t,hp',ht,hr⟩ := directory_represents h dir s b hp
  dsimp only
  simp only [localPermutation,localSource,hp',slotPermutation,switchTable,ht,Option.getD_some,Equiv.symm_symm]
  exact ⟨trivial,hr⟩

/-- In natural tape order, the scheduled matrix is exactly the permutation induced
by its emitted Beneš tables. The row's direction bit takes the matrix adjoint. -/
theorem flat_permutationRow (hd : 4 ≤ (CoprimeBox.box k).length) (dir : Bool)
    (s : Fin (directedPlan (dir,tally k)).length)
    (hp : (directedPlan (dir,tally k))[s.val].2.1 = kindCode .permutation) :
    let r := (directedPlan (dir,tally k))[s.val]
    (boxRow (physicalLayout h) hd r).submatrix (recordIndex h).symm (recordIndex h).symm =
      (permutationSource h hd (localSource h r)).toPEquiv.toMatrix := by
  classical
  let r := (directedPlan (dir,tally k))[s.val]
  let p := localPermutation h r
  have perBlock (b : Fin ((CoprimeBox.box k).length/4)) :
      ((readBlock r.2 b.val).map (fun z => (boxSlot (physicalLayout h) b z).matrix ((physicalLayout h).bits b))).getD 1 =
        (p b).toPEquiv.toMatrix := by
    have hb : Slot.matrix ((physicalLayout h).bits b) ((readBlock r.2 b.val).elim
        (.permutation (Equiv.refl _)) (boxSlot (physicalLayout h) b)) = (p b).toPEquiv.toMatrix :=
      congrArg (Slot.matrix ((physicalLayout h).bits b)) (switchTable_spec h dir s hp b).1
    cases hr : readBlock r.2 b.val with
    | none => simpa only [hr,Option.elim_none,Slot.matrix,Equiv.toPEquiv_refl,PEquiv.toMatrix_refl,
        Option.map_none,Option.getD_none] using hb
    | some z => simpa only [hr,Option.elim_some,Slot.matrix,Option.map_some,Option.getD_some] using hb
  have undirected : rowMatrix (fun b z => (boxSlot (physicalLayout h) b z).matrix ((physicalLayout h).bits b)) r.2 =
      (Equiv.piCongrRight p).toPEquiv.toMatrix := by
    rw [rowMatrix,funext perBlock,tensorMatrix_blockPerm]
  have adjoint : (((Equiv.piCongrRight p).toPEquiv.toMatrix : Matrix _ _ ℂ)ᴴ) =
      (Equiv.piCongrRight (fun b => (p b).symm)).toPEquiv.toMatrix := by
    ext x y
    have he : (Equiv.piCongrRight (fun b => (p b).symm)) x = y ↔ (Equiv.piCongrRight p) y = x :=
      by
        change (Equiv.piCongrRight p).symm x = y ↔ _
        exact (Equiv.symm_apply_eq _).trans eq_comm
    simp only [conjTranspose_apply,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,Option.mem_some_iff,he]
    split_ifs <;> simp
  change (boxRow (physicalLayout h) hd r).submatrix _ _ = _
  rw [boxRow,undirected,Matrix.submatrix_submatrix]
  have orient : (if r.1 then ((Equiv.piCongrRight p).toPEquiv.toMatrix : Matrix _ _ ℂ)ᴴ
      else (Equiv.piCongrRight p).toPEquiv.toMatrix) =
      (Equiv.piCongrRight (localSource h r)).toPEquiv.toMatrix := by
    have f : localSource h r = fun b => (push r.1 (p b)).symm := rfl
    rw [f]
    cases r.1 <;> simp [push,adjoint]
  rw [orient]
  exact permutationSource_matrix h hd (localSource h r)

end
end ShortFourier.BatchWord.PermDirectory

end NearSquareRoot
end Computability
end OAI
