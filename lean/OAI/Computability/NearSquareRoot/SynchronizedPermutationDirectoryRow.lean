import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectoryCorrect

/-! # The emitted Beneš tables execute the exact directed box row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord.PermDirectory

open IntegerMultiplication.Code Matrix BoxFin SynchronizedBlocks SynchronizedLayers.ScheduleProgram
open SynchronizedPadding

section Generic

variable {k L : ℕ} {box : List (ℕ × ℕ)} (h : BoxShape.Valid k L box) [∀ i, NeZero (modulus box i)]
  (hd : 4 ≤ box.length)

private theorem perm_adjoint {A : Type} [DecidableEq A] (p : Equiv.Perm A) :
    (p.toPEquiv.toMatrix : Matrix A A ℂ)ᴴ = p.symm.toPEquiv.toMatrix := by
  ext x y
  have hh : p.symm x = y ↔ p y = x := (Equiv.symm_apply_eq p).trans eq_comm
  simp only [conjTranspose_apply,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,Option.mem_some_iff,hh]
  split_ifs <;> simp

/-- A row whose decoded local slots are all permutations reads the inverse
of its coordinatewise push map in physical packed record order. -/
theorem row_source (r : Directed) (p : ∀ j, Equiv.Perm (BlockAddress (BoxAxis box) j))
    (hp : ∀ j, (readBlock r.2 j.val).elim (.permutation (Equiv.refl _)) (boxSlot (physicalLayout h) j) =
      .permutation (p j)) :
    (boxRow (physicalLayout h) hd r).submatrix (recordIndex h).symm (recordIndex h).symm =
      (permutationSource h hd (fun j => (push r.1 (p j)).symm)).toPEquiv.toMatrix := by
  let F := fun j z => (boxSlot (physicalLayout h) j z).matrix ((physicalLayout h).bits j)
  have block (j) : ((readBlock r.2 j.val).map (F j)).getD 1 = (p j).toPEquiv.toMatrix := by
    have H := hp j
    cases hz : readBlock r.2 j.val with
    | none =>
      simp only [hz,Option.elim_none,Slot.permutation.injEq] at H
      rw [← H]
      simp
    | some z =>
      simp only [hz,Option.elim_some] at H
      change (boxSlot (physicalLayout h) j z).matrix _ = _
      rw [H]
      rfl
  have R : rowMatrix F r.2 = (Equiv.piCongrRight p).toPEquiv.toMatrix := by
    unfold rowMatrix
    rw [funext block,tensorMatrix_blockPerm]
  let e := (recordIndex h).symm.trans (regroup hd _)
  change (if r.1 then (rowMatrix F r.2)ᴴ else rowMatrix F r.2).submatrix e e = _
  rw [R]
  cases hr : r.1
  · simpa only [Bool.false_eq_true,ite_false,push,Bool.cond_false,Equiv.symm_symm] using
      permutationSource_matrix h hd p
  · simp only [ite_true,perm_adjoint]
    exact permutationSource_matrix h hd (fun j => (p j).symm)

end Generic

section Actual

variable {k L : ℕ} (hb : BoxShape.Valid k L (CoprimeBox.box k)) [∀ i, NeZero (modulus (CoprimeBox.box k) i)]
  (long : 4 ≤ (CoprimeBox.box k).length)

/-- The tables computed from the direction, address width, and stage index are
precisely the per-block scattering tables of the actual directed matrix. -/
theorem directory_row (dir : Bool) (s : Fin (directedPlan (dir,tally k)).length)
    (hp : (directedPlan (dir,tally k))[s.val].2.1 = kindCode .permutation) :
    let r := (directedPlan (dir,tally k))[s.val]
    ∃ (p : ∀ j, Equiv.Perm (BlockAddress (BoxAxis (CoprimeBox.box k)) j))
        (tables : Fin ((CoprimeBox.box k).length/4) → Benes.RawTable),
      (∀ j, (directory (dir,tally k,tally s.val))[j.val]? =
        some (tally (physicalWidth (box := CoprimeBox.box k) j),tables j)) ∧
      (∀ j, let e := blockWord hb j
        Benes.RawRepresents (e.symm.trans ((p j).symm.trans e)) (tables j)) ∧
      (boxRow (physicalLayout hb) long r).submatrix (recordIndex hb).symm (recordIndex hb).symm =
        (permutationSource hb long p).toPEquiv.toMatrix := by
  let r := (directedPlan (dir,tally k))[s.val]
  have H := fun j => directory_represents hb dir s j hp
  dsimp only at H
  choose q t op entry graph using H
  refine ⟨fun j => (push r.1 (q j)).symm,t,entry,?_,row_source hb long r q op⟩
  intro j
  simpa only [Equiv.symm_symm] using graph j

/-- The logical sequence of Beneš switches generated from the computed
directory acts on every physical record by multiplication with the directed
complex matrix of the synchronized box. -/
theorem directory_scatter (dir : Bool) (s : Fin (directedPlan (dir,tally k)).length)
    (hp : (directedPlan (dir,tally k))[s.val].2.1 = kindCode .permutation)
    (D : ℕ) (hD : ∀ j, physicalWidth (box := CoprimeBox.box k) j ≤ D) :
    let r := (directedPlan (dir,tally k))[s.val]
    ∃ tables : Fin ((CoprimeBox.box k).length/4) → Benes.RawTable,
      (∀ j, (directory (dir,tally k,tally s.val))[j.val]? =
        some (tally (physicalWidth (box := CoprimeBox.box k) j),tables j)) ∧
      ∀ (v : Fin (2^k) → ℂ) (x : Fin (2^k)),
        let packed := packedRecord hb long
        let result := (Benes.executionOrder D).foldl (fun arr step =>
          Benes.scatter (Benes.packedStage (physicalWidth (box := CoprimeBox.box k))
            (fun _ : Unit => tables) step) arr) (v ∘ packed.symm)
        result (packed x) =
          (((boxRow (physicalLayout hb) long r).submatrix (recordIndex hb).symm (recordIndex hb).symm) *ᵥ v) x := by
  obtain ⟨p,ts,E,G,M⟩ := directory_row hb long dir s hp
  refine ⟨ts,E,?_⟩
  intro v x
  rw [M,permutationSource_mulVec hb long]
  exact packedPermutation_reads hb long p ts G D hD v x

end Actual
end ShortFourier.BatchWord.PermDirectory

end NearSquareRoot
end Computability
end OAI
