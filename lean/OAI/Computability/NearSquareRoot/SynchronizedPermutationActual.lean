import OAI.Computability.NearSquareRoot.SynchronizedPermutationNative
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSeed
import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectoryRow

/-! # Native bit-address realization of the actual Fourier permutation row directory -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader
open IntegerMultiplication Code Adic Controlled Controlled.PermutationLayout BoxFin
open ShortFourier.BatchWord SynchronizedPermutationBudget
open SynchronizedLayers SynchronizedLayers.ScheduleProgram

private theorem packed_cast {k k' L : ℕ} {box : List (ℕ × ℕ)} [∀ i, NeZero (modulus box i)]
    (ha : BoxShape.Valid k L box) (hb : BoxShape.Valid k' L box) (hd : 4 ≤ box.length)
    (e : k=k') (v : Fin (2^k)) : packedRecord ha hd v =
        packedRecord hb hd (Fin.cast (congrArg (2^·) e) v) := by
  subst k'
  rfl

/-- Exact behavior of one compiled pass on the entire native array, with both
position sweeps and the evaluated per-row control word fixed by the raw header. -/
def RealizesBatch {k L p b G low : ℕ} {box : List (ℕ × ℕ)} [∀ i, NeZero (modulus box i)]
    (hb : BoxShape.Valid k L box) (hd : 4 ≤ box.length) (out : Staging)
    (tables : Fin (box.length/4) → RawTable) (which : Fin (box.length/4) → ℕ)
    (stage : Bool × ℕ) (batch : ℕ) : Prop :=
  ∃ e : maskWidth p b G low = k, ∃ π : Equiv.Perm (Fin (maskWidth p b G low)),
    ∃ ctrl : Block 2 p → Fin b → Bool,
      out.1 = (Reflections.table π,Reflections.table π.symm) ∧
      (∀ z, maskBits (out,List.ofFn (Controlled.prefixBit z)) = List.ofFn (ctrl z)) ∧
      ∀ y, let rank := fun w => Fin.cast (congrArg (2^·) e) (flatAddress 2 _ w)
        packedRecord hb hd (rank (naturalStage π ctrl y)) =
          batchStage which (physicalWidth (box:=box)) (fun _ : Unit => tables) stage batch (packedRecord hb hd (rank y))

private abbrev W (k : ℕ) := physicalWidth (box := CoprimeBox.box k)
def live (k β j : ℕ) := (FieldDirectory.activeBlocks k β j (W k)).length
def highBits (D k β j : ℕ) := k-(2*((live k β j+1)*guardWidth k)+payloadBits D k)

variable {k L D : ℕ} [∀ i,NeZero (modulus (CoprimeBox.box k) i)]
  (hb : BoxShape.Valid k L (CoprimeBox.box k)) (hd : 4 ≤ (CoprimeBox.box k).length)
  (budget : BoxPasses k D 2) (dir : Bool) (row : Tally) (side : Bool) (j β : ℕ)
  (tables : Fin ((CoprimeBox.box k).length/4) → RawTable)

include budget
set_option maxHeartbeats 1200000 in
theorem fullHeader_batch
    (entries : ∀ q, (PermDirectory.directory (dir,tally k,row))[q.val]? = some (tally (W k q),tables q))
    (cert : ∀ q, ∃ f : Equiv.Perm (Word (W k q)), RawRepresents f (tables q)) :
    RealizesBatch (p:=highBits D k β j) (b:=live k β j) (G:=guardWidth k) (low:=payloadBits D k)
      hb hd (fullHeader D ((dir,tally k,row),(side,tally j),tally β)) tables
      (fun q => q.val / capacity k) (side,j) β := by
  let active := FieldDirectory.selectBlock k β j (W k)
  have good := FieldDirectory.selectBlock_live k β j (W k)
  have wide (q) : j < W k (active q) := (good q).2
  have chosen (q) : (active q).val / capacity k = β := (good q).1
  have all (q) (hs : q.val / capacity k = β) (hj : j < W k q) : ∃ a, active a = q :=
    (FieldDirectory.selectBlock_range k β j (W k) q).mpr ⟨hs,hj⟩
  have bound := FieldDirectory.activeLayout_le (W k) budget.width_bound budget.fits budget.reserves β j
  dsimp only at bound
  have cnt := FieldDirectory.controlCount_eq (W k) active j wide
  let c := FieldDirectory.controlCount (W k) active j
  have cap : payloadBits D k+2*((live k β j+1)*guardWidth k)+c ≤ k := by
    change payloadBits D k+2*(((FieldDirectory.activeBlocks k β j (W k)).length+1)*guardWidth k)+
      FieldDirectory.controlCount (W k) active j ≤ k
    rw [cnt]
    dsimp only [active]
    omega
  have pos : 0 < guardWidth k := by unfold guardWidth; omega
  have eq : maskWidth (highBits D k β j) (live k β j) (guardWidth k) (payloadBits D k) = k := by
    rw [maskWidth_eq _ _ _ _ pos,highBits]
    omega
  let h' : BoxShape.Valid (maskWidth (highBits D k β j) (live k β j) (guardWidth k) (payloadBits D k)) L
      (CoprimeBox.box k) := eq.symm ▸ hb
  have fit : payloadBits D k+2*((live k β j+1)*guardWidth k)+c ≤
      maskWidth (highBits D k β j) (live k β j) (guardWidth k) (payloadBits D k) := eq.symm ▸ cap
  have result := native_seed h' hd tables active active.injective (fun q => q.val / capacity k) (side,j) β
    wide chosen all pos fit (fun q => cert (active q))
  dsimp only at result
  rw [RealizesBatch,fullHeader_eq hb D dir row side j β tables entries]
  obtain ⟨π,ctrl,emitted,read,action⟩ := result
  have front : prepare (seed (W k) tables active side j
      (maskWidth (highBits D k β j) (live k β j) (guardWidth k) (payloadBits D k)) (guardWidth k) (payloadBits D k)) =
      prepare (seed (W k) tables active side j k (guardWidth k) (payloadBits D k)) := by rw [eq]
  refine ⟨eq,π,ctrl,?_,?_,?_⟩
  · rw [← front]
    exact emitted
  · rw [← front]
    exact read
  · intro y
    simpa only [packed_cast h' hb hd eq] using action y

/-- One table family serves all live batches of this directed Fourier row. The full
synchronized switch order on the same tapes reads the exact ranked matrix product. -/
theorem fullHeaders_row (s : Fin (directedPlan (dir,tally k)).length)
    (kind : (directedPlan (dir,tally k))[s.val].2.1 = kindCode .permutation) :
    let r := (directedPlan (dir,tally k))[s.val]
    ∃ ts : Fin ((CoprimeBox.box k).length/4) → RawTable,
      (∀ (stage : Bool × ℕ) (β : ℕ),
        RealizesBatch (p:=highBits D k β stage.2) (b:=live k β stage.2) (G:=guardWidth k) (low:=payloadBits D k)
          hb hd (fullHeader D ((dir,tally k,tally s.val),(stage.1,tally stage.2),tally β)) ts
          (fun q => q.val / capacity k) stage β) ∧
      ∀ (v : Fin (2^k) → ℂ) (x : Fin (2^k)),
        let packed := packedRecord hb hd
        let result := (executionOrder (SynchronizedPermutationBudget.width k)).foldl (fun arr step =>
          scatter (packedStage (W k) (fun _ : Unit => ts) step) arr) (v ∘ packed.symm)
        result (packed x) = (((boxRow (physicalLayout hb) hd r).submatrix
          (recordIndex hb).symm (recordIndex hb).symm).mulVec v) x := by
  obtain ⟨p,ts,entries,graph,matrix⟩ := PermDirectory.directory_row hb hd dir s kind
  refine ⟨ts,?_,?_⟩
  · intro stage β
    exact fullHeader_batch hb hd budget dir (tally s.val) stage.1 stage.2 β ts entries
      (fun q => ⟨_,graph q⟩)
  · intro v x
    rw [matrix,permutationSource_mulVec hb hd]
    exact packedPermutation_reads hb hd p ts graph _ budget.width_bound v x

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI
