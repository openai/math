import OAI.Computability.NearSquareRoot.SynchronizedPermutationQuery
import OAI.Computability.NearSquareRoot.PermutationLayoutBatch

/-! # The compiled Fourier switch stage on the original physical address -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader
open IntegerMultiplication Code Adic Controlled Controlled.PermutationLayout BoxFin

variable {p b G low c L : ℕ} {box : List (ℕ × ℕ)} [∀ i, NeZero (modulus box i)]

/-- The controls on the target word are literal queries into the represented batch
tables, evaluated on the bits extracted from the prepared prefix. -/
def switchControl {d : ℕ} (width : Fin d → ℕ) (t : Fin d → RawTable) (subset : Fin b → Fin d)
    (slot : (q : Fin d) → Fin (width q) → ℕ) (side : Bool) (j : ℕ) (prefixBits : Block 2 p)
    (q : Fin b) : Bool :=
  queryBit (query (width (subset q)) (t (subset q)) side j
    (prefixWordAt (slot (subset q)) (List.ofFn (Controlled.prefixBit prefixBits))))

/-- Every switch query in the selected batch is assembled from the actual raw header
and the data prefix. There is one output bit for every active target in order. -/
theorem queries_switchControl {d k : ℕ} (width : Fin d → ℕ) (t : Fin d → RawTable)
    (subset : Fin b → Fin d) (port : (q : Fin d) → Fin (width q) → Fin k)
    (natural : ∀ q i, (port q i).val = FieldDirectory.position width q i)
    (relative : Fin k → ℕ) (side : Bool) (j : ℕ) (z : Block 2 p) :
    (queries (((side,tally j),(List.ofFn (fun q => (tally (width q),t q)),List.ofFn fun u => tally (relative u)),
      List.ofFn fun q => tally (subset q).val),List.ofFn (Controlled.prefixBit z))).map queryBit =
        List.ofFn (switchControl width t subset (fun q i => relative (port q i)) side j z) := by
  rw [queries,plan_eq width t subset port natural,buildBatch_plan]
  simp only [List.map_ofFn]
  rfl

variable (hb : BoxShape.Valid (maskWidth p b G low) L box) (hd : 4 ≤ box.length)
  (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ maskWidth p b G low)
  (π : Equiv.Perm (Fin (maskWidth p b G low)))

/-- The conjugated, computed batch realizes the selected switch operations on every
natural record position, including spare entries of the padded residue box. -/
theorem execute_batch (which : Fin (box.length/4) → ℕ) (tables : Fin (box.length/4) → RawTable)
    (stage : Bool × ℕ) (batch : ℕ) (active : Fin b → Fin (box.length/4))
    (wide : ∀ q, stage.2 < physicalWidth (box := box) (active q))
    (selected : ∀ q, which (active q) = batch)
    (complete : ∀ j, which j = batch → stage.2 < physicalWidth (box := box) j → ∃ q, active q = j)
    (placed : ∀ q, π (targetPos pos fit q) = packedPort hb hd ⟨active q,⟨stage.2,wide q⟩⟩)
    (covered : ∀ q (i : Fin (physicalWidth (box := box) (active q))), i.val ≠ stage.2 →
      ∃ a : Fin c, π (controlPos fit a) = packedPort hb hd ⟨active q,i⟩)
    (cert : ∀ q, ∃ f : Equiv.Perm (Word (physicalWidth (box:=box) (active q))),
      RawRepresents f (tables (active q)))
    (y : Block 2 (maskWidth p b G low)) :
    let ctrl := switchControl (physicalWidth (box:=box)) tables active
      (fun q i => PermutationLayout.offset π G low b (packedPort hb hd ⟨q,i⟩)) stage.1 stage.2
    packedRecord hb hd (flatAddress 2 _ (naturalStage π ctrl y)) =
      batchStage which (physicalWidth (box:=box)) (fun _ : Unit => tables) stage batch
        (packedRecord hb hd (flatAddress 2 _ y)) := by
  intro ctrl
  apply natural_batch hb hd pos fit π ctrl which tables stage batch active wide selected complete placed
  intro q
  obtain ⟨f,hf⟩ := cert q
  let j : Fin (physicalWidth (box:=box) (active q)) := ⟨stage.2,wide q⟩
  have query := relocated_query pos fit π (fun i => packedPort hb hd ⟨active q,i⟩) hf stage.1 j
    (fun i hi => covered q i (fun eq => hi (Fin.ext eq))) y
  have word : (fun i => Controlled.prefixBit y (packedPort hb hd ⟨active q,i⟩)) =
      (packedRecord hb hd (flatAddress 2 _ y)).2 (active q) :=
    funext fun i => (packedRecord_blockBit hb hd y (active q) i).symm
  dsimp only [ctrl,switchControl]
  simpa only [word,j] using query

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI
