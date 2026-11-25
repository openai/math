import OAI.Computability.NearSquareRoot.SynchronizedPermutationTargetTape
import OAI.Computability.NearSquareRoot.SynchronizedBatchDecode
import OAI.Computability.NearSquareRoot.PrecisionGridSplitRank

/-! # Numerical source ranks for the block permutation slots

A permutation instruction uses the current axis as its column and the spectator
tuple as its row. The arithmetic query acts on flat row-major ranks in that
layout, including active fibers, borrowed workspace and padding.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open Matrix IntegerMultiplication Code Strip Staff SynchronizedBorrowing AxisWord

/-- Split out the selected axis field, apply its placed address query, and
reinsert the resulting field into the original packed address. -/
def packedTarget (low stride start v a r : ℕ) (f : ℕ → ℕ) (index : ℕ) : ℕ :=
  let dest := placedPermTarget start v a r f (FieldSplit.row low stride index) (FieldSplit.col low stride index)
  FieldSplit.join low stride dest.1 dest.2

theorem packedTarget_realizes {I : Type} {s : Regime I} {low stride start v a r index : I → ℕ}
    {f : I → ℕ → ℕ} (P : Realizes s low) (W : Realizes s stride) (Start : Realizes s start)
    (V : Realizes s v) (A : Realizes s a) (R : Realizes s r) (Q : Realizes s index)
    (F : ∀ t, Realizes s t → Realizes s (fun i => f i (t i))) :
    Realizes s (fun i => packedTarget (low i) (stride i) (start i) (v i) (a i) (r i) (f i) (index i)) := by
  let dest := fun i => placedPermTarget (start i) (v i) (a i) (r i) (f i)
    (FieldSplit.row (low i) (stride i) (index i)) (FieldSplit.col (low i) (stride i) (index i))
  have H : s.Has (fun i => PlacedPermutationTape.coordinates (dest i)) :=
    PlacedPermutationTape.placedPermTarget_has Start V A R (FieldSplit.row_realizes P W Q)
      (FieldSplit.col_realizes P W Q) F
  have Row : Realizes s (fun i => (dest i).1) := H.ez Easy.fst
  have Col : Realizes s (fun i => (dest i).2) := H.ez Easy.snd
  exact FieldSplit.join_realizes P W Row Col

/-- The first field is the product of the lower radices. The two final fields
are the padded width of the selected axis and the requested packed index. -/
abbrev PackedQuery := Tally × OpcodeQuery
abbrev ValidPackedQuery := {q : PackedQuery // q.2.2.1.2.2.length = 2 ^ q.2.1.1.length}

def packedReply (z : PackedQuery) : Tally :=
  let q := z.2
  tally (packedTarget z.1.length q.2.2.1.length q.2.1.1.1.length q.2.1.1.2.length
    q.2.1.2.1.length q.2.1.2.2.length
    (permutationTarget q.1.1.length q.1.2.1.length q.1.2.2.length) q.2.2.2.length)

private def rankRegime : Regime ValidPackedQuery :=
  ⟨fun q => Code.size q.val, fun q => send q.val, Dom.base _⟩

private theorem rankField (f : PackedQuery → Tally) (hf : Easy f) :
    Realizes rankRegime (fun q => (f q.val).length) := by
  have h : rankRegime.Has (fun q => q.val) := rankRegime.self
  simpa only [Realizes, Function.comp_def, recover_tally] using h.ez hf

/-- A fixed multitape machine writes the packed source rank on valid headers.
Its time and visited space are polynomial in the encoded query size. -/
theorem packedReply_machine :
    PolyTreeMachine (fun q : ValidPackedQuery => Code.size q.val)
      (fun q => send q.val) (fun q => send (packedReply q.val)) := by
  apply polyTreeMachine_of_BT _ (Dom.base _)
  have extent (q : ValidPackedQuery) : q.val.2.2.1.2.2.length = 2 ^ q.val.2.1.1.length := q.property
  have R : Realizes rankRegime (fun q => 2 ^ q.val.2.1.1.length) := by
    simpa only [extent] using rankField (fun q => q.2.2.1.2.2) (by fun_prop)
  have h := packedTarget_realizes (s := rankRegime)
    (rankField (fun q => q.1) (by fun_prop)) (rankField (fun q => q.2.2.2.1) (by fun_prop))
    (rankField (fun q => q.2.2.1.1.1) (by fun_prop)) (rankField (fun q => q.2.2.1.1.2) (by fun_prop))
    (rankField (fun q => q.2.2.1.2.1) (by fun_prop)) R (rankField (fun q => q.2.2.2.2) (by fun_prop))
    (fun _ => permutationTarget_realizes (rankField (fun q => q.2.1.1) (by fun_prop)) R
      (rankField (fun q => q.2.1.2.1) (by fun_prop)) (rankField (fun q => q.2.1.2.2) (by fun_prop)))
  change rankRegime.Has (fun q => packedReply q.val)
  simpa only [packedReply, extent, Realizes, Function.comp_def] using h

/-- Spell the field widths, placement, opcode, and packed index as one tape query. -/
def packedQuery (low stride start v a k tag arg index : ℕ) : ValidPackedQuery :=
  ⟨(tally low, (tally k, tally tag, tally arg), ((tally start, tally v), (tally a, tally (2^k))),
    tally stride, tally index), by simp⟩

theorem packedReply_query (low stride start v a k tag arg index : ℕ) :
    packedReply (packedQuery low stride start v a k tag arg index).val =
      tally (packedTarget low stride start v a (2^k) (permutationTarget k tag arg) index) := by
  simp [packedReply, packedQuery]

variable {m : ℕ} (a c k : Fin m → ℕ) [∀ i, NeZero (a i)]
    (spectator : ∀ i, Spectators a c i ≃ Fin (Fintype.card (Spectators a c i)))
    (har : ∀ i, a i ≤ 2 ^ k i) (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * a i)

/-- Physical address permutation of a single axis-tagged, batch-tagged instruction. -/
noncomputable def opcodeSource (i : Fin m) (j : Fin 15) (tag arg : ℕ) :
    Equiv.Perm (Address a c) :=
  let e := axisLayout a c spectator i
  let route := placedPermutation (hborrow i) j (borrowedPermutation (har i) (opcodePermutation (k i) tag arg))
  (e.trans route).trans e.symm

/-- The decoded gate matrix is the permutation of the actual block addresses. -/
theorem gateMatrix_permutation (i : Fin m) (j : Fin 15) (op : Inst)
    (ht : op.1.length = 0 ∨ op.1.length = 18) :
    gateMatrix a c k spectator har hborrow (i,j,op) =
      (opcodeSource a c k spectator har hborrow i j op.1.length op.2.1.length).toPEquiv.toMatrix := by
  rw [gateMatrix, placedOpcode_matrix (har i) (hborrow i) j op ht]
  ext x y
  simp only [submatrix_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff,
    opcodeSource, Equiv.trans_apply, Equiv.symm_apply_eq]

end ShortFourier.BatchWord

namespace BoxFin

open IntegerMultiplication.Code ShortFourier ShortFourier.BatchWord ShortFourier.AxisWord
  SynchronizedBorrowing SynchronizedBlocks Matrix

variable {K L : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid K L box)
  [∀ i, NeZero (modulus box i)] (b : Fin (box.length / 4))

/-- Exact parameters and physical packed input for the block permutation query. -/
def blockPermQuery (k : Fin (count b) → ℕ) (t : Fin (count b)) (j : Fin 15) (tag arg : ℕ)
    (x : BlockAddress (BoxAxis box) b) : ValidPackedQuery :=
  let d := blockFieldRadix box b
  let n := Fintype.card (Spectators (fun i => modulus box (axis b i)) (fun i => padding box (axis b i)) t)
  packedQuery (CRT.«prefix» d t) (d t) (first n j) (size n j)
    (modulus box (axis b t)) (k t) tag arg (blockAddressRank hb b x).val

/-- The literal tape output is the packed source rank of the actual block permutation. -/
theorem blockPermQuery_correct (k : Fin (count b) → ℕ)
    (har : ∀ i, modulus box (axis b i) ≤ 2 ^ k i)
    (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * modulus box (axis b i))
    (t : Fin (count b)) (j : Fin 15) (tag arg : ℕ) (x : BlockAddress (BoxAxis box) b) :
    let a := fun i => modulus box (axis b i)
    let c := fun i => padding box (axis b i)
    packedReply (blockPermQuery hb b k t j tag arg x).val =
      tally (blockAddressRank hb b (opcodeSource a c k (blockSpectators hb b) har hborrow t j tag arg x)).val := by
  dsimp only
  rw [blockPermQuery, packedReply_query]
  apply congrArg tally
  symm
  unfold opcodeSource
  simp only [Equiv.trans_apply]
  rw [blockAxisLayout_inverse]
  obtain ⟨hrow,hcol⟩ := blockAxisLayout_fields hb b t x
  let u := axisLayout (fun i => modulus box (axis b i)) (fun i => padding box (axis b i)) (blockSpectators hb b) t x
  have h := placedOpcode_coordinates (NeZero.pos _) (har t) (hborrow t) j tag arg u
  change FieldSplit.join _ _ (cellCoordinates _).1 (cellCoordinates _).2 = _
  rw [h]
  simp only [packedTarget, cellCoordinates, u, hrow, hcol]

/-- The decoded direct permutation descriptor reads exactly the record selected
by the query generator in physical packed order. -/
theorem blockPermQuery_reads (k : Fin (count b) → ℕ)
    (har : ∀ i, modulus box (axis b i) ≤ 2 ^ k i)
    (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * modulus box (axis b i))
    (bits : BlockAddress (BoxAxis box) b ≃ Fin 2 × Fin (Fintype.card (BlockAddress (BoxAxis box) b)/2))
    (he : Even (Fintype.card (BlockAddress (BoxAxis box) b)))
    (t : Fin (count b)) (j : Fin 15) (op : Inst) (ht : op.1.length = 0 ∨ op.1.length = 18)
    (records : ℕ → ℂ) (x : BlockAddress (BoxAxis box) b) :
    let a := fun i => modulus box (axis b i)
    let c := fun i => padding box (axis b i)
    let s := decodeSlot a c k (blockSpectators hb b) har hborrow bits he (encode (t,j,op),[])
    (s.matrix bits *ᵥ fun y => records (blockAddressRank hb b y).val) x =
      records (packedReply (blockPermQuery hb b k t j op.1.length op.2.1.length x).val).length := by
  dsimp only
  have htag : op.1.length ≠ 10 := by omega
  rw [decode_direct_matrix _ _ _ _ _ _ _ _ _ htag, gateMatrix_permutation _ _ _ _ _ _ _ _ _ ht,
    PEquiv.toMatrix_toPEquiv_mulVec, blockPermQuery_correct hb b k har hborrow, tally_length]
  rfl

end BoxFin

end NearSquareRoot
end Computability
end OAI
