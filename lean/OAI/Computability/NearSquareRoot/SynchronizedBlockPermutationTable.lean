import OAI.Computability.NearSquareRoot.SynchronizedBlockPermutationQuery
import OAI.Computability.NearSquareRoot.SynchronizedNumberedBits
import OAI.Computability.NearSquareRoot.CRTTableWordEquiv
import OAI.Computability.NearSquareRoot.SynchronizedPhysicalRouting

/-! # Complete permutation tables for direct block opcodes

The table builder enumerates every packed address of one small block. It
returns the graph in the most-significant-bit-first format consumed by the
Beneš compiler. The extent and the number of addresses are supplied in unary.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication Code Strip Staff Carry AxisWord

/-- Interpret the supplied unary radius as the width of the radix computation.
For a power of two its ceiling logarithm recovers the opcode width. -/
def extentReply (z : PackedQuery) : Tally :=
  let q := z.2
  let r := q.2.1.2.2.length
  tally (packedTarget z.1.length q.2.2.1.length q.2.1.1.1.length q.2.1.1.2.length
    q.2.1.2.1.length r (permutationTarget (Nat.clog 2 r) q.1.2.1.length q.1.2.2.length) q.2.2.2.length)

private theorem rounded_radius (r : ℕ) : 2 ^ Nat.clog 2 r ≤ 2 * (r + 1) := by
  by_cases h : 1 < r
  · have hp := Nat.pow_pred_clog_lt_self (b := 2) (by decide) h
    have hn := Nat.clog_pos (b := 2) (by decide) h
    calc
      _ = 2 ^ (Nat.clog 2 r).pred * 2 := by
        rw [← pow_succ]
        exact congrArg (fun t : ℕ => 2^t) (Nat.succ_pred_eq_of_pos hn).symm
      _ ≤ _ := by omega
  · interval_cases r <;> decide

private def input : Regime PackedQuery := ⟨Code.size,send,Dom.base _⟩

private theorem field (f : PackedQuery → Tally) (hf : Easy f) :
    Realizes input (fun z => (f z).length) := by
  have h : input.Has id := input.self
  simpa only [Realizes, Function.comp_def, recover_tally, id_eq] using h.ez hf

/-- Total polynomial stack program for one lookup, over arbitrary raw headers. -/
theorem extentReply_poly : Poly extentReply := by
  let r (z : PackedQuery) := z.2.2.1.2.2.length
  have R : Realizes input r := field _ (show Easy (fun z : PackedQuery => z.2.2.1.2.2) by fun_prop)
  have K := (Figure.of_spoken R).short_log
  have bound : Realizes input (fun z => 2 * (r z + 1)) := (Realizes.fix 2).times (R.plus (.fix 1))
  have pow : Realizes input (fun z => 2 ^ Nat.clog 2 (r z)) :=
    ((Figure.natural 2).repeated K).pay ((diameter _ bound).mono (fun z => rounded_radius (r z)))
  exact packedTarget_realizes (s := input)
    (field (fun z => z.1) (by fun_prop)) (field (fun z => z.2.2.2.1) (by fun_prop))
    (field (fun z => z.2.2.1.1.1) (by fun_prop)) (field (fun z => z.2.2.1.1.2) (by fun_prop))
    (field (fun z => z.2.2.1.2.1) (by fun_prop)) R (field (fun z => z.2.2.2.2) (by fun_prop))
    (fun _ => permutationTarget_realizes K pow (field (fun z => z.2.1.2.1) (by fun_prop))
      (field (fun z => z.2.1.2.2) (by fun_prop)))

theorem extentReply_valid (q : ValidPackedQuery) : extentReply q.val = packedReply q.val := by
  simp only [extentReply, packedReply, q.property, Nat.clog_pow 2 _ (by decide)]

def setIndex (z : PackedQuery) (i : Tally) : PackedQuery :=
  (z.1, z.2.1, z.2.2.1, z.2.2.2.1, i)

/-- Header, unary volume, and bit width of the block. -/
abbrev TableQuery := PackedQuery × Tally × Tally

/-- Full source table in packed address order, with one unary rank per cell. -/
def sourceTable (q : TableQuery) : List Tally :=
  (Iter.lineup q.2.1).map fun i => extentReply (setIndex q.1 i)

theorem sourceTable_poly : Poly sourceTable := by
  have update : Easy (fun z : PackedQuery × Tally => setIndex z.1 z.2) := by
    unfold setIndex
    fun_prop
  have h := ((Easy.fst (X := PackedQuery) (Y := Tally × Tally)).poly.pair
    ((Easy.snd.compose Easy.fst).poly.compose Iter.poly_line)).compose
      (Poly.push default [] (update.poly.compose extentReply_poly))
  exact h

/-- Spelling of the full table as paired binary input and output port labels. -/
def portTable (q : TableQuery) : Benes.RawTable := CRTTable.wordRows (q.2.2, sourceTable q)

theorem portTable_poly : Poly portTable :=
  ((Easy.snd.poly.sndCompose).pair sourceTable_poly).compose CRTTable.wordRows_poly

/-- A single fixed multitape program writes the entire table. -/
theorem portTable_machine : PolyTreeMachine Code.size send (fun q => send (portTable q)) :=
  polyTreeMachine_of_BT (portTable_poly.on (Dom.base _)) (Dom.base _)

@[simp] theorem sourceTable_length (q : TableQuery) : (sourceTable q).length = q.2.1.length := by
  simp [sourceTable]

theorem sourceTable_get (q : TableQuery) (i : ℕ) (hi : i < q.2.1.length) :
    (sourceTable q)[i]'(by simpa using hi) = extentReply (setIndex q.1 (tally i)) := by
  simp [sourceTable, Iter.lineup]

/-- The full identity table for an idle block, with charged volume and width. -/
def idlePortTable (q : Tally × Tally) : Benes.RawTable := CRTTable.wordRows (q.2, Iter.lineup q.1)

theorem idlePortTable_poly : Poly idlePortTable :=
  (Easy.snd.poly.pair (Easy.fst.poly.compose Iter.poly_line)).compose CRTTable.wordRows_poly

theorem idlePortTable_represents (w : ℕ) :
    Benes.RawRepresents (Equiv.refl (Fin w → Bool)) (idlePortTable (tally (2^w), tally w)) := by
  have H := CRTTable.wordRows_represents w (Iter.lineup (tally (2^w))) (Equiv.refl _)
    (by simp) (by intro i; simp [Iter.lineup])
  simpa [idlePortTable] using H

/-- These are source queries and destination queries at once: reversal and
the exchange with a stage bit are involutions, as are their placed copies. -/
theorem opcodeSource_inv {m : ℕ} (a c k : Fin m → ℕ) [∀ i, NeZero (a i)]
    (spectator : ∀ i, Spectators a c i ≃ Fin (Fintype.card (Spectators a c i)))
    (har : ∀ i, a i ≤ 2 ^ k i) (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * a i)
    (i : Fin m) (j : Fin 15) (tag arg : ℕ) :
    (opcodeSource a c k spectator har hborrow i j tag arg).symm =
      opcodeSource a c k spectator har hborrow i j tag arg := by
  have U : (opcodePermutation (k i) tag arg).symm = opcodePermutation (k i) tag arg := by
    unfold opcodePermutation
    split_ifs <;> simp
  let u := borrowedPermutation (har i) (opcodePermutation (k i) tag arg)
  have V : u.symm = u := by
    apply Equiv.ext
    intro t
    change auxiliaryLayout (har i) ((opcodePermutation (k i) tag arg).symm ((auxiliaryLayout (har i)).symm t)) = _
    rw [U]
    rfl
  have W : (placedPermutation (b := fiberCount a c i) (c := c i) (hborrow i) j u).symm =
      placedPermutation (hborrow i) j u := by
    rw [placedPermutation, Equiv.Perm.viaFintypeEmbedding, Equiv.Perm.extendDomain_symm, Equiv.prodCongr_symm, V]
    rfl
  let e := axisLayout a c spectator i
  change ((e.trans (placedPermutation _ j u)).trans e.symm).symm = _
  apply Equiv.ext
  intro t
  change e.symm ((placedPermutation (hborrow i) j u).symm (e t)) = e.symm ((placedPermutation _ j u) (e t))
  rw [W]

/-- The literal direct opcode decodes to the permutation used by the complete
port table. This also identifies the slot constructor for dispatcher proofs. -/
theorem decode_opcodeSource {m : ℕ} (a c k : Fin m → ℕ) [∀ i, NeZero (a i)]
    (spectator : ∀ i, Spectators a c i ≃ Fin (Fintype.card (Spectators a c i)))
    (har : ∀ i, a i ≤ 2 ^ k i) (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * a i)
    (bits : Address a c ≃ Fin 2 × Fin (Fintype.card (Address a c)/2)) (he : Even (Fintype.card (Address a c)))
    (i : Fin m) (j : Fin 15) (op : Inst) (ht : op.1.length = 0 ∨ op.1.length = 18) :
    decodeSlot a c k spectator har hborrow bits he (encode (i,j,op),[]) =
      .permutation (opcodeSource a c k spectator har hborrow i j op.1.length op.2.1.length) := by
  let p := opcodePermutation (k i) op.1.length op.2.1.length
  have P := decode_direct_permutation a c k spectator har hborrow bits he (i,j,op) p
    (fixedSlot_permutation (a i) (k i) op ht)
  have M := decode_direct_matrix a c k spectator har hborrow bits he (i,j,op)
    (by change op.1.length ≠ 10; omega)
  rw [P,gateMatrix_permutation a c k spectator har hborrow i j op ht] at M
  rw [P]
  apply congrArg Slot.permutation
  apply Equiv.ext
  intro t
  exact Option.some.inj (congrArg (fun z : PEquiv _ _ => z t) (PEquiv.toMatrix_injective (α := ℂ) M))

end ShortFourier.BatchWord

namespace BoxFin

open IntegerMultiplication.Code ShortFourier ShortFourier.BatchWord ShortFourier.AxisWord SynchronizedBlocks
open SynchronizedBorrowing

variable {K L : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid K L box)
    [∀ i, NeZero (modulus box i)] (b : Fin (box.length / 4))

/-- Scalar header, enumeration length and Beneš port width for one direct block permutation. -/
def directTableQuery (k : Fin (count b) → ℕ) (t : Fin (count b)) (j : Fin 15) (tag arg : ℕ) : TableQuery :=
  let n := fiberCount (blockModulus b) (blockPadding b) t
  let d := blockFieldRadix box b
  ((packedQuery (CRT.«prefix» d t) (d t) (first n j) (size n j) (blockModulus b t) (k t) tag arg 0).val,
    tally (2 ^ physicalWidth (box := box) b), tally (physicalWidth (box := box) b))

/-- The generated full unary table contains the physical source of every port. -/
theorem directTable_entry (k : Fin (count b) → ℕ) (har : ∀ i, blockModulus b i ≤ 2 ^ k i)
    (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * blockModulus b i)
    (t : Fin (count b)) (j : Fin 15) (tag arg : ℕ) (x : BlockAddress (BoxAxis box) b) :
    let q := directTableQuery (box := box) b k t j tag arg
    let e := blockBitRank hb b
    (sourceTable q)[(e x).val]? =
      some (tally (e (opcodeSource (blockModulus b) (blockPadding b) k (blockSpectators hb b)
        har hborrow t j tag arg x)).val) := by
  let q := directTableQuery (box := box) b k t j tag arg
  let e := blockBitRank hb b
  have hlen : q.2.1.length = 2 ^ physicalWidth (box := box) b := by simp [q, directTableQuery]
  have hi := (e x).isLt
  have h : (e x).val < q.2.1.length := by simpa only [hlen] using hi
  dsimp only
  rw [List.getElem?_eq_getElem (by rw [sourceTable_length]; exact h), sourceTable_get q _ h]
  change some (extentReply (blockPermQuery hb b k t j tag arg x).val) = _
  rw [extentReply_valid, blockPermQuery_correct hb b k har hborrow]
  rfl

/-- The full source table generated from scalar fields is a duplicate-free
Beneš graph of the block permutation in physical binary address order. -/
theorem directTable_represents (k : Fin (count b) → ℕ) (har : ∀ i, blockModulus b i ≤ 2 ^ k i)
    (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * blockModulus b i)
    (t : Fin (count b)) (j : Fin 15) (tag arg : ℕ) :
    let e := (blockBitRank hb b).trans (CRTTable.wordEquiv (physicalWidth b))
    let p := opcodeSource (blockModulus b) (blockPadding b) k (blockSpectators hb b) har hborrow t j tag arg
    Benes.RawRepresents (e.symm.trans (p.trans e))
      (portTable (directTableQuery (box := box) b k t j tag arg)) := by
  let e := blockBitRank hb b
  let w := physicalWidth (box := box) b
  let p := opcodeSource (blockModulus b) (blockPadding b) k (blockSpectators hb b) har hborrow t j tag arg
  let q := directTableQuery (box := box) b k t j tag arg
  have hlen : (sourceTable q).length = 2^w := by simp [q, w, directTableQuery]
  let π := e.symm.trans (p.trans e)
  have h := CRTTable.wordRows_represents w (sourceTable q) π hlen (by
    intro i
    have hentry := directTable_entry hb b k har hborrow t j tag arg (e.symm i)
    change (sourceTable q)[(e (e.symm i)).val]? = some (tally (π i).val) at hentry
    rw [e.apply_symm_apply, List.getElem?_eq_getElem (by rw [hlen]; exact i.isLt)] at hentry
    simpa using congrArg List.length (Option.some.inj hentry))
  exact h

end BoxFin

end NearSquareRoot
end Computability
end OAI
