import OAI.Computability.BorderVNP.CellSparseExteriorDriver
import OAI.Computability.BorderVNP.DiagonalNativePackedProduct
import OAI.Computability.BorderVNP.CoverAddressCoding

/-! # Uniqueness of the logical signed input on an occupied physical call row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open VPVNP.BurstRAM CellSparse CellMacro CellDispatch CompactMachine Evaluator
open private record_unique from OAI.Computability.BorderVNP.CoverAddressCoding
open private value value_bits from OAI.Computability.BorderVNP.CellPacketBinaryCount

private theorem natBits_inj {x y : ℕ} (h : x.bits=y.bits) : x=y :=
  (value_bits x).1.symm.trans ((congrArg (fun ds : List Bool => value 0 ds.reverse) h).trans (value_bits y).1)

private theorem words_inj {xs ys : List ℕ}
    (same : Generator.records (xs.map Nat.bits) = Generator.records (ys.map Nat.bits)) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [Generator.records]
  | cons x xs ih =>
    cases ys with
    | nil => simp [Generator.records] at same
    | cons y ys =>
      simp only [List.map_cons,Generator.records,List.cons.injEq,true_and] at same
      obtain ⟨front,tail⟩ := record_unique _ _ _ _ same
      exact congrArg₂ List.cons (natBits_inj front) (ih tail)

/-- Two encodings read by the private sparse expander can differ in their
physical source addresses. Equal transmitted bytes recover the same
dense logical wires and the same trailing report. -/
theorem expand_of_encode {width width' p p' : ℕ} {tail tail' : List Bool} (xs ys : List Span)
    (same : encode width tail p xs = encode width' tail' p' ys) :
    expand width tail p xs = expand width' tail' p' ys := by
  induction xs generalizing width width' p p' tail tail' ys with
  | nil =>
    cases ys with
    | cons y ys => simp [encode] at same
    | nil =>
      obtain ⟨size,last⟩ := record_unique _ _ _ _ (List.cons.inj same).2
      exact congrArg₂ List.append (congrArg (fun k => List.replicate k false) (natBits_inj size)) last
  | cons x xs ih =>
    cases ys with
    | nil => simp [encode] at same
    | cons y ys =>
      simp only [encode,List.append_assoc,List.cons.injEq,true_and] at same
      obtain ⟨size,more⟩ := record_unique _ _ _ _ same
      obtain ⟨values,endOfRun⟩ := record_unique _ _ _ _ more
      simp only [expand,natBits_inj size,values,ih ys endOfRun]

private theorem unique_frame (xs ys a b : List Bool)
    (h : FieldDecoder.frame xs++a=FieldDecoder.frame ys++b) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [FieldDecoder.frame]
  | cons x xs ih =>
    cases ys with
    | nil => simp [FieldDecoder.frame] at h
    | cons y ys =>
      simp only [FieldDecoder.frame,List.cons_append,List.cons.injEq,true_and] at h
      exact congrArg₂ List.cons h.1 (ih ys h.2)

private theorem unpack_eq {w : ℕ} (hw : 0<w) {xs ys : List Bool} (h : CompactFrame.pack w xs = CompactFrame.pack w ys) :
    xs=ys := by
  have bits := congrArg TeamPrivateCall.inputBits h
  rw [CompactFrame.inputBits_pack hw,CompactFrame.inputBits_pack hw] at bits
  exact unique_frame xs ys _ _ bits

/-- The self-delimiting packet recovers the true private-wire count, every
original directory operand, and every decoded external bit. -/
theorem logical_input_unique {D D' : Directory} {p p' : ℕ} {u v : Field}
    (same : Packet.input D p u.bytes = Packet.input D' p' v.bytes) :
    (⟨D,p,u.values⟩ : CellInput) = ⟨D',p',v.values⟩ := by
  obtain ⟨front,ext⟩ := record_unique _ _ _ _ same
  have words := words_inj front
  have decoded := congrArg Packet.parse words
  rw [Packet.parse_words,Packet.parse_words] at decoded
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj decoded)
  exact congrArg (fun data => CellInput.mk D p data) (expand_of_encode u.spans v.spans ext)

/-- Choosing a different completing joint tuple for the same local native
prefix leaves the input of each owned cell uniquely determined by the
burst actually fetched from its row. This includes rejected private assignments. -/
theorem owned_input_unique {w n : ℕ} {pub : Arg → Word w} {m : Memory w}
    (A B : Evaluator.GeneratedCells driver n pub m) (i : ℕ)
    (fit : i<(Frame.ofMemory pub m).count) (mine : readings m ((Frame.ofMemory pub m).address i)=(Frame.ofMemory pub m).team)
    {D D' : Directory} {p p' : ℕ} {u v : Field}
    (left : A.payload i = Packet.input D p u.bytes) (right : B.payload i = Packet.input D' p' v.bytes)
    (first : A.cell i = ⟨D,p,u.values⟩) (next : B.cell i = ⟨D',p',v.values⟩) : A.cell i=B.cell i := by
  have h := (A.packed.words i fit mine).symm.trans (B.packed.words i fit mine)
  rw [left,right] at h
  exact first.trans ((logical_input_unique (unpack_eq A.packed.width h)).trans next.symm)

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
