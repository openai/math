import OAI.Computability.BorderVNP.PackedBankPacket
import OAI.Computability.BorderVNP.PackedBankBoxWords
import OAI.Computability.BorderVNP.PackedBankShift

/-! # Serialized repeated paid-site boxes

The site contributes one strided tie per fixed incident physical bundle, one
staging equality per one-copy lane, and one box. The box ID is its actual
slot in the merged cell directory. All addresses include the cell-local
site offset and all numerical fields are emitted by public word expressions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankPacket.Paid

open BankPacket PaidBox CellSparse Word
open scoped Classical

/-- Site prefix, merged box ID, compiled paid-box operands and canonical cable bases. -/
abbrev Input (n d : ℕ) := Unit ⊕ Unit ⊕ Operand d ⊕ Fin n

variable {n : ℕ} (w : Fin n → ℕ)

private abbrev I := Input n (∑ r, w r)

private def off : WidthExpr (I w) := .field (.inl ())

private def field (k : Operand (∑ r,w r)) : WidthExpr (I w) := .field (.inr (.inr (.inl k)))

private def relative (k : Operand (∑ r,w r)) : WidthExpr (I w) := .binary .add (off w) (field w k)

private def port (base : WidthExpr (I w)) (stride : ℕ) : PortCode (I w) := ⟨base,.const stride,.const 1⟩

private def tie (r : Fin n) : RecordCode (I w) :=
  let base := .binary .add (off w) (PoolCircuit.scaleExpr (.inr (.inr (.inl none))) (start w r))
  .equal (field w none) (.const (w r)) (port w (.field (.inr (.inr (.inr r)))) (w r)) (port w base (w r))

/-- Complete fixed public record shape of one repeated paid-term bank site. -/
def rows : List (RecordCode (I w)) :=
  (List.ofFn (fun k : Fin (∑ r,w r) =>
    let r := (finSigmaFinEquiv (n := w)).symm k
    .equal (field w none) (.const 1) (port w (relative w (some (some (k,false)))) (w r.1))
      (port w (relative w (some (some (k,true)))) (∑ r,w r))) ++
    [.box (.field (.inr (.inl ()))) (relative w (some none)) (field w none) (.const (∑ r,w r))]) ++
    List.ofFn (tie w)

/-- Bind the local repeated table to its slot in the merged one-copy directory. -/
def withBoxID (id : ℕ) : Record → Record
  | .box _ base copies stride => .box id base copies stride
  | r => r

variable (x : I w → ℕ)

/-- Numeric tie between a physical canonical cable and its consecutive site-input slice. -/
def bundleTie (r : Fin n) : Record :=
  let copies := x (.inr (.inr (.inl none)))
  .equal copies (w r) ⟨x (.inr (.inr (.inr r))),w r,1⟩
    ⟨x (.inl ()) + start w r * copies,w r,1⟩

private theorem tie_read (r : Fin n) : (tie w r).read x = bundleTie w x r := by
  simp [tie,bundleTie,RecordCode.read,field,port,PortCode.read,WidthExpr.eval,Op.apply,off,PoolCircuit.scale_eval]

/-- The emitted packet materializes the relocated actual staged records and the fixed
physical bundle ties. The incoming operands may be any values; on a genuine branch
the paid-box operand compiler provides exactly the actual multiplicity-dependent header. -/
theorem read_rows :
    (rows w).map (RecordCode.read x) =
      ((decode w (fun i => x (.inr (.inr (.inl i))))).map (fun r => withBoxID (x (.inr (.inl ()))) (r.shift (x (.inl ()))))) ++
        List.ofFn (bundleTie w x) := by
  simp only [rows,PaidBox.decode,List.map_append,List.map_ofFn,Function.comp_def,List.map_cons,List.map_nil,tie_read]
  rfl

/-- Substituting the genuine count header yields the actual sparse records of the paid
site with its cell-local addresses and merged directory ID. -/
theorem physical_rows {K : Type*} [Field K] {D m : ℕ} (e : Crossing.PaidIdentity K D m)
    (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site) (copies : ℕ)
    (x : I (widths (e.net a) v) → ℕ)
    (hx : ∀ i, x (.inr (.inr (.inl i))) = header (widths (e.net a) v) copies i) :
    (rows (widths (e.net a) v)).map (RecordCode.read x) =
      ((siteDirectory e position a v copies).records.map
        (fun r => withBoxID (x (.inr (.inl ()))) (r.shift (x (.inl ()))))) ++
        List.ofFn (bundleTie (widths (e.net a) v) x) := by
  rw [read_rows, funext hx, decode_header e position a v copies]

end Packing.BankPacket.Paid

end BorderVNP
end Computability
end OAI
