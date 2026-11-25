import OAI.Computability.BorderVNP.CellPacketGeometryCounts
import OAI.Computability.BorderVNP.CellPacketGeometrySiteWords
import OAI.Computability.BorderVNP.PackedBankBoxOrdinal
import OAI.Computability.BorderVNP.PackedBankPacket

/-! # Fixed source pins for all actual public site-word records

One slot per row-code word is selected from the shared record emitter. Its local
count prefix is omitted. Cell headers use the genuine dynamic box and row counts,
and the report vectors retain their fixed list lengths and actual numeric addresses.
Private box bodies contribute no source word and no geometry gate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open CellSparse Packet Packing.BankPacket Packing.Word

variable {E I Orig : Type} {s C : ℕ}
variable {α β γ δ η : Type*}

/-- The static types of the cell's public operand fields. -/
structure Template (E I Orig : Type) (s C : ℕ) where
  /-- Box tags and fixed one-copy crossing metadata, in per-site order. -/
  boxes : Fin s → List (Source.Box Orig)
  /-- Each typed per-site record has a fixed number of scalar arithmetic operands. -/
  format : Fin s → List (RecordCode I)
  /-- Source operand containing this cell's number of private assignment bits. -/
  privateWires : Fin C → E
  /-- Fixed list shapes of the reported gadget subtotals and their address operands. -/
  reports : Fin C → List (List E)

/-- Output word of the shared sparse site-record emitter. -/
abbrev Template.RowPin (T : Template E I Orig s C) := Σ i : Fin s, Fin (tape (T.format i)).length

/-- Numeric fields in the public word table after adjoining the shared row outputs. -/
abbrev Template.Fields (T : Template E I Orig s C) := E ⊕ T.RowPin

/-- The typed sparse directory on the branch determined by the input operand values. -/
def Template.directory (T : Template E I Orig s C) (owner : Fin s → Fin C)
    (args : E → ℕ) (fields : Fin s → I → ℕ) : SiteWords.Directory (Fin s) Orig C where
  sites := List.finRange s
  owner := owner
  boxes := T.boxes
  rows i := (T.format i).map (RecordCode.read (fields i))
  privateWires c := args (T.privateWires c)
  reports c := (T.reports c).map (List.map args)

/-- Interpretation of both kinds of upstream word pin. -/
def Template.arguments (T : Template E I Orig s C) (args : E → ℕ) (fields : Fin s → I → ℕ) :
    T.Fields → ℕ :=
  Sum.elim args fun z => ((tape (T.format z.1))[z.2.val]).eval (fields z.1)

private def reportAtoms (T : Template E I Orig s C) (c : Fin C) : List (Atom T.Fields C) :=
  .literal (T.reports c).length :: (T.reports c).flatMap (fun v =>
    .literal v.length :: v.map (fun e => .field (.inl e)))

private def rowAtoms (T : Template E I Orig s C) (i : Fin s) : List (Atom T.Fields C) :=
  ((List.finRange (tape (T.format i)).length).drop 1).map (fun j => .field (.inr ⟨i,j⟩))

private def group (xs : List α) (owner : α → β) (values : α → List γ) : List (β × γ) :=
  xs.flatMap fun i => (values i).map (Prod.mk (owner i))

/-- Fixed array of geometry pins before adding the cell markers. Input-dependent
labels and operands change values but never change the array length or order. -/
def Template.atoms (T : Template E I Orig s C) : List (Owner s C × Atom T.Fields C) :=
  group (List.finRange C) Sum.inr (fun c => [.field (.inl (T.privateWires c)),.boxes c]) ++
  group (List.finRange s) Sum.inl (fun i => (SiteWords.boxWords (T.boxes i)).map Atom.literal) ++
  group (List.finRange C) Sum.inr (fun c => [.rows c]) ++
  group (List.finRange s) Sum.inl (rowAtoms T) ++ group (List.finRange C) Sum.inr (reportAtoms T)

private theorem group_values (xs : List α) (owner : α → β) (values : α → List γ)
    (f : β → δ) (g : γ → η) : (group xs owner values).map (Prod.map f g) =
      group xs (f ∘ owner) (fun i => (values i).map g) := by
  simp [group,List.map_flatMap,List.map_map,Function.comp_def]

/-- The batched site histogram is the length of the actual stable cell list. -/
theorem merged_length {A : Type*} (owner : Fin s → Fin C) (boxes : Fin s → List A) (c : Fin C) :
    total owner (fun i => (boxes i).length) c = ((SiteWords.owned c owner (List.finRange s)).flatMap boxes).length := by
  have h := Packing.BankBoxOrdinal.table_length (fun i => (owner i).val) boxes c.val
  rw [Packing.BankBoxOrdinal.table_eq_filtered] at h
  simpa only [total,SiteWords.owned,Fin.val_inj] using h.symm

/-- Evaluating every fixed public source word gives the exact typed global sparse
stream, including the dynamic merged list counts. -/
theorem Template.atoms_eval (T : Template E I Orig s C) (owner : Fin s → Fin C)
    (args : E → ℕ) (fields : Fin s → I → ℕ) :
    let eval := Atom.eval owner (fun i => (T.boxes i).length) (fun i => (T.format i).length)
      (T.arguments args fields)
    T.atoms.map (Prod.map (Sum.elim owner id) eval) = (T.directory owner args fields).words := by
  intro eval
  let D := T.directory owner args fields
  have hboxes (c) : total owner (fun i => (T.boxes i).length) c = (D.cellBoxes c).length :=
    merged_length owner T.boxes c
  have hrows (c) : total owner (fun i => (T.format i).length) c = (D.cellRecords c).length := by
    simpa [D,Template.directory,SiteWords.Directory.cellRecords] using
      merged_length owner (fun i => (T.format i).map (RecordCode.read (fields i))) c
  have hr (i : Fin s) : (rowAtoms T i).map eval = (D.rows i).flatMap Packet.record := by
    let xs := tape (T.format i)
    have idx : (List.finRange xs.length).map (fun j => xs[j.val].eval (fields i)) = xs.map (WidthExpr.eval (fields i)) := by
      simpa only [List.map_map,List.get_eq_getElem,Function.comp_def] using
        congrArg (List.map (WidthExpr.eval (fields i))) (List.map_get_finRange xs)
    have tail := congrArg (List.drop 1) ((idx.trans (tape_eval (fields i) (T.format i))))
    simpa only [rowAtoms,List.map_map,List.map_drop,Function.comp_def,eval,Atom.eval,arguments,Sum.elim_inr,
      Packet.fieldList,List.drop_succ_cons,List.drop_zero,D,Template.directory,xs] using tail
  have ht (c : Fin C) : (reportAtoms T c).map eval = Packet.fieldList Packet.vector (D.reports c) := by
    simp [reportAtoms,eval,Atom.eval,arguments,D,Template.directory,Packet.fieldList,Packet.vector,
      List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
  have head (c : Fin C) : ([.field (.inl (T.privateWires c)),.boxes c] : List (Atom T.Fields C)).map eval =
      [D.privateWires c,(D.cellBoxes c).length] := by simp [eval,Atom.eval,arguments,D,directory,hboxes c]
  have count (c : Fin C) : ([.rows c] : List (Atom T.Fields C)).map eval = [(D.cellRecords c).length] := by
    simp only [List.map_cons,List.map_nil,eval,Atom.eval,hrows]
  have box (i : Fin s) : ((SiteWords.boxWords (T.boxes i)).map Atom.literal).map eval =
      SiteWords.boxWords (T.boxes i) := by simp [eval,List.map_map,Function.comp_def,Atom.eval]
  change _ = D.words
  simp only [atoms,List.map_append,group_values,head,box,count,hr,ht]
  rfl

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
