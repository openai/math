import OAI.Computability.BorderVNP.CellProfileWordEmit
import OAI.Computability.QuantumFactoring.BitStackListFlatten

/-! # Printing Boolean lists and filtered one-copy tables

A table's selected row list carries the original binary row numbers. The
temporary depth in the Boolean disjunction instead counts already retained
operands. This distinction is observable in the exact descriptor bytes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}

/-- Supply a binary ordinal and fetch the named entry from its original typed list. -/
private noncomputable def withEntry (b : β) {items : α → List β}
    (hl : Procedure ea (listCode eb) items) :
    Procedure (prodCode ea Nat.bits) (prodCode ea eb)
      (fun x => (x.1, ((items x.1).drop x.2).headD b)) := by
  let env := Procedure.first ea Nat.bits
  let i := Procedure.second ea Nat.bits
  exact env.pair ((Procedure.listGet eb b).comp (i.pair (hl.comp env)))

/-- Emit a conjunction over the entries of an explicitly supplied typed list. -/
noncomputable def allList (b : β) {items : α → List β} {t : α → β → Term}
    (hl : Procedure ea (listCode eb) items)
    (ht : Boolean (prodCode ea eb) (fun z => t z.1 z.2)) :
    Boolean ea (fun x => Term.all ((items x).map (t x))) := by
  let q := allRange (t := fun x i => t x (((items x).drop i).headD b))
    ((NativeAIG.Emission.listUnaryLength eb b).comp hl) (preBool ht (withEntry b hl))
  exact q.congrFun (fun x => congrArg (fun l => CellMacro.Generator.serialized 8
    ((Term.all) l |>.emit x.2)) (map_range_getD (items x.1) b (t x.1)))

/-- Emit a disjunction over the entries of an explicitly supplied typed list. -/
noncomputable def anyList (b : β) {items : α → List β} {t : α → β → Term}
    (hl : Procedure ea (listCode eb) items)
    (ht : Boolean (prodCode ea eb) (fun z => t z.1 z.2)) :
    Boolean ea (fun x => Term.any ((items x).map (t x))) := by
  let q := anyRange (t := fun x i => t x (((items x).drop i).headD b))
    ((NativeAIG.Emission.listUnaryLength eb b).comp hl) (preBool ht (withEntry b hl))
  exact q.congrFun (fun x => congrArg (fun l => CellMacro.Generator.serialized 8
    ((Term.any) l |>.emit x.2)) (map_range_getD (items x.1) b (t x.1)))

/-- Emit a test of a little-endian word whose addresses are given by explicit
wire entries, in their actual list order. -/
noncomputable def wordIsList (b : β) {items : α → List β} {a : α → β → NatExpr} {j : α → ℕ}
    (hl : Procedure ea (listCode eb) items) (hj : Procedure ea Nat.bits j)
    (ha : Address (prodCode ea eb) (fun z => a z.1 z.2)) :
    Boolean ea (fun x => wordIs ((items x).map (a x)) (j x)) := by
  let q := wordIsRange (a := fun x i => a x (((items x).drop i).headD b))
    ((NativeAIG.Emission.listUnaryLength eb b).comp hl) hj (preAddr ha (withEntry b hl))
  exact q.congrFun (fun x => congrArg (fun l => CellMacro.Generator.serialized 8
    ((fun l => wordIs l (j x.1)) l |>.emit x.2)) (map_range_getD (items x.1) b (a x.1)))

private def selected {γ : Type} (test : γ → Bool) (rows : List γ) : List ℕ :=
  rows.zipIdx.filterMap fun r => if test r.1 then some r.2 else none

private theorem selected_eq (test : γ → Bool) (rows : List γ) :
    (rows.mapIdx (fun i v => if test v then [i] else [])).flatten = selected test rows := by
  rw [List.mapIdx_eq_zipIdx_map,selected,List.filterMap_eq_flatMap_toList,List.flatMap_def]
  congr 1
  apply List.map_congr_left
  rintro ⟨v,i⟩ _
  change (if test v then [i] else []) = (if test v then some i else none).toList
  cases test v <;> rfl

private noncomputable def selectedRows (c : γ) {rows : α → List γ} {test : α → γ → Bool}
    (hr : Procedure ea (listCode ec) rows)
    (ht : Procedure (prodCode ea ec) boolCode (fun z => test z.1 z.2)) :
    Procedure ea (listCode Nat.bits) (fun x => selected (test x) (rows x)) := by
  let context := prodCode ea (prodCode Nat.bits ec)
  let arg := Procedure.first ea (prodCode Nat.bits ec)
  let entry := Procedure.second ea (prodCode Nat.bits ec)
  let i := (Procedure.first Nat.bits ec).comp entry
  let v := (Procedure.second Nat.bits ec).comp entry
  let nil := Procedure.constant context (listCode Nat.bits) []
  let one := (Procedure.listCons Nat.bits).comp (i.pair nil)
  let item := Procedure.conditional (ht.comp (arg.pair v)) one nil
  let chunks := (Procedure.listMapIdxWith (f := fun x i v => if test x v then [i] else [])
    c [] item).comp ((Procedure.identity ea).pair hr)
  exact ((Procedure.listFlatten Nat.bits 0).comp chunks).congrFun
    (fun x => selected_eq (test x) (rows x))

/-- Print the source's complete row test, including its original row numbers,
filter predicate, binary word comparison, and left-to-right retained order. -/
noncomputable def rowTestList (defaultWire : β) (defaultRow : γ)
    {ws : α → List β} {rs : α → List γ} {addr : α → β → NatExpr} {test : α → γ → Bool}
    (hw : Procedure ea (listCode eb) ws) (hr : Procedure ea (listCode ec) rs)
    (ha : Address (prodCode ea eb) (fun z => addr z.1 z.2))
    (ht : Procedure (prodCode ea ec) boolCode (fun z => test z.1 z.2)) :
    Boolean ea (fun x => rowTest ((ws x).map (addr x)) (test x) (rs x)) := by
  let env := Procedure.first ea Nat.bits
  let j := Procedure.second ea Nat.bits
  let data := Procedure.first (prodCode ea Nat.bits) eb
  let wire := Procedure.second (prodCode ea Nat.bits) eb
  let lanes := preAddr ha ((env.comp data).pair wire)
  let testRow := wordIsList (a := fun (x : α × ℕ) b => addr x.1 b) defaultWire (hw.comp env) j lanes
  let code := anyList (t := fun (x : α) j => wordIs ((ws x).map (addr x)) j)
    0 (selectedRows defaultRow hr ht) testRow
  refine code.congrFun ?_
  intro x
  apply congrArg (fun ts => CellMacro.Generator.serialized 8 ((Term.any ts).emit x.2))
  rw [selected, List.map_filterMap]
  apply congrArg (fun f => (rs x.1).zipIdx.filterMap f)
  funext r
  cases test x.1 r.1 <;> rfl

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
