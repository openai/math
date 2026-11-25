import OAI.Computability.BorderVNP.CellFactorEmitFields
import OAI.Computability.BorderVNP.CellGadgetSteps
import OAI.Computability.BorderVNP.CellPrefixEmit
import OAI.Computability.BorderVNP.CellProfileWeaken
import OAI.Computability.BorderVNP.CellTableTermEmit

/-! # Native printing of private one-copy factor instructions

The typed constructor selects a concrete Boolean table, sign table, identifier table or unary
equality. Each emitted row is selected by its original index. The gadget count generator
retains its caller-supplied symbolic row and shifts the selector under the candidate loop.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

variable {α γ : Type} {ea : α → List Bool} {ec : γ → List Bool}

private noncomputable def ifBool {test : α → Bool} {yes no : α → Term}
    (ht : Procedure ea Procedure.boolCode test) (hy : Boolean ea yes) (hn : Boolean ea no) :
    Boolean ea (fun x => if test x then yes x else no x) := by
  let c := ht.comp (Procedure.first ea Nat.bits)
  exact (Procedure.conditional c hy hn).congrFun (fun x => by
    cases h : test x.1 <;> simp [h])

private noncomputable def rowsBool (d : γ) {off : α → NatExpr} {ws : α → List ℕ}
    {rs : α → List γ} {test : α → γ → Bool}
    (ho : Address ea off) (hw : Procedure ea Typed.naturals ws) (hr : Procedure ea (listCode ec) rs)
    (ht : Procedure (prodCode ea ec) Procedure.boolCode (fun z => test z.1 z.2)) :
    Boolean ea (fun x => rowTest (tableWires (off x) (ws x)) (test x) (rs x)) := by
  let a := addAddr (preAddr ho (Procedure.first ea Nat.bits)) (litAddr (Procedure.second ea Nat.bits))
  exact rowTestList 0 d hw hr a ht

private noncomputable def unaryPass {aux : α → ℕ} {f : α → Factor} {off copy : α → NatExpr}
    (ha : Procedure ea Nat.bits aux) (hf : Procedure ea Typed.factor f) (ho : Address ea off) (hc : Address ea copy) :
    Boolean ea (fun x =>
      (Term.wire (.add (off x) (.lit (FactorData.unaryFields (f x)).1))).equal
        (.wire (((FactorData.unaryFields (f x)).2.shift (aux x)).expr (copy x) (.lit 0)))) := by
  let u := FactorData.unaryP hf
  let n := (Procedure.first ..).comp u
  let p := FactorData.shiftPort ha ((Procedure.second ..).comp u)
  exact equalBool (wireBool (addAddr ho (litAddr n))) (wireBool (portAddr p hc (constAddr ea (.lit 0))))

/-- Print the presence/Boolean test of an actual table or shifted unary port. -/
noncomputable def factorPassBool {aux : α → ℕ} {f : α → Factor} {off copy : α → NatExpr}
    (ha : Procedure ea Nat.bits aux) (hf : Procedure ea Typed.factor f)
    (ho : Address ea off) (hc : Address ea copy) :
    Boolean ea (fun x => factorPass (off x) (copy x) ((f x).shift (aux x))) := by
  let ws := FactorData.wiresP hf
  let bs := FactorData.boolRowsP hf
  let ids := FactorData.idsP hf
  let truth := rowsBool (test := fun _ => (id : Bool → Bool)) false ho ws bs (Procedure.second ..)
  let signed := rowsBool (test := fun _ _ => true) false ho ws bs (Procedure.constant _ _ true)
  let gadget := rowsBool (test := fun _ _ => true) 0 ho ws ids (Procedure.constant _ _ true)
  let p := ifBool (FactorData.tagP true false false false hf) truth
    (ifBool (FactorData.tagP false true false false hf) signed
      (ifBool (FactorData.tagP false false true false hf) gadget (unaryPass ha hf ho hc)))
  exact p.congrFun (fun x => by cases h : f x.1 <;>
    simp only [h,FactorData.tag,FactorData.wires,FactorData.boolRows,FactorData.ids,FactorData.unaryFields,
      Factor.shift,factorPass,ite_true,ite_false,Bool.false_eq_true])

/-- Print the sign-toggle expression of the actual selected factor constructor. -/
noncomputable def factorSignBool {aux : α → ℕ} {f : α → Factor} {off : α → NatExpr}
    (hf : Procedure ea Typed.factor f) (ho : Address ea off) :
    Boolean ea (fun x => factorSign (off x) ((f x).shift (aux x))) := by
  let t := rowsBool (test := fun _ => (id : Bool → Bool)) false ho (FactorData.wiresP hf) (FactorData.boolRowsP hf)
    (Procedure.second ..)
  let p := ifBool (FactorData.tagP false true false false hf) t (constBool ea (.lit false))
  exact p.congrFun (fun x => by cases h : f x.1 <;> simp [h,FactorData.tag,FactorData.wires,
    FactorData.boolRows,Factor.shift,factorSign])

/-- Print the full signed table-factor instruction in its relocated private assignment bank. -/
noncomputable def factorBodyStmt {aux : α → ℕ} {f : α → Factor} {idx off copy : α → NatExpr}
    (ha : Procedure ea Nat.bits aux) (hf : Procedure ea Typed.factor f)
    (ho : Address ea off) (hc : Address ea copy) :
    Statement ea (fun x => factorBody (aux x) (f x) (idx x) (off x) (copy x)) := by
  let physical := addAddr (litAddr ha) ho
  exact seqStmt (guardBool (factorPassBool ha hf physical hc)) (signBool (factorSignBool (aux := aux) hf physical))

/-- Physically emit the range guard including comparison of each selected ID against the report length. -/
noncomputable def rangeBodyStmt {limit : α → ℕ} {f : α → Factor} {off : α → NatExpr}
    (hl : Procedure ea Nat.bits limit) (hf : Procedure ea Typed.factor f) (ho : Address ea off) :
    Statement ea (fun x => (rangeTerm (limit x) (off x) (f x)).guard) := by
  let test := Procedure.binaryLe.comp ((hl.comp (Procedure.first ea Nat.bits)).pair (Procedure.second ea Nat.bits))
  let t := rowsBool (test := fun x v => decide (limit x ≤ v)) 0 ho (FactorData.wiresP hf) (FactorData.idsP hf) test
  let p := ifBool (FactorData.tagP false false true false hf) (notBool t) (constBool ea (.lit true))
  apply guardBool
  exact p.congrFun (fun x => by cases h : f x.1 <;> simp [h,FactorData.tag,FactorData.wires,FactorData.ids,rangeTerm])

/-- Print the gadget selection bit using the original row IDs and an independently computed query ID. -/
noncomputable def factorSelectBool {id aux : α → ℕ} {f : α → Factor} {off : α → NatExpr}
    (hi : Procedure ea Nat.bits id) (hf : Procedure ea Typed.factor f) (ho : Address ea off) :
    Boolean ea (fun x => factorSelect (off x) (id x) ((f x).shift (aux x))) := by
  let test := Procedure.binaryEq.comp ((Procedure.second ea Nat.bits).pair (hi.comp (Procedure.first ea Nat.bits)))
  let t := rowsBool (test := fun x v => decide (v = id x)) 0 ho (FactorData.wiresP hf) (FactorData.idsP hf) test
  let p := ifBool (FactorData.tagP false false true false hf) t (constBool ea (.lit false))
  exact p.congrFun (fun x => by cases h : f x.1 <;> simp [h,FactorData.tag,FactorData.wires,FactorData.ids,Factor.shift,factorSelect])

private theorem weaken_rows {β : Type} (off : NatExpr) (ws : List ℕ) (test : β → Bool) (rs : List β) :
    (rowTest (tableWires off ws) test rs).weaken = rowTest (tableWires off.weaken ws) test rs := by
  unfold rowTest
  generalize rs.zipIdx = zs
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    have hw : (tableWires off ws).map NatExpr.weaken = tableWires off.weaken ws := by
      simp [tableWires,List.map_map,Function.comp_def,NatExpr.weaken]
    simp only [Term.any] at ih ⊢
    cases ht : test z.1 <;> simp [ht,Term.weaken,ih,weaken_wordIs,hw]

private theorem weaken_select (off : NatExpr) (id : ℕ) (f : Factor) :
    (factorSelect off id f).weaken = factorSelect off.weaken id f := by
  cases f with
  | gadget w r => exact weaken_rows off w (fun x => decide (x = id)) r
  | _ => rfl

/-- Emit the actual prefix transition for a repeated table occurrence. The row index and the
physical offset are supplied under the fresh candidate counter. -/
noncomputable def gadgetStepStmt {cap aux id : α → ℕ} {f : α → Factor} {idx off copy : α → NatExpr}
    (hc : Procedure ea Nat.bits cap) (ha : Procedure ea Nat.bits aux) (hi : Procedure ea Nat.bits id)
    (hf : Procedure ea Typed.factor f) (hj : Address ea (fun x => (idx x).weaken))
    (ho : Address ea (fun x => (off x).weaken)) :
    Statement ea (fun x => Gadget.stepBody (cap x) (aux x) (id x) (f x) (idx x) (off x) (copy x)) := by
  let a := addAddr (litAddr ha) ho
  let sel := factorSelectBool (aux := aux) hi hf a
  apply prefixStep (Procedure.constant _ _ 0) hc hj
  exact sel.congrFun (fun x => by dsimp only; rw [weaken_select]; rfl)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
