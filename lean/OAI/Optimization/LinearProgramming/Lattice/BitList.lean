import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! Bounded indexed list updates on the finite Boolean-stack machine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

variable {α β γ : Type}

/-- Read a framed list by a binary index; the out-of-bounds value is explicit. -/
noncomputable def nthDP (e : α → List Bool) (d : α) :
    Procedure (prodCode Nat.bits (listCode e)) e (fun z => z.2[z.1]?.getD d) :=
  (listGet e d).congrFun (by rintro ⟨i,xs⟩; simp)

/-- Tabulate with the genuine length of a framed input list as clock. In particular, a
large binary selector never determines the iteration count. -/
noncomputable def tabulateAlongP {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    (da : α) (db : β) {items : γ → List α} {f : γ → ℕ → β}
    (xs : Procedure ec (listCode ea) items)
    (entry : Procedure (prodCode unaryCode ec) eb (fun z => f z.2 z.1)) :
    Procedure ec (listCode eb) (fun c => (List.range (items c).length).map (f c)) := by
  let count := (PriceGame.Control.Native.rowSizeP ea da).comp xs
  exact ((tabulate db entry).comp (count.pair (identity ec))).congrFun (by intro c; rfl)

/-- Replace one element selected by a binary integer; an out-of-range selector leaves
the original list untouched, as in `List.set`. -/
noncomputable def setNthP (e : α → List Bool) (d : α) :
    Procedure (prodCode (prodCode Nat.bits e) (listCode e)) (listCode e)
      (fun z => z.2.set z.1.1 z.1.2) := by
  let env := prodCode (prodCode Nat.bits e) (listCode e)
  let input := second unaryCode env
  let selected := (first (prodCode Nat.bits e) (listCode e)).comp input
  let idx := (first Nat.bits e).comp selected
  let value := (second Nat.bits e).comp selected
  let xs := second (prodCode Nat.bits e) (listCode e)
  let j := unaryToBits.comp (first unaryCode env)
  let old := (nthDP e d).comp (j.pair (xs.comp input))
  let eq := PriceGame.Control.Native.natEqP.comp (idx.pair j)
  let op := conditional eq value old
  let f := fun (z : (ℕ × α) × List α) (k : ℕ) => if z.1.1 = k then z.1.2 else z.2[k]?.getD d
  have entry : Procedure (prodCode unaryCode env) e (fun z => f z.2 z.1) :=
    op.congrFun (by intro z; simp [f,Function.comp_apply,id_eq])
  exact (tabulateAlongP d d xs entry).congrFun (by
    rintro ⟨⟨i,x⟩,as⟩
    change (List.range as.length).map (fun k => if i = k then x else as[k]?.getD d) = as.set i x
    apply List.ext_getElem
    · simp
    · intro j _ hj
      have h : j < as.length := by simpa using hj
      simp [List.getElem_set,List.getElem?_eq_getElem h])

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
