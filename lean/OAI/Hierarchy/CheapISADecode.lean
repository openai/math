import OAI.Hierarchy.CheapISAFetch
import OAI.Hierarchy.CheapISADispatch

namespace OAI
/-! # Reading an actual original instruction and entering its physical handler -/

namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing

variable {w p r k : ℕ}

def opcode : Instr w p r k → Fin 13
  | .constant .. | .publicWord .. => 0
  | .stateWord .. => 1
  | .copy .. => 2
  | .binary .add .. => 3
  | .binary .sub .. => 4
  | .binary .bitAnd .. => 5
  | .jumpEq .. => 6
  | .jumpLt .. => 7
  | .readExternal .. => 8
  | .writeExternal .. => 9
  | .returnState .. => 10
  | .accept => 11
  | _ => 12

theorem fields_tag (pub : Fin k→Word w) (i : Instr w p r k) :
    fields pub i 0 = ((opcode i).val : Word (width w)) := by
  cases i <;> try rfl
  case binary op _ _ _ _ => cases op <;> rfl

/-- Data available without another instruction fetch. Source values are the
two literal external loads, including their defined values on unused ports. -/
structure Entered (M : Machine w p r k) (i : Instr w p r k) (c : Config w p r) (m : Memory w)
    (d : Config (width w) 72 13) (n : Memory (width w)) : Prop where
  pc : d.pc=handler (opcode i)
  held : d.persistent=wide c.persistent
  banks : Banks (ROM M) c.reg m n
  imm : d.reg 2=fields M.publicData i 1
  x : d.reg 8=n (fields M.publicData i 2).val
  y : d.reg 9=n (fields M.publicData i 3).val
  dst : d.reg 5=fields M.publicData i 4
  yes : d.reg 6=fields M.publicData i 5
  no : d.reg 7=fields M.publicData i 6

theorem decode (M : Machine w p r k) (hp : p≤2^(w+1)) (hr : r≤2^(w+1))
    {c m d n} (rep : Rel M c m d n) :
    ∃t e,t≤47 ∧ advance (machine w p r M.entry).program t d n=some (e,n) ∧
      Entered M (M.code c.pc) c m e n := by
  obtain ⟨f,ran,h⟩:=fetch M hp hr rep
  have tag : f.reg 1=((opcode (M.code c.pc)).val:Word (width w)) :=
    (h.field 0).trans (fields_tag ..)
  obtain ⟨s,e,short,go,pc,st,eqs⟩:=dispatch M f n h.atDecode _ tag
  refine ⟨23+s,e,by omega,advance_trans ran go,pc,st.trans h.persistent,h.banks,?_,?_,?_,?_,?_,?_⟩
  · exact (eqs 2 (by decide)).trans (h.field 1)
  · exact (eqs 8 (by decide)).trans h.left
  · exact (eqs 9 (by decide)).trans h.right
  · exact (eqs 5 (by decide)).trans (h.field 4)
  · exact (eqs 6 (by decide)).trans (h.field 5)
  · exact (eqs 7 (by decide)).trans (h.field 6)

end Hierarchy.CheapISA

end OAI
