import OAI.Hierarchy.CheapISAMachine
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace OAI
/-! # The actual bounded decoder executes the selected comparison prefix -/
namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing

def handler : Fin 13→Fin 72 := ![49,50,51,52,53,54,55,56,57,60,63,64,48]

private def compareStart (i : ℕ) (hi : i≤12) : Fin 72 := ⟨24+2*i,by omega⟩
private def compareJump (i : Fin 12) : Fin 72 := ⟨25+2*i.val,by omega⟩

private theorem literal_inst (w p r : ℕ) (entry : Fin p) (i : Fin 12) :
    (machine w p r entry).code (compareStart i.val i.isLt.le)=
      .constant 10 (i.val:Word (width w)) (compareJump i) := by
  fin_cases i <;> rfl

private theorem branch_inst (w p r : ℕ) (entry : Fin p) (i : Fin 12) :
    (machine w p r entry).code (compareJump i)=
      .jumpEq 1 10 (handler i.castSucc) (compareStart (i.val+1) i.isLt) := by
  fin_cases i <;> rfl

private theorem literal_eq (w : ℕ) (tag : Fin 13) (i : Fin 12) :
    (tag.val:Word (width w))=(i.val:Word (width w)) ↔ tag.val=i.val := by
  have room : 32≤2^width w := (show 32=2^5 by decide) ▸
    Nat.pow_le_pow_right (by decide : 0<2) (show 5≤width w by unfold width;omega)
  constructor
  · intro eqn
    exact (Fin.val_cast_of_lt (show tag.val<2^width w by omega)).symm.trans
      ((congrArg Fin.val eqn).trans (Fin.val_cast_of_lt (show i.val<2^width w by omega)))
  · exact fun eqn => congrArg (fun z : ℕ=>(z:Word (width w))) eqn

private def afterPair {w : ℕ} (d : Config (width w) 72 13) (i : Fin 12) (pc : Fin 72) :
    Config (width w) 72 13 := {d with pc:=pc,reg:=Function.update d.reg 10 (i.val:Word (width w))}

private theorem compare_pair {w p r k : ℕ} (M : Machine w p r k) (d : Config (width w) 72 13)
    (n : Memory (width w)) (tag : Fin 13) (i : Fin 12) (atStart : d.pc=compareStart i.val i.isLt.le)
    (read : d.reg 1=(tag.val:Word (width w))) :
    advance (machine w p r M.entry).program 2 d n=some (afterPair d i
      (if tag.val=i.val then handler i.castSucc else compareStart (i.val+1) i.isLt),n) := by
  let U:=machine w p r M.entry
  let mid:=d.put (compareJump i) 10 (i.val:Word (width w))
  have first : U.program.step d=.localStep mid := by
    change (((machine w p r M.entry).code d.pc).run U.publicData d)=_
    rw [atStart,literal_inst]; rfl
  have second : U.program.step mid=.localStep (afterPair d i
      (if tag.val=i.val then handler i.castSucc else compareStart (i.val+1) i.isLt)) := by
    change (((machine w p r M.entry).code (compareJump i)).run U.publicData mid)=_
    rw [branch_inst]
    simp only [Instr.run,mid,Config.put,Function.update_of_ne (by decide : (1:Fin 13)≠10),
      Function.update_self,read,literal_eq,afterPair]
  change advance U.program 2 d n=_
  simp only [advance,first,second]

/-- Twelve physical tag tests, each a constant followed by a conditional jump.
The unmatched thirteenth tag lands at the native reject instruction. -/
theorem dispatch {w p r k : ℕ} (M : Machine w p r k) (d : Config (width w) 72 13)
    (n : Memory (width w)) (atDecode : d.pc=24) (tag : Fin 13)
    (read : d.reg 1=(tag.val:Word (width w))) :
    ∃ δ out,δ≤24 ∧ advance (machine w p r M.entry).program δ d n=some (out,n) ∧
      out.pc=handler tag ∧ out.persistent=d.persistent ∧ ∀j:Fin 13,j≠10→ out.reg j=d.reg j := by
  have before (s : ℕ) (hs : s≤tag.val) :
      ∃ out,advance (machine w p r M.entry).program (2*s) d n=some (out,n) ∧
        out.pc=compareStart s (by omega) ∧ out.persistent=d.persistent ∧
        ∀j:Fin 13,j≠10→ out.reg j=d.reg j := by
    induction s with
    | zero =>
      exact ⟨d,rfl,atDecode,rfl,fun _ _=>rfl⟩
    | succ t ih =>
      obtain ⟨old,ran,pc,st,regs⟩:=ih (by omega)
      let i : Fin 12:=⟨t,by omega⟩
      have test : tag.val≠i.val := by dsimp only [i];omega
      have landing:=compare_pair M old n tag i pc ((regs 1 (by decide)).trans read)
      rw [ite_eq_right test] at landing
      refine ⟨afterPair old i (compareStart (i.val+1) i.isLt),by simpa only [Nat.mul_succ] using advance_trans ran landing,rfl,st,?_⟩
      intro j hj
      exact (Function.update_of_ne hj _ _).trans (regs j hj)
  obtain ⟨old,ran,pc,st,regs⟩:=before tag.val le_rfl
  by_cases fits : tag.val<12
  · let i : Fin 12:=⟨tag.val,fits⟩
    have landing:=compare_pair M old n tag i pc ((regs 1 (by decide)).trans read)
    rw [ite_eq_left (show tag.val=i.val from rfl)] at landing
    have same : i.castSucc=tag:=Fin.ext rfl
    refine ⟨2*tag.val+2,_,by omega,advance_trans ran landing,?_,st,?_⟩
    · exact congrArg handler same
    · intro j hj
      exact (Function.update_of_ne hj _ _).trans (regs j hj)
  · have last : tag=(12:Fin 13) := Fin.ext (show tag.val=12 by omega)
    refine ⟨2*tag.val,old,by omega,ran,?_,st,regs⟩
    exact pc.trans (by subst tag;rfl)

end Hierarchy.CheapISA

end OAI
