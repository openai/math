import OAI.Hierarchy.CheapISAHandlers
import OAI.Hierarchy.CheapISADecode

namespace OAI
/-! # The widened instruction decoder preserves the original registers and RAM -/

namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing

variable {w p r k : ℕ}

def tick {C : Type*} (a : CallAction w C) (m : Memory w) : Option (C × Memory w) :=
  match a with
  | .localStep next => some (next,m)
  | .read a ret => some (ret (m a.val),m)
  | .write a v next => some (next,writeMemory m a v)
  | _ => none

theorem one (M : Machine w p r k) (c : Config w p r) (m : Memory w) :
    advance M.program 1 c m=tick ((M.code c.pc).run M.publicData c) m := by
  simp only [advance,Machine.program]
  cases (M.code c.pc).run M.publicData c <;> rfl

private theorem matching (M : Machine w p r k) (hp : p≤2^(w+1)) (hr : r≤2^(w+1))
    (i : Instr w p r k) (cheap : TaggedShorterCheapCPU.Cheap i)
    {c m d n c' m'} (h : Entered M i c m d n) (ran : tick (i.run M.publicData c) m=some (c',m')) :
    ∃op : Fin 10,d.pc=Body.label op ∧ Body.next op d=(c'.pc.val : Word (width w)) ∧
      c'.persistent=c.persistent ∧ Banks (ROM M) c'.reg m' (Body.memory p r op d n) := by
  obtain ⟨pc,held,banks,imm,xv,yv,dst,yes,no⟩:=h
  have load (j : Fin r) : n (regAddr p j : Word (width w)).val=wide (c.reg j) := by
    rw [Fin.val_cast_of_lt (reg_fits hp hr j),banks.register]
  cases i with
  | constant t v q =>
    simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
    rcases ran with ⟨rfl,rfl⟩
    have val : Body.result p r 0 d n=wide (v) := by
      exact imm
    change d.reg 5=(regAddr p t : Word (width w)) at dst
    refine ⟨0,pc,yes,rfl,?_⟩
    change Banks (ROM M) _ _ (writeMemory n (d.reg 5) (Body.result p r 0 d n))
    rw [val,dst]
    exact banks.putReg hp hr t _
  | publicWord t j q =>
    simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
    rcases ran with ⟨rfl,rfl⟩
    have val : Body.result p r 0 d n=wide (M.publicData j) := by
      exact imm
    change d.reg 5=(regAddr p t : Word (width w)) at dst
    refine ⟨0,pc,yes,rfl,?_⟩
    change Banks (ROM M) _ _ (writeMemory n (d.reg 5) (Body.result p r 0 d n))
    rw [val,dst]
    exact banks.putReg hp hr t _
  | stateWord t q =>
    simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
    rcases ran with ⟨rfl,rfl⟩
    have val : Body.result p r 1 d n=wide (c.persistent) := by
      exact held
    change d.reg 5=(regAddr p t : Word (width w)) at dst
    refine ⟨1,pc,yes,rfl,?_⟩
    change Banks (ROM M) _ _ (writeMemory n (d.reg 5) (Body.result p r 1 d n))
    rw [val,dst]
    exact banks.putReg hp hr t _
  | copy t x q =>
    simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
    rcases ran with ⟨rfl,rfl⟩
    have X : d.reg 8=wide (c.reg x) := xv.trans (load x)
    have val : Body.result p r 2 d n=wide (c.reg x) := by
      exact X
    change d.reg 5=(regAddr p t : Word (width w)) at dst
    refine ⟨2,pc,yes,rfl,?_⟩
    change Banks (ROM M) _ _ (writeMemory n (d.reg 5) (Body.result p r 2 d n))
    rw [val,dst]
    exact banks.putReg hp hr t _
  | binary op t x y q =>
    cases op with
    | add =>
      simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
      rcases ran with ⟨rfl,rfl⟩
      have X : d.reg 8=wide (c.reg x) := xv.trans (load x)
      have Y : d.reg 9=wide (c.reg y) := yv.trans (load y)
      have val : Body.result p r 3 d n=wide (c.reg x+c.reg y) := by
        change BinaryOp.bitAnd.eval (d.reg 8+d.reg 9) (mask w)=_; rw [X,Y,wide_add]
      change d.reg 5=(regAddr p t : Word (width w)) at dst
      refine ⟨3,pc,yes,rfl,?_⟩
      change Banks (ROM M) _ _ (writeMemory n (d.reg 5) (Body.result p r 3 d n))
      rw [val,dst]
      exact banks.putReg hp hr t _
    | sub =>
      simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
      rcases ran with ⟨rfl,rfl⟩
      have X : d.reg 8=wide (c.reg x) := xv.trans (load x)
      have Y : d.reg 9=wide (c.reg y) := yv.trans (load y)
      have val : Body.result p r 4 d n=wide (c.reg x-c.reg y) := by
        change BinaryOp.bitAnd.eval (d.reg 8-d.reg 9) (mask w)=_; rw [X,Y,wide_sub]
      change d.reg 5=(regAddr p t : Word (width w)) at dst
      refine ⟨4,pc,yes,rfl,?_⟩
      change Banks (ROM M) _ _ (writeMemory n (d.reg 5) (Body.result p r 4 d n))
      rw [val,dst]
      exact banks.putReg hp hr t _
    | bitAnd =>
      simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
      rcases ran with ⟨rfl,rfl⟩
      have X : d.reg 8=wide (c.reg x) := xv.trans (load x)
      have Y : d.reg 9=wide (c.reg y) := yv.trans (load y)
      have val : Body.result p r 5 d n=wide (BinaryOp.bitAnd.eval (c.reg x) (c.reg y)) := by
        change BinaryOp.bitAnd.eval (d.reg 8) (d.reg 9)=_; rw [X,Y,wide_bitAnd]
      change d.reg 5=(regAddr p t : Word (width w)) at dst
      refine ⟨5,pc,yes,rfl,?_⟩
      change Banks (ROM M) _ _ (writeMemory n (d.reg 5) (Body.result p r 5 d n))
      rw [val,dst]
      exact banks.putReg hp hr t _
    | _ => exact False.elim cheap
  | jumpEq x y q z =>
    simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
    rcases ran with ⟨rfl,rfl⟩
    have X : d.reg 8=wide (c.reg x) := xv.trans (load x)
    have Y : d.reg 9=wide (c.reg y) := yv.trans (load y)
    refine ⟨6,pc,?_,rfl,banks⟩
    change (if d.reg 8=d.reg 9 then d.reg 6 else d.reg 7)=_
    by_cases eqn : c.reg x=c.reg y
    · simp only [X,Y,wide_injective.eq_iff,ite_eq_left eqn]
      exact yes
    · simp only [X,Y,wide_injective.eq_iff,ite_eq_right eqn]
      exact no
  | jumpLt x y q z =>
    simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
    rcases ran with ⟨rfl,rfl⟩
    have X : d.reg 8=wide (c.reg x) := xv.trans (load x)
    have Y : d.reg 9=wide (c.reg y) := yv.trans (load y)
    refine ⟨7,pc,?_,rfl,banks⟩
    change (if d.reg 8<d.reg 9 then d.reg 6 else d.reg 7)=_
    by_cases lt : c.reg x<c.reg y
    · simp only [X,Y,wide_lt_iff,ite_eq_left lt]
      exact yes
    · simp only [X,Y,wide_lt_iff,ite_eq_right lt]
      exact no
  | readExternal t x q =>
    simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
    rcases ran with ⟨rfl,rfl⟩
    have X : d.reg 8=wide (c.reg x) := xv.trans (load x)
    have address : Body.dataAddress p r d=(dataAddr p r (c.reg x) : Word (width w)) := by
      rw [Body.dataAddress,X,← dataAddr_word]
    have val : Body.result p r 8 d n=wide (m (c.reg x).val) := by
      change n (Body.dataAddress p r d).val=_
      rw [address,Fin.val_cast_of_lt (data_fits hp hr _),banks.exterior]
    change d.reg 5=(regAddr p t : Word (width w)) at dst
    refine ⟨8,pc,yes,rfl,?_⟩
    change Banks (ROM M) _ _ (writeMemory n (d.reg 5) (Body.result p r 8 d n))
    rw [val,dst]
    exact banks.putReg hp hr t _
  | writeExternal x y q =>
    simp only [Instr.run,tick,Option.some.injEq,Prod.mk.injEq] at ran
    rcases ran with ⟨rfl,rfl⟩
    have X : d.reg 8=wide (c.reg x) := xv.trans (load x)
    have Y : d.reg 9=wide (c.reg y) := yv.trans (load y)
    have address : Body.dataAddress p r d=(dataAddr p r (c.reg x) : Word (width w)) := by
      rw [Body.dataAddress,X,← dataAddr_word]
    refine ⟨9,pc,yes,rfl,?_⟩
    change Banks (ROM M) _ _ (writeMemory n (Body.dataAddress p r d) (d.reg 9))
    rw [address,Y]
    exact banks.putData hp hr _ _
  | loadPrivate => exact False.elim cheap
  | storePrivate => exact False.elim cheap
  | choose => exact False.elim cheap
  | returnState => contradiction
  | accept => contradiction
  | reject => contradiction

/-- A successful original instruction produces exactly its new register file,
persistent state and observed memory at the next native fetch. -/
theorem commit (M : Machine w p r k) (hp : p≤2^(w+1)) (hr : r≤2^(w+1))
    (cheap : ∀q,TaggedShorterCheapCPU.Cheap (M.code q))
    {c m d n c' m'} (h : Entered M (M.code c.pc) c m d n)
    (ran : advance M.program 1 c m=some (c',m')) :
    ∃s e o,s≤5 ∧ advance (machine w p r M.entry).program s d n=some (e,o) ∧ Rel M c' m' e o := by
  rw [one] at ran
  obtain ⟨op,atBody,next,persist,mem⟩:=matching M hp hr _ (cheap c.pc) h ran
  obtain ⟨e,go,entry,pc,held⟩:=Body.run M.entry op d n atBody
  exact ⟨Body.ticks op,e,_,Body.ticks_le op,go,entry,pc.trans next,
    held.trans (h.held.trans (congrArg wide persist.symm)),mem⟩

end Hierarchy.CheapISA

end OAI
