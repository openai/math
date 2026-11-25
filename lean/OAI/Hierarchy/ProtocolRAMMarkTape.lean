import OAI.Hierarchy.ProtocolRAMFieldLoop
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Fixed native interpreter of addressed Boolean updates to the live mark bank -/

namespace Hierarchy.ProtocolRAM.MarkTape
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w r k : ℕ}

structure Gate where
  lhs : ℕ
  rhs : ℕ
  dst : ℕ
deriving DecidableEq

def Gate.apply (g : Gate) (m : Memory w) : Memory w :=
  Function.update m g.dst (1-BinaryOp.bitAnd.eval (m g.lhs) (m g.rhs))

def eval (gs : List Gate) (m : Memory w) := gs.foldl (fun a g => g.apply a) m

theorem frame (gs : List Gate) (m : Memory w) (a : ℕ) (safe : ∀g∈gs,a≠g.dst) :
    eval gs m a = m a := by
  induction gs generalizing m with
  | nil => rfl
  | cons g gs ih =>
    exact (ih (g.apply m) (fun c hc=>safe c (List.mem_cons_of_mem g hc))).trans
      (Function.update_of_ne (safe g (List.mem_cons_self ..)) ..)

def ops : List (Op 7 4) :=
  [.publicWord 2 0,.binary .add 2 2 0,.read 2 2,.read 2 2,
   .publicWord 3 1,.binary .add 3 3 0,.read 3 3,.read 3 3,
   .binary .bitAnd 4 2 3,.constant 5 1,.binary .sub 4 5 4,
   .publicWord 6 2,.binary .add 6 6 0,.read 6 6,.write 6 4,.binary .add 0 0 5]

def procedure (w base n : ℕ) : Procedure w :=
  ⟨19,7,4,OrdinalOpLoop.block w ops 0 1 3,![(base:Word w),((base+n:ℕ):Word w),((base+2*n:ℕ):Word w),(n:Word w)]⟩

def Packed (base : ℕ) (gs : List Gate) (m : Memory w) : Prop :=
  ∀ i : Fin gs.length, m (base+i.val)=((gs.get i).lhs:Word w) ∧
      m (base+gs.length+i.val)=((gs.get i).rhs:Word w) ∧
      m (base+2*gs.length+i.val)=((gs.get i).dst:Word w)

private theorem trace_step (reg : Fin 7 ↪ Fin r) (pub : Fin 4 → Fin k) (v : Fin k → Word w)
    (state : Word w) (rs : Regs w r) (m : Memory w) :
    let read (j : Fin 4) := m (v (pub j)+rs (reg 0)).val
    ∃ es out, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,out,writeMemory m (read 2) (1-BinaryOp.bitAnd.eval (m (read 0).val) (m (read 1).val))) ∧
      out (reg 0)=rs (reg 0)+1 ∧ out (reg 1)=rs (reg 1) := by
  dsimp only
  simp [ops,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff]

/-- All three addresses are read at runtime from a dense native tape. Destination
addresses may repeat, so each instruction sees the current external mark and flag. -/
theorem run (base : ℕ) (gs : List Gate) (m : Memory w) (tape : Packed base gs m)
    (space : base+3*gs.length<2^w)
    (bounds : ∀ g∈gs, g.lhs<2^w ∧ g.rhs<2^w ∧ base+3*gs.length≤g.dst ∧ g.dst<2^w) :
    (procedure w base gs.length).Exec m (eval gs m) (3+17*gs.length) := by
  intro P R K M pc reg pub exit rom data c start entry eqm
  subst start
  change Fin 7 ↪ Fin R at reg
  change Fin 4 → Fin K at pub
  change ∀ i,M.publicData (pub i)=(![(base:Word w),((base+gs.length:ℕ):Word w),((base+2*gs.length:ℕ):Word w),(gs.length:Word w)] : Fin 4→Word w) i at data
  let mem i := eval (gs.take i) m
  obtain ⟨out,ran,stop⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 3 M pc reg pub exit rom gs.length
    (by omega) (data 3) mem (by
      intro i hi state rs cur limit
      let z : Fin gs.length := ⟨i,hi⟩
      let g := gs.get z
      have inList : g∈gs := List.get_mem ..
      obtain ⟨leftFit,rightFit,_,outFit⟩ := bounds g inList
      have old (a : ℕ) (lo : a < base+3*gs.length) : mem i a=m a := by
        apply frame
        intro p hp
        have floor := (bounds p (List.mem_of_mem_take hp)).2.2.1
        omega
      obtain ⟨es,u,actual,inc,lim⟩ := trace_step reg pub M.publicData state rs (mem i)
      refine ⟨es,u,?_,by simpa [cur] using inc,lim.trans limit⟩
      dsimp only at actual
      rw [data 0,data 1,data 2,cur] at actual
      have read (a : ℕ) (lo : a+i<base+3*gs.length) :
          mem i ((a:Word w)+(i:Word w)).val = m (a+i) := by
        rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega : a+i<2^w),old _ lo]
      obtain ⟨left,right,out⟩ := tape z
      change m (base+i)=(g.lhs:Word w) at left
      change m (base+gs.length+i)=(g.rhs:Word w) at right
      change m (base+2*gs.length+i)=(g.dst:Word w) at out
      change trace _ _ _ _ _=some (_,_,writeMemory (mem i)
        (mem i (((base+2*gs.length:ℕ):Word w)+(i:Word w)).val)
        (1-BinaryOp.bitAnd.eval (mem i (mem i ((base:Word w)+(i:Word w)).val).val)
          (mem i (mem i (((base+gs.length:ℕ):Word w)+(i:Word w)).val).val))) at actual
      rw [read _ (by omega),read _ (by omega),read _ (by omega),left,right,out,
        Fin.val_cast_of_lt leftFit,Fin.val_cast_of_lt rightFit] at actual
      have next : writeMemory (mem i) (g.dst:Word w)
          (1-BinaryOp.bitAnd.eval (mem i g.lhs) (mem i g.rhs)) = mem (i+1) := by
        have step : mem (i+1)=g.apply (mem i) := by
          change (gs.take (i+1)).foldl (fun a x=>Gate.apply x a) m=_
          rw [List.take_succ_eq_append_getElem hi,List.foldl_append]
          rfl
        rw [step]
        funext a
        simp [writeMemory,Gate.apply,Fin.val_cast_of_lt outFit,Function.update_apply]
      rwa [next] at actual) c entry
  have opCost : 1+ops.length=17 := rfl
  refine ⟨3+gs.length*17,by omega,out,mem gs.length,?_,stop,?_⟩
  · simpa only [opCost,mem,List.take_zero,eval,List.foldl_nil] using ran
  · simp only [mem,List.take_length]

def markInstruction {P R K : ℕ} : Instr w P R K → Prop
  | .binary o .. => o=.add ∨ o=.sub ∨ o=.bitAnd
  | .constant .. | .publicWord .. | .readExternal .. | .writeExternal .. | .jumpLt .. => True
  | _ => False

set_option maxRecDepth 8192 in
theorem cheap (w base n : ℕ) {P R K : ℕ} (pc : Fin 19 ↪ Fin P) (reg : Fin 7 ↪ Fin R)
    (pub : Fin 4 → Fin K) (exit : Fin P) (i : Fin 19) :
    markInstruction ((procedure w base n).block.emit pc reg pub exit i) := by
  fin_cases i <;> first | exact True.intro | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)


end Hierarchy.ProtocolRAM.MarkTape

end OAI
