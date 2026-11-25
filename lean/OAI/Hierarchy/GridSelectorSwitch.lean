import OAI.ThreeFlat.RAM.TickProcedureContracts
import OAI.ThreeFlat.RAM.TickFuel

namespace OAI
/-! # Native selector branch to the idle or compression controller -/

namespace Hierarchy.GridSelectorSwitch
open ThreeFlat.RAM
open ContinuationLink PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM

variable {w P R K : ℕ}

private def front (address : Word w) (pc : Fin 4 ↪ Fin P) (reg : Fin 2 ↪ Fin R)
    (idle sim : Fin P) : Fin 4 → Instr w P R K
  | 0 => .constant (reg 0) address (pc 1)
  | 1 => .readExternal (reg 0) (reg 0) (pc 2)
  | 2 => .constant (reg 1) 0 (pc 3)
  | _ => .jumpEq (reg 0) (reg 1) idle sim

def program (address : Word w) (A B : Procedure w) : Procedure w where
  labels := 4+(A.labels+B.labels)
  registers := 2+(A.registers+B.registers)
  slots := A.slots+B.slots
  publicData := Fin.addCases A.publicData B.publicData
  block := {
    first := Fin.castAdd _ (0 : Fin 4)
    emit := fun pc reg pub exit =>
      let bodyPC := (Fin.natAddEmb 4).trans pc
      let bodyReg := (Fin.natAddEmb 2).trans reg
      let left := (Fin.castAddEmb B.labels).trans bodyPC
      let right := (Fin.natAddEmb A.labels).trans bodyPC
      Fin.addCases
        (front address ((Fin.castAddEmb _).trans pc) ((Fin.castAddEmb _).trans reg)
          (left A.block.first) (right B.block.first))
        (Fin.addCases
          (A.block.emit left ((Fin.castAddEmb B.registers).trans bodyReg) (pub ∘ Fin.castAdd B.slots) exit)
          (B.block.emit right ((Fin.natAddEmb A.registers).trans bodyReg) (pub ∘ Fin.natAdd A.slots) exit)) }

private theorem enter (M : Machine w P R K) (address : Word w) (pc : Fin 4 ↪ Fin P)
    (reg : Fin 2 ↪ Fin R) (left right : Fin P) (c : Config w P R) (m : Memory w)
    (entry : c.pc=pc 0) (text : ∀ i,M.code (pc i)=front address pc reg left right i) :
    ∃ d : Config w P R, advance M.program 4 c m=some (d,m) ∧
      d.pc=(if m address.val=0 then left else right) := by
  let a := c.put (pc 1) (reg 0) address
  let b := a.put (pc 2) (reg 0) (m address.val)
  let z := b.put (pc 3) (reg 1) 0
  let out := { z with pc := if m address.val=0 then left else right }
  refine ⟨out,?_,rfl⟩
  have f0 := text 0
  have f1 := text 1
  have f2 := text 2
  have f3 := text 3
  simp only [front] at f0 f1 f2 f3
  have ne := reg.injective.ne (by decide : (0 : Fin 2)≠1)
  simp [advance,Machine.program,Instr.run,entry,f0,f1,f2,f3,Config.put,a,b,z,out]

/-- The native four-row selector read executes before either of the linked
programs. A rejected selection contributes zero even under arbitrary extra fuel. -/
theorem admission {F : Type*} [Semiring F] (field : FieldCode F w) (address : Word w)
    (A B : Procedure w) (pre ok : Memory w → Prop) (post : Memory w → Memory w → Prop)
    (ta tb : ℕ)
    (idle : TickStageSpec.Admission field A.block A.publicData (fun m => pre m ∧ m address.val=0) ok post ta)
    (sim : TickStageSpec.Admission field B.block B.publicData (fun m => pre m ∧ m address.val≠0) ok post tb) :
    TickStageSpec.Admission field (program address A B).block (program address A B).publicData
      pre ok post (4+max ta tb) := by
  intro P R K M pc reg pub exit text values c m entry hpre
  let bp := (Fin.natAddEmb 4).trans pc
  let br := (Fin.natAddEmb 2).trans reg
  let lp := (Fin.castAddEmb B.labels).trans bp
  let rp := (Fin.natAddEmb A.labels).trans bp
  let lr := (Fin.castAddEmb B.registers).trans br
  let rr := (Fin.natAddEmb A.registers).trans br
  let fp := (Fin.castAddEmb (A.labels+B.labels)).trans pc
  let fr := (Fin.castAddEmb (A.registers+B.registers)).trans reg
  have inst (i : Fin 4) : M.code (fp i)=front address fp fr (lp A.block.first) (rp B.block.first) i := by
    change M.code (pc (i.castAdd (A.labels+B.labels)))=front address fp fr
      (pc (Fin.natAdd 4 (A.block.first.castAdd B.labels)))
      (pc (Fin.natAdd 4 (Fin.natAdd A.labels B.block.first))) i
    have row := text (i.castAdd (A.labels+B.labels))
    dsimp only [program] at row
    rw [Fin.addCases_left] at row
    exact row
  obtain ⟨c',moved,there⟩ := enter M address fp fr (lp A.block.first) (rp B.block.first) c m entry inst
  rcases eq_or_ne (m address.val) 0 with h|h
  · have iA : A.block.Installed M lp lr (pub ∘ Fin.castAdd B.slots) exit := fun i => by
      change M.code (pc (Fin.natAdd 4 (i.castAdd B.labels)))=A.block.emit lp lr _ exit i
      simpa [program,lp,lr,bp,br] using text (Fin.natAdd 4 (i.castAdd B.labels))
    have words i : M.publicData (pub (Fin.castAdd B.slots i))=A.publicData i := by
      simpa [program] using values (Fin.castAdd B.slots i)
    rcases idle M lp lr _ exit iA words c' m (by simpa [h] using there) ⟨hpre,h⟩ with ⟨yes,no⟩
    refine ⟨fun good => ?_,fun bad => TickFuel.Returns.later (TickFuel.Returns.prefix moved (no bad)) (by omega)⟩
    obtain ⟨t,ht,d,o,pos,hit,done⟩ := yes good
    exact ⟨4+t,by omega,d,o,pos,hit,advance_trans moved done⟩
  · have iB : B.block.Installed M rp rr (pub ∘ Fin.natAdd A.slots) exit := fun i => by
      change M.code (pc (Fin.natAdd 4 (Fin.natAdd A.labels i)))=B.block.emit rp rr _ exit i
      simpa [program,rp,rr,bp,br] using text (Fin.natAdd 4 (Fin.natAdd A.labels i))
    have words i : M.publicData (pub (Fin.natAdd A.slots i))=B.publicData i := by
      simpa [program] using values (Fin.natAdd A.slots i)
    rcases sim M rp rr _ exit iB words c' m (by simpa [h] using there) ⟨hpre,h⟩ with ⟨yes,no⟩
    refine ⟨fun good => ?_,fun bad => TickFuel.Returns.later (TickFuel.Returns.prefix moved (no bad)) (by omega)⟩
    obtain ⟨t,ht,d,o,pos,hit,done⟩ := yes good
    exact ⟨4+t,by omega,d,o,pos,hit,advance_trans moved done⟩

end Hierarchy.GridSelectorSwitch

end OAI
