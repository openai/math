import OAI.ThreeFlat.RAM.AdmissionHeader
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # Choosing a native procedure by evaluating a word in external memory -/

namespace ThreeFlat.RAM.PhysicalProcedure

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr ContinuationLink
open scoped Fin.CommRing

variable {w p r k : ℕ}

private abbrev GuardLabels (f : Formula 1) := 3+(3*f.work+1)
private abbrev GuardRegisters (f : Formula 1) := 2+f.work

private def testExpr (f : Formula 1) : Term w k 1 := AdmissionBank.closed f

private theorem scratchSize (f : Formula 1) : (testExpr (w:=w) (k:=k) f).binds=f.work :=
  AdmissionBank.binds_closed f

private theorem codeSize (f : Formula 1) : (testExpr (w:=w) (k:=k) f).labels=3*f.work+1 := by
  rw [Term.labels_eq,scratchSize]

private def gate (f : Formula 1) (pc : Fin (GuardLabels f) ↪ Fin p) (i : Fin 3) :=
  pc (i.castAdd (3*f.work+1))

private def exprPC (f : Formula 1) (pc : Fin (GuardLabels f) ↪ Fin p)
    (i : Fin (testExpr (w:=w) (k:=k) f).labels) := pc (Fin.natAdd 3 (i.cast (codeSize f)))

private def flag (f : Formula 1) (reg : Fin (GuardRegisters f) ↪ Fin r) (i : Fin 2) :=
  reg (i.castAdd f.work)

private def temps (f : Formula 1) (reg : Fin (GuardRegisters f) ↪ Fin r) :
    Fin (testExpr (w:=w) (k:=k) f).binds ↪ Fin r :=
  ((Fin.castLEEmb (scratchSize f).le).trans (Fin.natAddEmb 2)).trans reg

private def jumps (f : Formula 1) (pc : Fin (GuardLabels f) ↪ Fin p)
    (reg : Fin (GuardRegisters f) ↪ Fin r) (yes no : Fin p) : Fin 3 → Instr w p r k
  | 0 => .constant (flag f reg 0) 0 (exprPC f pc (testExpr (w:=w) (k:=k) f).first)
  | 1 => .constant (flag f reg 0) 0 (gate f pc 2)
  | _ => .jumpEq (flag f reg 0) (flag f reg 1) no yes

private def rows (f : Formula 1) (pc : Fin (GuardLabels f) ↪ Fin p)
    (reg : Fin (GuardRegisters f) ↪ Fin r) (yes no : Fin p) :
    Fin (GuardLabels f) → Instr w p r k :=
  Fin.addCases (jumps f pc reg yes no) fun i =>
    (testExpr (w:=w) (k:=k) f).emit (exprPC f pc) (fun _ => flag f reg 0)
      (temps f reg) (flag f reg 1) (gate f pc 1) (i.cast (codeSize f).symm)

/-- The tested operand and the optional public shape parameters are initialized to zero. -/
def ifWord (f : Formula 1) (m : Memory w) : Word w := f.value (fun _ => 0) m (fun _ => 0)

private theorem run_guard (f : Formula 1) (M : Machine w p r k) (pc : Fin (GuardLabels f) ↪ Fin p)
    (reg : Fin (GuardRegisters f) ↪ Fin r) (yes no : Fin p)
    (rom : ∀ i, M.code (pc i)=rows f pc reg yes no i)
    (c : Config w p r) (m : Memory w) (entry : c.pc=gate f pc 0) :
    ∃ d : Config w p r, advance M.program (2*f.work+4) c m=some (d,m) ∧
      d.pc=(if ifWord f m=0 then no else yes) := by
  let e := testExpr (w:=w) (k:=k) f
  have gateRom (i : Fin 3) : M.code (gate f pc i)=jumps f pc reg yes no i := by
    simpa only [gate,rows,Fin.addCases_left] using rom (i.castAdd (3*f.work+1))
  have prog (i : Fin e.labels) : M.code (exprPC f pc i) =
      e.emit (exprPC f pc) (fun _ => flag f reg 0) (temps f reg) (flag f reg 1) (gate f pc 1) i := by
    simpa only [e,exprPC,rows,Fin.addCases_right,Fin.cast_cast,Fin.cast_refl,id_eq] using
      rom (Fin.natAdd 3 (i.cast (codeSize f)))
  let boot := c.put (exprPC f pc e.first) (flag f reg 0) 0
  have bootRun : advance M.program 1 c m=some (boot,m) := by
    simp [advance,Machine.program,entry,gateRom,jumps,Instr.run,boot,e]
  let out := e.run M.publicData m (fun _ => flag f reg 0) (temps f reg) (flag f reg 1) (gate f pc 1) boot
  have guardSteps : advance M.program e.steps boot m=some (out,m) :=
    e.advance_emit M _ _ _ _ _ prog boot m rfl
  have fresh : ∀ (_ : Fin 1) (j : Fin e.binds), flag f reg 0 ≠ temps f reg j := by
    intro _ j h
    have v := congrArg Fin.val (reg.injective h)
    change 0=2+j.val at v
    omega
  have result : out.reg (flag f reg 1)=ifWord f m := by
    rw [show out.reg (flag f reg 1) = e.eval M.publicData m (boot.reg ∘ fun _ : Fin 1 => flag f reg 0) from
      e.run_result _ _ _ _ _ _ _ fresh (temps f reg).injective]
    simp [e,testExpr,AdmissionBank.eval_closed,boot,Config.put,Function.comp_def,ifWord]
  have outPC : out.pc=gate f pc 1 := e.run_pc ..
  have diff : flag f reg 1 ≠ flag f reg 0 := by
    intro h
    have v := congrArg Fin.val (reg.injective h)
    change 1=0 at v
    omega
  have endStep : ∃ d : Config w p r, advance M.program 2 out m=some (d,m) ∧
      d.pc=(if ifWord f m=0 then no else yes) := by
    by_cases h : ifWord f m=0
    · simp [advance,Machine.program,outPC,gateRom,jumps,Instr.run,Config.put,
        Function.update_of_ne diff,result,h]
    · simp [advance,Machine.program,outPC,gateRom,jumps,Instr.run,Config.put,
        Function.update_of_ne diff,result,h,Ne.symm h]
  obtain ⟨d,finish,here⟩ := endStep
  have time : 1+e.steps+2=2*f.work+4 := by rw [Term.steps_eq,scratchSize]; omega
  refine ⟨d,?_,here⟩
  rw [←time]
  exact advance_trans (advance_trans bootRun guardSteps) finish

/-- Evaluate the fixed predicate and enter exactly one of the two supplied procedures. -/
def ifValue (f : Formula 1) (yes no : Procedure w) : Procedure w where
  labels := GuardLabels f+(yes.labels+no.labels)
  registers := GuardRegisters f+(yes.registers+no.registers)
  slots := yes.slots+no.slots
  publicData := Fin.addCases yes.publicData no.publicData
  block := {
    first := ((0 : Fin 3).castAdd (3*f.work+1)).castAdd (yes.labels+no.labels)
    emit := fun pc reg pub exit =>
      let G := (Fin.castAddEmb (yes.labels+no.labels)).trans pc
      let B := (Fin.natAddEmb (GuardLabels f)).trans pc
      let R := (Fin.castAddEmb (yes.registers+no.registers)).trans reg
      let S := (Fin.natAddEmb (GuardRegisters f)).trans reg
      let Y := (Fin.castAddEmb no.labels).trans B
      let N := (Fin.natAddEmb yes.labels).trans B
      Fin.addCases (rows f G R (Y yes.block.first) (N no.block.first)) (Fin.addCases
        (yes.block.emit Y ((Fin.castAddEmb no.registers).trans S) (pub ∘ Fin.castAdd no.slots) exit)
        (no.block.emit N ((Fin.natAddEmb yes.registers).trans S) (pub ∘ Fin.natAdd yes.slots) exit)) }

/-- For each initial memory the budget pays for the branch that runs. -/
theorem ifValue_spec (f : Formula 1) (yes no : Procedure w) (pre : Memory w → Prop)
    (post : Memory w → Memory w → Prop) (cost : Memory w → ℕ) (budget : ℕ)
    (bound : ∀ m, pre m → 2*f.work+4+cost m≤budget)
    (onYes : ∀ m, pre m → ifWord f m≠0 → yes.Spec (fun x => x=m) post (cost m))
    (onNo : ∀ m, pre m → ifWord f m=0 → no.Spec (fun x => x=m) post (cost m)) :
    (ifValue f yes no).Spec pre post budget := by
  intro P R K M pc reg pub exit rom table c m entry hm
  let G := (Fin.castAddEmb (yes.labels+no.labels)).trans pc
  let B := (Fin.natAddEmb (GuardLabels f)).trans pc
  let T := (Fin.castAddEmb (yes.registers+no.registers)).trans reg
  let S := (Fin.natAddEmb (GuardRegisters f)).trans reg
  let Y := (Fin.castAddEmb no.labels).trans B
  let N := (Fin.natAddEmb yes.labels).trans B
  have hr (i : Fin (GuardLabels f)) : M.code (G i)=rows f G T (Y yes.block.first) (N no.block.first) i := by
    change M.code (pc (i.castAdd (yes.labels+no.labels))) =
      rows f G T (pc (Fin.natAdd (GuardLabels f) (yes.block.first.castAdd no.labels)))
        (pc (Fin.natAdd (GuardLabels f) (Fin.natAdd yes.labels no.block.first))) i
    have installed := rom (i.castAdd (yes.labels+no.labels))
    simp only [ifValue,Fin.addCases_left] at installed
    exact installed
  have hy : yes.block.Installed M Y ((Fin.castAddEmb no.registers).trans S) (pub ∘ Fin.castAdd no.slots) exit := by
    intro i
    change M.code (pc (Fin.natAdd (GuardLabels f) (i.castAdd no.labels))) =
      yes.block.emit Y ((Fin.castAddEmb no.registers).trans S) (pub ∘ Fin.castAdd no.slots) exit i
    have installed := rom (Fin.natAdd (GuardLabels f) (i.castAdd no.labels))
    simp only [ifValue,Fin.addCases_left,Fin.addCases_right] at installed
    exact installed
  have hn : no.block.Installed M N ((Fin.natAddEmb yes.registers).trans S) (pub ∘ Fin.natAdd yes.slots) exit := by
    intro i
    change M.code (pc (Fin.natAdd (GuardLabels f) (Fin.natAdd yes.labels i))) =
      no.block.emit N ((Fin.natAddEmb yes.registers).trans S) (pub ∘ Fin.natAdd yes.slots) exit i
    have installed := rom (Fin.natAdd (GuardLabels f) (Fin.natAdd yes.labels i))
    simp only [ifValue,Fin.addCases_right] at installed
    exact installed
  have dy (i : Fin yes.slots) : M.publicData ((pub ∘ Fin.castAdd no.slots) i)=yes.publicData i := by
    change M.publicData (pub (i.castAdd no.slots))=yes.publicData i
    simpa only [ifValue,Fin.addCases_left,Function.comp_apply] using table (i.castAdd no.slots)
  have dn (i : Fin no.slots) : M.publicData ((pub ∘ Fin.natAdd yes.slots) i)=no.publicData i := by
    change M.publicData (pub (Fin.natAdd yes.slots i))=no.publicData i
    simpa only [ifValue,Fin.addCases_right,Function.comp_apply] using table (Fin.natAdd yes.slots i)
  obtain ⟨d,guardRun,branch⟩ := run_guard f M G T _ _ hr c m entry
  have routed : ∃ t≤cost m, ∃ o m', advance M.program t d m=some (o,m') ∧ o.pc=exit ∧ post m m' := by
    by_cases h : ifWord f m=0
    · exact onNo m hm h M N _ _ exit hn dn d m (by simpa [h] using branch) rfl
    · exact onYes m hm h M Y _ _ exit hy dy d m (by simpa [h] using branch) rfl
  obtain ⟨t,ht,o,m',steps,endAt,hpost⟩ := routed
  exact ⟨_,(Nat.add_le_add_left ht _).trans (bound m hm),o,m',advance_trans guardRun steps,endAt,hpost⟩

end ThreeFlat.RAM.PhysicalProcedure

end OAI
