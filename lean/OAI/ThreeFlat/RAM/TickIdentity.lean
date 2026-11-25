import OAI.ThreeFlat.RAM.TickCheckSetup
import OAI.ThreeFlat.RAM.ScanLoop
import OAI.ThreeFlat.RAM.ContinuationLink

namespace OAI
/-! # A complete native identity branch of the physical tick -/

namespace ThreeFlat.RAM.TickIdentity

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped Classical

variable {w p r k : ℕ} {F : Type*} [Semiring F]

/-- The three regions in a single scan use two pointers and one exclusive end. -/
def values (w left right n : ℕ) : Fin 7 → Word w :=
  ![Fin.ofNat _ left,Fin.ofNat _ (left+n),Fin.ofNat _ right,0,0,1,0]

private def inputs (reg : Fin 7 ↪ Fin r) : Fin 6 ↪ Fin r := (Fin.castAddEmb 1).trans reg

/-- A seven-word setup followed by the seven native rows of the compare loop. -/
def compare (w left right n : ℕ) : Block w 14 7 0 where
  first := (0 : Fin 7).castAdd 7
  emit pc reg _ exit := Fin.append
    (TickCheckSetup.emit ((Fin.castAddEmb 7).trans pc) reg (values w left right n)
      (pc (Fin.natAdd 7 (0 : Fin 7))))
    (ScanLoop.block ((Fin.natAddEmb 7 : Fin 7 ↪ Fin 14).trans pc) (inputs reg) exit)

theorem mass_compare (field : FieldCode F w) (M : Machine w p r k) (left right n : ℕ)
    (pc : Fin 14 ↪ Fin p) (reg : Fin 7 ↪ Fin r) (pub : Fin 0 → Fin k) (exit : Fin p)
    (rom : (compare w left right n).Installed M pc reg pub exit) (c : Config w p r) (m : Memory w)
    (entry : c.pc = pc (compare w left right n).first)
    (fitL : left+n < 2^w) (fitR : right+n < 2^w) :
    ∃ d : Config w p r, d.pc = exit ∧ ∀ fuel, mass field M.program (fuel+8+6*n) c m =
      if ScanLoop.agree m left right n then mass field M.program fuel d m else 0 := by
  let P : Fin 7 ↪ Fin p := (Fin.castAddEmb 7).trans pc
  let Q := ((Fin.natAddEmb 7 : Fin 7 ↪ Fin 14).trans pc)
  let V := values w left right n
  have first (i : Fin 7) : M.code (P i) = TickCheckSetup.emit P reg V (Q 0) i := by
    simpa only [P,Q,V,compare,Fin.append_left,Function.Embedding.trans_apply,Fin.castAddEmb_apply,Fin.natAddEmb_apply] using rom (i.castAdd 7)
  have loop (i : Fin 7) : M.code (Q i) = ScanLoop.block Q (inputs reg) exit i := by
    simpa only [P,Q,compare,Fin.append_right,Function.Embedding.trans_apply,Fin.castAddEmb_apply,Fin.natAddEmb_apply] using rom (Fin.natAdd 7 i)
  let b := TickCheckSetup.loaded P reg V (Q 0) c
  have setup := TickCheckSetup.advance_setup M P reg V (Q 0) first c m entry
  have lv : (b.reg (inputs reg 0)).val = left := by
    change ((TickCheckSetup.loaded P reg V (Q 0) c).reg (reg (0 : Fin 7))).val = left
    rw [TickCheckSetup.loaded_reg]
    exact Nat.mod_eq_of_lt (show left < 2^w by omega)
  have limit : (b.reg (inputs reg 1)).val = left+n := by
    change ((TickCheckSetup.loaded P reg V (Q 0) c).reg (reg (1 : Fin 7))).val = left+n
    rw [TickCheckSetup.loaded_reg]
    exact Nat.mod_eq_of_lt fitL
  have rv : (b.reg (inputs reg 2)).val = right := by
    change ((TickCheckSetup.loaded P reg V (Q 0) c).reg (reg (2 : Fin 7))).val = right
    rw [TickCheckSetup.loaded_reg]
    exact Nat.mod_eq_of_lt (show right < 2^w by omega)
  have unit : b.reg (inputs reg 5) = 1 :=
    TickCheckSetup.loaded_reg P reg V (Q 0) c 5
  refine ⟨ScanLoop.endConfig (inputs reg) Q exit m n b,ScanLoop.endConfig_pc ..,?_⟩
  intro fuel
  have cmp := ScanLoop.mass_block field M Q (inputs reg) exit loop n fuel b m rfl
    (by rw [lv,limit]) (by rw [rv]; exact fitR) unit
  rw [lv,rv] at cmp
  rw [show fuel+8+6*n = (fuel+1+6*n)+7 by omega]
  exact (mass_of_advance field M.program setup _).trans cmp

/-- Each of the three comparisons runs on the same external memory. -/
structure Regions where
  oldAux : ℕ
  newAux : ℕ
  zero : ℕ
  oldChunk : ℕ
  newChunk : ℕ

structure Regions.Fits (A : Regions) (w n : ℕ) : Prop where
  oldAux : A.oldAux+n < 2^w
  newAux : A.newAux+n < 2^w
  zero : A.zero+n < 2^w
  oldChunk : A.oldChunk+n < 2^w
  newChunk : A.newChunk+n < 2^w

def block (w n : ℕ) (A : Regions) : Block w 42 7 0 :=
  (compare w A.oldAux A.zero n).seq ((compare w A.newAux A.zero n).seq (compare w A.oldChunk A.newChunk n))

def valid (A : Regions) (m : Memory w) (n : ℕ) : Prop :=
  (∀ i : Fin n, m (A.oldAux+i.val) = 0) ∧ (∀ i : Fin n, m (A.newAux+i.val) = 0) ∧
    ScanLoop.agree m A.oldChunk A.newChunk n

/-- The complete linked branch passes to the caller only if both auxiliary
endpoints vanish and all external chunk bits agree. -/
theorem mass_block (field : FieldCode F w) (M : Machine w p r k) (A : Regions) (n : ℕ)
    (pc : Fin 42 ↪ Fin p) (reg : Fin 7 ↪ Fin r) (pub : Fin 0 → Fin k) (exit : Fin p)
    (rom : (block w n A).Installed M pc reg pub exit) (c : Config w p r) (m : Memory w)
    (entry : c.pc = pc (block w n A).first) (fit : A.Fits w n)
    (zero : ∀ j : Fin n, m (A.zero+j.val) = 0) :
    ∃ d : Config w p r, d.pc = exit ∧ ∀ fuel, mass field M.program (fuel+24+18*n) c m =
      if valid A m n then mass field M.program fuel d m else 0 := by
  obtain ⟨ra,rbc⟩ := (Block.seq_installed ..).mp rom
  obtain ⟨rb,rc⟩ := (Block.seq_installed ..).mp rbc
  obtain ⟨ca,pa,sa⟩ := mass_compare field M _ _ _ _ reg pub _ ra c m entry fit.oldAux fit.zero
  obtain ⟨cb,pb,sb⟩ := mass_compare field M _ _ _ _ reg pub _ rb ca m pa fit.newAux fit.zero
  obtain ⟨cc,pc',sc⟩ := mass_compare field M _ _ _ _ reg pub _ rc cb m pb fit.oldChunk fit.newChunk
  refine ⟨cc,pc',?_⟩
  intro fuel
  have eqz (a : ℕ) : ScanLoop.agree m a A.zero n ↔ ∀ j : Fin n, m (a+j.val) = 0 := by
    simp only [ScanLoop.agree,zero]
  rw [show fuel+24+18*n = ((fuel+8+6*n)+8+6*n)+8+6*n by omega,sa,sb,sc]
  by_cases ha : ScanLoop.agree m A.oldAux A.zero n
  · by_cases hb : ScanLoop.agree m A.newAux A.zero n
    · by_cases hc : ScanLoop.agree m A.oldChunk A.newChunk n
      · have hv : valid A m n := ⟨(eqz _).mp ha,(eqz _).mp hb,hc⟩
        simp only [ite_eq_left ha,ite_eq_left hb,ite_eq_left hc,ite_eq_left hv]
      · have hv : ¬valid A m n := fun h => hc h.2.2
        simp only [ite_eq_left ha,ite_eq_left hb,ite_eq_right hc,ite_eq_right hv]
    · have hv : ¬valid A m n := fun h => hb ((eqz _).mpr h.2.1)
      simp only [ite_eq_left ha,ite_eq_right hb,ite_eq_right hv]
  · have hv : ¬valid A m n := fun h => ha ((eqz _).mpr h.1)
    simp only [ite_eq_right ha,ite_eq_right hv]

private def accept {w : ℕ} (_ : Fin 1 ↪ Fin 43) (_ : Fin 1) : Instr w 43 7 0 := .accept

/-- A closed 43-label native ROM, without public operands. -/
def machine (w n : ℕ) (A : Regions) : Machine w 43 7 0 :=
  close (block w n A) (0 : Fin 1) accept Fin.elim0

/-- From arbitrary incoming registers, one accepting instruction closes the
three physical comparisons. Additional fuel preserves the resulting value. -/
theorem mass_machine (field : FieldCode F w) (A : Regions) (n fuel : ℕ)
    (c : Config w 43 7) (m : Memory w) (entry : c.pc = (machine w n A).entry)
    (fit : A.Fits w n) (zero : ∀ j : Fin n, m (A.zero+j.val) = 0) :
    mass field (machine w n A).program (fuel+25+18*n) c m = if valid A m n then 1 else 0 := by
  have rom := close_installed (block w n A) (0 : Fin 1) accept Fin.elim0
  obtain ⟨d,hd,sem⟩ := mass_block field (machine w n A) A n _ _ _ _ rom c m entry fit zero
  have tail : (machine w n A).code (Fin.natAdd 42 (0 : Fin 1)) = .accept :=
    close_tail (block w n A) (0 : Fin 1) accept Fin.elim0 0
  rw [show fuel+25+18*n = (fuel+1)+24+18*n by omega,sem]
  simp only [mass,Machine.program,hd,tail,Instr.run,FieldCode.terminal]


end ThreeFlat.RAM.TickIdentity

end OAI
