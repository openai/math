import OAI.ThreeFlat.RAM.TickGreedySweepModel
import OAI.ThreeFlat.RAM.TickGreedyRowValue

namespace OAI
/-! # A fixed-ROM sweep publishing every greedy group and slot -/

namespace ThreeFlat.RAM.TickGreedySweep

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink Fin.CommRing TickGreedyRow

variable {w p r k : ℕ}

def itemPC (pc : Fin 30 ↪ Fin p) : Fin 29 ↪ Fin p := (Fin.castAddEmb 1).trans pc
def itemReg (reg : Fin 17 ↪ Fin r) : Fin 16 ↪ Fin r := (Fin.castAddEmb 1).trans reg
def guard (pc : Fin 30 ↪ Fin p) := pc (Fin.natAdd 29 (0 : Fin 1))

/-- Register 16 is the exclusive input end. The other registers have the ABI of the row kernel. -/
def block (w : ℕ) : Block w 30 17 0 where
  first := Fin.natAdd 29 (0 : Fin 1)
  emit pc reg _ exit i := Fin.addCases (m := 29) (n := 1) (motive := fun _ => Instr w _ _ _)
    (rows (itemPC pc) (itemReg reg) (guard pc))
    (fun _ : Fin 1 => .jumpLt (itemReg reg 0) (reg 16) (itemPC pc 0) exit) i

theorem block_installed (M : Machine w p r k) (pc : Fin 30 ↪ Fin p) (reg : Fin 17 ↪ Fin r)
    (pub : Fin 0 → Fin k) (exit : Fin p) (h : (block w).Installed M pc reg pub exit) :
    Installed M (itemPC pc) (itemReg reg) (guard pc) ∧
      M.code (guard pc) = .jumpLt (itemReg reg 0) (reg 16) (itemPC pc 0) exit := by
  constructor
  · intro i
    change M.code (pc (i.castAdd 1)) = rows (itemPC pc) (itemReg reg) (guard pc) i
    simpa only [block,Fin.addCases_left] using h (i.castAdd 1)
  · simpa only [block,guard,Fin.addCases_right] using h (Fin.natAdd 29 (0 : Fin 1))

def params (R : Fin 16 ↪ Fin r) (c : Config w p r) : Params w :=
  ⟨c.reg (R 6),c.reg (R 7),c.reg (R 8),c.reg (R 9),c.reg (R 10)⟩

theorem next_eq (R : Fin 16 ↪ Fin r) (c : Config w p r) (m : Memory w) :
    next R c m = (params R c).step (state R c) (m (c.reg (R 0)).val,m (c.reg (R 0)+1).val) := rfl

/-- The registers outside the row kernel's destinations, the persistent word and private memory. -/
structure Frame (R : Fin 16 ↪ Fin r) (c d : Config w p r) : Prop where
  registers : ∀ i, (∀ j : Fin 16, (j.val ≤ 5 ∨ 11 ≤ j.val) → i ≠ R j) → d.reg i = c.reg i
  persistent : d.persistent = c.persistent
  privateMem : d.privateMem = c.privateMem

theorem Frame.trans {R : Fin 16 ↪ Fin r} {a b c : Config w p r}
    (ab : Frame R a b) (bc : Frame R b c) : Frame R a c :=
  ⟨fun i hi => (bc.registers i hi).trans (ab.registers i hi),
    bc.persistent.trans ab.persistent,bc.privateMem.trans ab.privateMem⟩

theorem Frame.params {R : Fin 16 ↪ Fin r} {c d : Config w p r} (h : Frame R c d) :
    params R d = params R c := by
  have keep (j : Fin 16) (hj : 5 < j.val ∧ j.val < 11) : d.reg (R j) = c.reg (R j) :=
    h.registers _ (fun i hi => R.injective.ne (by intro he; subst i; omega))
  unfold TickGreedySweep.params
  rw [keep 6 (by decide),keep 7 (by decide),keep 8 (by decide),keep 9 (by decide),keep 10 (by decide)]

theorem Frame.endReg {reg : Fin 17 ↪ Fin r} {c d : Config w p r} (h : Frame (itemReg reg) c d) :
    d.reg (reg 16) = c.reg (reg 16) := by
  apply h.registers
  intro j _ eqn
  have hj := congrArg Fin.val (reg.injective eqn)
  change 16 = j.val at hj
  have := j.isLt
  omega

/-- The actual 30-label machine runs one comparison per item and once on the
empty suffix. Its result memory is the explicit sequence of pair writes.
A destination no later than the source allows in-place operation. -/
theorem advance_sweep (M : Machine w p r k) (pc : Fin 30 ↪ Fin p) (reg : Fin 17 ↪ Fin r)
    (pub : Fin 0 → Fin k) (exit : Fin p) (rom : (block w).Installed M pc reg pub exit)
    (items : List (Pair w)) (P : Params w) (s : State w) (src dst : ℕ)
    (srcRoom : src+2*items.length < 2^w) (dstRoom : dst+2*items.length < 2^w)
    (safe : dst ≤ src ∨ src+2*items.length ≤ dst) (c : Config w p r) (m : Memory w)
    (hc : c.pc = guard pc) (stored : Stores m src items)
    (source : c.reg (itemReg reg 0) = (src : Word w))
    (target : c.reg (itemReg reg 1) = (dst : Word w))
    (endReg : c.reg (reg 16) = ((src+2*items.length : ℕ) : Word w))
    (constant : params (itemReg reg) c = P) (initial : state (itemReg reg) c = s) :
    ∃ out, advance M.program (1+24*items.length) c m =
      some (out,putPairs m dst (replay P s items).2) ∧ out.pc = exit ∧
      state (itemReg reg) out = (replay P s items).1 ∧
      out.reg (itemReg reg 0) = ((src+2*items.length : ℕ) : Word w) ∧
      out.reg (itemReg reg 1) = ((dst+2*items.length : ℕ) : Word w) ∧ Frame (itemReg reg) c out := by
  obtain ⟨kernel,test⟩ := block_installed M pc reg pub exit rom
  induction items generalizing src dst s c m with
  | nil =>
    have eq : c.reg (itemReg reg 0) = c.reg (reg 16) := by simp [source,endReg]
    refine ⟨{c with pc := exit},?_,rfl,initial,?_,?_,⟨fun _ _ => rfl,rfl,rfl⟩⟩
    · simp [advance,Machine.program,hc,test,Instr.run,eq,replay,putPairs]
    · simpa using source
    · simpa using target
  | cons item items ih =>
    simp only [List.length_cons,Nat.mul_succ] at srcRoom dstRoom safe endReg
    obtain ⟨v₀,v₁,tail⟩ := stored
    let R := itemReg reg
    let enter : Config w p r := {c with pc := itemPC pc 0}
    let d := outputConfig (itemPC pc) R (guard pc) enter m
    let chosen := P.step s item
    have live : c.reg (itemReg reg 0) < c.reg (reg 16) := by
      rw [source,endReg,Fin.lt_def,Fin.val_cast_of_lt (by omega),Fin.val_cast_of_lt srcRoom]
      omega
    have check : advance M.program 1 c m = some (enter,m) := by
      simp [advance,Machine.program,hc,test,Instr.run,live,enter]
    have answer : next R enter m = chosen := by
      change next (itemReg reg) c m = P.step s item
      rw [next_eq,constant,initial,source,Fin.val_cast_of_lt (by omega : src < 2^w),
        show (src : Word w)+1 = ((src+1 : ℕ) : Word w) by simp,
        Fin.val_cast_of_lt (by omega : src+1 < 2^w),v₀,v₁]
    have rowRun := advance_row M (itemPC pc) R (guard pc) kernel enter m rfl
    change advance M.program 23 enter m = some (d,writePair m (c.reg (itemReg reg 1))
      (next R enter m).group (next R enter m).slot) at rowRun
    rw [answer,target,writePair_eq m dst (by omega) (chosen.group,chosen.slot)] at rowRun
    have res : RowResult R (guard pc) enter d m := output_result ..
    have fr : Frame (itemReg reg) c d := ⟨res.registers,res.persistent,res.privateMem⟩
    have source' : d.reg (itemReg reg 0) = ((src+2 : ℕ) : Word w) := by
      change d.reg (R 0) = _
      rw [res.source,show enter.reg (R 0) = (src : Word w) from source,Nat.cast_add]
      ring
    have target' : d.reg (itemReg reg 1) = ((dst+2 : ℕ) : Word w) := by
      change d.reg (R 1) = _
      rw [res.target,show enter.reg (R 1) = (dst : Word w) from target,Nat.cast_add]
      ring
    let m' := putPair m dst (chosen.group,chosen.slot)
    have tail' : Stores m' (src+2) items := stores_congr (src+2) items tail (fun x h₁ h₂ => by
      simp [m',putPair,show x ≠ dst+1 by omega,show x ≠ dst by omega])
    obtain ⟨out,run,done,last,os,ot,frame⟩ := ih chosen (src+2) (dst+2) (by omega) (by omega)
      (by omega) d m' res.pc tail' source' target'
      (by rw [fr.endReg,endReg]; congr 1; omega) (fr.params.trans constant) (res.result.trans answer)
    refine ⟨out,?_,done,last,?_,?_,fr.trans frame⟩
    · rw [show 1+24*(item::items).length = (1+23)+(1+24*items.length) by simp only [List.length_cons,Nat.mul_succ]; omega]
      exact advance_trans (advance_trans check rowRun) run
    · rw [show src+2*(item::items).length = src+2+2*items.length by
        simp only [List.length_cons,Nat.mul_succ]; omega]
      exact os
    · rw [show dst+2*(item::items).length = dst+2+2*items.length by
        simp only [List.length_cons,Nat.mul_succ]; omega]
      exact ot

end ThreeFlat.RAM.TickGreedySweep

end OAI
