import OAI.Computability.BorderVNP.CubeISAOwnedVertexPrepare
import OAI.Computability.BorderVNP.CubeISASelectorRead

/-! # Validating and emitting one team-owned packet's vertex references

The callback reads the selected term from the packet bank, inserts the
group bit in every local vertex rank, writes three-word references, and
advances the output cursor by the exact number of words written.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedVertex

open Cube Cube.Physical Cube.Physical.VertexIndex VPVNP.BurstRAM

/-- Copy the persistent group, coordinate, dimension and output cursor to
the scratch inputs of the half-cube writer. -/
def moveShape : Code := .block [.copy 39 3,.copy 40 4,.copy 48 5,.copy 47 7]

/-- Advance the directory cursor by three words for each vertex just written. -/
def advanceDirectory : Code := .block [
  .constant 50 3, .binary .mul 50 50 46, .binary .add 7 7 50]

/-- Prepare and write the half-cube once its selector has passed validation. -/
def emitDecoded : Code := .seq moveShape (.seq prepareShape (.seq pass advanceDirectory))

/-- Full native callback for an owned packet, beginning with its actual bit prefix. -/
def emitPacket : Code := .seq SelectorRead.reader emitDecoded

/-- Tick allowance including selector validation, shape, all three stores per
vertex, and the final cursor advance. -/
def emitPacketCost (n width : ℕ) : ℕ :=
  SelectorRead.init.slots+width*(SelectorRead.step.slots+1)+1+(requireLt 43 42).slots +
    (4+(shapeSetup.slots+n*(shapeBody.slots+1)+1+(15*2^n+5+3)))

variable {w n d blocks : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem advance_run (s : Bank w) (m : Memory w) {out count : ℕ}
    (cursor : readings s 7 = out) (len : readings s 46 = count) (small : 3 < 2^w)
    (fit : out+3*count < 2^w) :
    BoundedRun pub macros advanceDirectory s m 3 (fun z => z.reg 7 = out+3*count ∧ z.mem = readings m) := by
  have prod : 3*count < 2^w := by omega
  have safe : advanceDirectory.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [advanceDirectory,Code.block,Code.fixedSafe,Code.safeReadOnly,
      Code.fixedEval,Code.evalNat,addressOp,addressOpFits,NatState.ofWords,small,len,cursor,prod,fit]
  apply (advanceDirectory.runFixed pub macros s m safe).mono (by decide)
  intro z hz
  subst z
  simp (config := {decide := true}) [advanceDirectory,Code.block,Code.fixedEval,Code.evalNat,addressOp,
    NatState.ofWords,len,cursor]

private theorem decoded_run (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool)
    (s : Bank w) (m : Memory w) {bank out sel : ℕ}
    (upper : readings s 15 = (p.1.1 i).val.2.val) (ori : readings s 25 = p.1.2.toNat)
    (group : readings s 3 = (groupSymbol p i high).val) (coord : readings s 4 = i.val)
    (dim : readings s 5 = n) (base : readings s 24 = bank) (cursor : readings s 7 = out)
    (term : readings s 43 = sel) (fit : out+3*2^n < 2^w)
    (indices : 2^(n+1) ≤ 2^w) (small : 3 < 2^w) :
    BoundedRun pub macros emitDecoded s m
      (4+(shapeSetup.slots+n*(shapeBody.slots+1)+1+(15*2^n+5+3))) fun z =>
      z.reg 7 = out+3*2^n ∧
      z.mem = image out bank sel (2^i.val) (ownerBit i p.1.2 high).toNat (readings m) (2^n) := by
  have safe : moveShape.fixedSafe w (readings pub) (.ofWords s m) := by simp [moveShape,Code.block,Code.fixedSafe,Code.safeReadOnly]
  apply (moveShape.runFixed pub macros s m safe).seq
  intro u mu hu
  have hl (r : Reg) (hr : r.val < 39) : readings u r = readings s r := by
    exact (congrArg (fun z : NatState => z.reg r) hu).trans
      (moveShape.fixedEval_protected _ _ (by decide) _ hr)
  have data : readings u 39 = readings s 3 ∧ readings u 40 = readings s 4 ∧
      readings u 48 = readings s 5 ∧ readings u 47 = readings s 7 ∧
      readings u 43 = readings s 43 ∧ readings mu = readings m := by
    change (NatState.ofWords u mu).reg 39 = _ ∧ (NatState.ofWords u mu).reg 40 = _ ∧
      (NatState.ofWords u mu).reg 48 = _ ∧ (NatState.ofWords u mu).reg 47 = _ ∧
      (NatState.ofWords u mu).reg 43 = _ ∧ (NatState.ofWords u mu).mem = _
    rw [hu]
    simp (config := {decide := true}) [moveShape,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords]
  obtain ⟨g,c,e,o,tr,mem⟩ := data
  have cap : 2^n < 2^w := by omega
  have shape := prepareShape_run pub macros p i high u mu ((hl 15 (by decide)).trans upper)
    ((hl 25 (by decide)).trans ori) (g.trans group) (c.trans coord) (e.trans dim) cap (by omega)
  apply shape.seq
  rintro v mv ⟨scale,digit,count,hm,keep,output⟩
  have bank' : (v 24).val = bank := (keep 24 (by decide)).trans ((hl 24 (by decide)).trans base)
  have sel' : (v 43).val = sel := (keep 43 (by decide)).trans (tr.trans term)
  have out' : (v 47).val = out := output.trans (o.trans cursor)
  change readings mv = readings mu at hm
  have run := pass_run pub macros i (ownerBit i p.1.2 high) v mv scale digit count
    (by rw [out']; exact fit.le) indices small
  apply run.seq
  rintro t mt ⟨img,low⟩
  have pointer := (low 7 (by decide)).trans ((keep 7 (by decide)).trans ((hl 7 (by decide)).trans cursor))
  have length := (low 46 (by decide)).trans count
  apply (advance_run t mt pointer length small fit).mono le_rfl
  intro z hz
  rw [bank',sel',out',hm,mem] at img
  exact ⟨hz.1,hz.2.trans img⟩

/-- A genuine returning packet callback exists precisely for a valid selector
prefix. Its memory image records that exact selected term and every vertex
of the incident group, and its output cursor advances by `3 * 2^n`. -/
theorem emitPacket_run (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool)
    (s : Bank w) (m : Memory w) {bank out width count : ℕ}
    (upper : readings s 15 = (p.1.1 i).val.2.val) (ori : readings s 25 = p.1.2.toNat)
    (group : readings s 3 = (groupSymbol p i high).val) (coord : readings s 4 = i.val)
    (dim : readings s 5 = n) (base : readings s 24 = bank) (cursor : readings s 7 = out)
    (bits : readings s 41 = width) (choices : readings s 42 = count)
    (word : width ≤ w) (input : bank+width ≤ 2^w) (fit : out+3*2^n < 2^w)
    (indices : 2^(n+1) ≤ 2^w) (small : 3 < 2^w) :
    TestRun pub macros emitPacket s m (emitPacketCost n width)
      (SelectorRead.Valid (readings m) bank width count) fun z =>
        z.reg 7 = out+3*2^n ∧
        z.mem = image out bank (SelectorRead.decoded (readings m) bank width).val
          (2^i.val) (ownerBit i p.1.2 high).toNat (readings m) (2^n) ∧
        (∀ j : Reg, j.val < 24 → j ≠ 7 → z.reg j = readings s j) ∧
        z.reg 41 = width ∧ z.reg 42 = count := by
  let sel := (SelectorRead.decoded (readings m) bank width).val
  let Q (z : NatState) := z.reg 7 = out+3*2^n ∧ z.mem =
    image out bank sel (2^i.val) (ownerBit i p.1.2 high).toNat (readings m) (2^n)
  have r := SelectorRead.reader_run (pub := pub) (mac := macros) s m bank width count base bits choices
    (by omega) word input
  have tail u mu (h : (NatState.ofWords u mu).mem = readings m ∧ readings u 43 = sel ∧
      ∀ j, ¬ SelectorRead.Scratch j → readings u j = readings s j) :
      TestRun pub macros emitDecoded u mu
        (4+(shapeSetup.slots+n*(shapeBody.slots+1)+1+(15*2^n+5+3))) True Q := by
    obtain ⟨mem,rank,keep⟩ := h
    apply ((decoded_run p i high u mu ((keep 15 (by unfold SelectorRead.Scratch; decide)).trans upper)
      ((keep 25 (by unfold SelectorRead.Scratch; decide)).trans ori) ((keep 3 (by unfold SelectorRead.Scratch; decide)).trans group)
      ((keep 4 (by unfold SelectorRead.Scratch; decide)).trans coord) ((keep 5 (by unfold SelectorRead.Scratch; decide)).trans dim)
      ((keep 24 (by unfold SelectorRead.Scratch; decide)).trans base) ((keep 7 (by unfold SelectorRead.Scratch; decide)).trans cursor)
      rank fit indices small).mono le_rfl ?_).asTest (by decide)
    rintro z ⟨hz,himg⟩
    exact ⟨hz,himg.trans (congrArg (fun mm => image out bank sel (2^i.val)
      (ownerBit i p.1.2 high).toNat mm (2^n)) mem)⟩
  have checked := (r.seq tail).mono (Nat.le_refl _)
    (show SelectorRead.Valid (readings m) bank width count ∧ True ↔ SelectorRead.Valid (readings m) bank width count by simp)
    (fun _ (hq : Q _) => hq)
  have preserved : ∀ j : Reg, (j.val < 24 ∧ j ≠ 7 ∨ j = 41 ∨ j = 42) →
      emitPacket.keeps j = true := by decide
  have post {es t mt} (run : Runs pub macros emitPacket s m es t mt) (hq : Q (.ofWords t mt)) :=
    And.intro hq.1 (And.intro hq.2 (And.intro (fun j hj hne =>
      congrArg Fin.val (run.keepsReg (preserved j (.inl ⟨hj,hne⟩)))) (And.intro
      ((congrArg Fin.val (run.keepsReg (preserved 41 (.inr (.inl rfl))))).trans bits)
      ((congrArg Fin.val (run.keepsReg (preserved 42 (.inr (.inr rfl))))).trans choices))))
  constructor
  · intro valid
    obtain ⟨es,t,mt,run,cap,hq⟩ := checked.complete valid
    exact ⟨es,t,mt,run,cap,post run hq⟩
  · intro es t mt run
    obtain ⟨valid,hq⟩ := checked.sound run
    exact ⟨valid,post run hq⟩

end RoutingISA.OwnedVertex

end BorderVNP
end Computability
end OAI
