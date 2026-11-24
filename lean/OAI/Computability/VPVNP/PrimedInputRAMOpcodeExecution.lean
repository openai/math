import OAI.Computability.VPVNP.PrimedInputRAMOpcodeDispatch
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeAct
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeLoad
import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete

/-!
# Native data calls for the primed input passes

Each call reads the three cut lengths, decodes the persistent cursor and computes the
source and owner with private word operations. Only the final action may consume a
branch bit. Its external writes and payload read are the operations of the public
schedule. The three preceding external reads leave the memory unchanged.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Opcodes

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- The first pass uses only the owner bit; the second pass uses the copy source. -/
def rawItem (first : Bool) (d : RawCopy × Bool) (dest : Word w) : Item w :=
  if first then if d.2 then .choose dest else .skip
  else .copy (Layout.compileCopy (encodeBit w) d.1) dest

/-- The skip opcode is a register reset after the two tests. Every other action executes
the same two tests followed by the public item's data events. -/
def actEvents (op : Item w) (m : Memory w) (b : Bool) : List (Event w) :=
  let ticks := match op with | .skip => 3 | _ => 2
  List.replicate ticks .tick ++ (op.report (encodeBit w) 0 m b).events

private theorem act_raw (pub : Pub → Word w) (state : Word w) (before rs : Regs w 48)
    (m : Memory w) (first : Bool) (d : RawCopy × Bool) (dest next : Word w) (b : Bool)
    (hw : 0 < w) (hz : before 0 = 0) (ho : before 1 = 1)
    (hphase : (before 4 < before 5) ↔ first = true)
    (hdest : before 30 = dest) (hnext : before 29 = next) (h : DispatchOutput before rs d) :
    ∃ final, Flow.Exec pub state act rs m (actEvents (rawItem first d dest) m b) final
        ((rawItem first d dest).memory (encodeBit w) m b) ∧ final 29 = next := by
  have eqReg (i : Reg) (hi : i.val < 32) (h25 : i ≠ 25) (h26 : i ≠ 26) (h27 : i ≠ 27) (h28 : i ≠ 28) :
      rs i = before i := (h i hi h25).trans (fieldResult_other before d i h26 h27 h28)
  have h0 := (eqReg 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hz
  have h1 := (eqReg 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ho
  have h4 := eqReg 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 := eqReg 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h29 := (eqReg 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnext
  have h30 := (eqReg 30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdest
  have howner := (h 28 (by decide) (by decide)).trans (fieldResult_owner before d)
  have hfetch := (h 27 (by decide) (by decide)).trans (fieldResult_fetch before d)
  have hval := (h 26 (by decide) (by decide)).trans (fieldResult_payload before d)
  rw [← h4, ← h5] at hphase
  rcases d with ⟨src, own⟩
  cases first with
  | true =>
    have hf := hphase.mpr rfl
    cases own with
    | true =>
      have hs : rs 28 = rs 1 := howner.trans h1.symm
      refine ⟨rs, ?_, h29⟩
      simpa [actEvents, rawItem, Item.report, cellReport, Item.memory, h0, h1, h30, encodeBit]
        using act_choose pub state rs m hf hs b
    | false =>
      have hs : rs 28 ≠ rs 1 := by
        rw [howner, h1]; exact fun e ↦ Bool.false_ne_true ((encodeBit_eq_one hw false).mp e)
      exact ⟨_, act_skip pub state rs m hf hs, h29⟩
  | false =>
    have hf : ¬rs 4 < rs 5 := fun e ↦ Bool.false_ne_true (hphase.mp e)
    cases src with
    | literal v =>
      have hl : rs 27 ≠ rs 1 := by
        rw [hfetch, h1]; exact fun e ↦ Bool.false_ne_true ((encodeBit_eq_one hw false).mp e)
      refine ⟨rs, ?_, h29⟩
      simpa [actEvents, rawItem, Layout.compileCopy, Item.report, copyReport, Item.memory,
        CopySource.get, h30, hval] using act_literal pub state rs m hf hl
    | fetch a =>
      have hl : rs 27 = rs 1 := hfetch.trans h1.symm
      refine ⟨Function.update rs (26 : Reg) (m (rs 26).val), ?_, h29⟩
      simpa [actEvents, rawItem, Layout.compileCopy, Item.report, copyReport, Item.memory,
        CopySource.get, h30, hval] using act_fetch pub state rs m hf hl

/-- The reported events record all 28 parameter/coordinate instructions, every private
dispatch tick, and the final choice or copy. -/
def dataEvents (m : Memory w) (cost : ℕ) (op : Item w) (b : Bool) : List (Event w) :=
  (parameterEvents w m ++ List.replicate 7 .tick) ++ List.replicate cost .tick ++ actEvents op m b

private theorem choices_ticks (n : ℕ) : choiceBits (List.replicate n (.tick : Event w)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, choiceBits, ih]

private theorem probes_ticks (n : ℕ) : countProbes (List.replicate n (.tick : Event w)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, countProbes, ih]

private theorem probes_append (es fs : List (Event w)) :
    countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

@[simp] theorem dataEvents_choices (m : Memory w) (cost : ℕ) (op : Item w) (b : Bool) :
    choiceBits (dataEvents m cost op b) = op.bits b := by
  simp only [dataEvents, Flow.choiceBits_append, choices_ticks, List.append_nil]
  change [] ++ choiceBits (actEvents op m b) = _
  cases op with
  | skip | choose => rfl
  | copy src dst => cases src <;> rfl

@[simp] theorem dataEvents_probes (m : Memory w) (cost : ℕ) (op : Item w) (b : Bool) :
    countProbes (dataEvents m cost op b) = 3 + op.probeCount := by
  simp only [dataEvents, probes_append, probes_ticks, Nat.add_zero]
  change 3 + countProbes (actEvents op m b) = _
  cases op with
  | skip | choose => rfl
  | copy src dst => cases src <;> rfl

private theorem after_ticks (m : Memory w) (n : ℕ) : after m (List.replicate n .tick) = m := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, after, update] using ih

@[simp] theorem dataEvents_memory (m : Memory w) (cost : ℕ) (op : Item w) (b : Bool) :
    after m (dataEvents m cost op b) = op.memory (encodeBit w) m b := by
  have ap (a : Memory w) (es fs : List (Event w)) : after a (es ++ fs) = after (after a es) fs := by
    simp [after]
  simp only [dataEvents, ap, after_ticks]
  change after m (actEvents op m b) = _
  cases op with
  | skip | choose => rfl
  | copy src dst => cases src <;> rfl

theorem dataEvents_length (m : Memory w) (cost : ℕ) (op : Item w) (b : Bool) :
    (dataEvents m cost op b).length ≤ cost + 32 := by
  simp only [dataEvents, List.length_append, List.length_replicate]
  change 21 + 7 + cost + (actEvents op m b).length ≤ _
  have ha : (actEvents op m b).length ≤ 4 := by
    cases op with
    | skip | choose => simp [actEvents, Item.report, cellReport]
    | copy src dst => cases src <;> simp [actEvents, Item.report, copyReport]
  omega

/-- A complete opcode derivation from a decoded dispatch ABI. The dispatch computation
uses no binary choice, so its tick count can be chosen before the private branch bit. -/
theorem dataCall_exec {L : Lengths} {n r H base P g v j : ℕ} {prefixAt : ℕ → Bool}
    (pub : Pub → Word w) (state : Word w) (rs pre : Regs w 48) (m : Memory w)
    (first : Bool) (dest next : Word w) (hw : 0 < w)
    (hpre : Flow.Exec pub state (.seq loadParameters unpackCursor) rs m
      (parameterEvents w m ++ List.replicate 7 .tick) pre m)
    (I : DispatchInput L n r H w base P g v j prefixAt pub pre)
    (hphase : pre 4 < pre 5 ↔ first = true) (hdest : pre 30 = dest) (hnext : pre 29 = next) :
    let d := (dispatchRow L n r H w base P prefixAt g v j).1
    let op := rawItem first d dest
    ∃ cost ≤ 3*r+128, ∀ b, ∃ final, Flow.Exec pub state (dataCall PortCode.program) rs m
      (dataEvents m cost op b) final (op.memory (encodeBit w) m b) ∧ final 29 = next := by
  dsimp only
  obtain ⟨cost,out,hr,hc,ho⟩ := dispatch_exec pub state pre m I
  refine ⟨cost,hc,fun b ↦ ?_⟩
  have hz : pre 0 = 0 := Fin.ext I.header.zero
  have hone : pre 1 = 1 := by
    apply Fin.ext
    simpa [Fin.val_one, Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')] using I.header.one
  obtain ⟨final,ha,hn⟩ := act_raw pub state pre out m first _ dest next b hw hz hone hphase hdest hnext ho
  exact ⟨final, (hpre.seq hr).seq ha, hn⟩

end PrimedInputRAM.Opcodes

end VPVNP
end Computability
end OAI
