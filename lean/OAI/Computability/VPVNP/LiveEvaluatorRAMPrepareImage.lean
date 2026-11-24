import OAI.Computability.VPVNP.LiveEvaluatorAction
import OAI.Computability.VPVNP.LiveEvaluatorRAMScratchImage
import OAI.Computability.VPVNP.LiveEvaluatorRAMSchedule

/-!
# The scheduled preparing call on configuration images

The first call reads the old state and the two head symbols and consults the
fixed evaluator's row. The selected five words must match the proposed state
and are published to disjoint scratch memory. The choice stream distinguishes
the slots even if they specify identical instructions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM

open BurstRAM (Word Memory choiceBits)
open PrimedStackRAM (Regs)
open PrimedInputRAM (Flow)
open UniversalMachine (Program Instruction chosenInstruction windowCenter)
open LiveEvaluatorEncoding (ConfigWindow)
open LiveEvaluatorRAMPrepare
open LiveEvaluatorRAMDispatch (ticks dispatchBits instructionRegs_fields)
open scoped Fin.CommRing

variable {w M : ℕ}

/-- The allocation supplies enough bits for every program row, both
configurations, and the separate five-word scratch area. -/
structure PrepLayout (p : Program) (pub : Fin 4 → Word w) (M : ℕ) : Prop where
  width : 2 ≤ w
  states : p.extra + 2 ≤ 2 ^ w
  rows : 9 * p.extra ≤ 2 ^ w
  radius : (pub 0).val = M
  oldFit : (pub 1).val + Schedule.calls M ≤ 2 ^ w
  outFit : (pub 2).val + Schedule.calls M ≤ 2 ^ w
  scratchFit : (pub 3).val + 5 ≤ 2 ^ w
  oldDisjoint : (pub 1).val + Schedule.calls M ≤ (pub 3).val ∨ (pub 3).val + 5 ≤ (pub 1).val
  outDisjoint : (pub 2).val + Schedule.calls M ≤ (pub 3).val ∨ (pub 3).val + 5 ≤ (pub 2).val

/-- A native run from cursor zero, indexed by its final memory and consumed bits. -/
def Prepared (p : Program) (pub : Fin 4 → Word w) (m mem : Memory w) (bs : List Bool) : Prop :=
  ∃ es rs, Flow.Exec pub 0 (Schedule.body (prepare p)) (fun _ => 0) m es rs mem ∧ choiceBits es = bs

private abbrev entryRegs (pub : Fin 4 → Word w) (m : Memory w) : Regs w 32 :=
  Schedule.loaded pub 0 (fun _ => 0) m

private abbrev selectRegs (p : Program) (pub : Fin 4 → Word w) (m : Memory w) : Regs w 32 :=
  boundsRegs p (entryRegs pub m)

private def recordRegs (p : Program) (pub : Fin 4 → Word w) (m : Memory w)
    (old : LiveEvaluatorEncoding.Code p.extra M) (a : Instruction p.extra) : Regs w 32 :=
  match old with
  | .accepted => carryRegs (selectRegs p pub m)
  | _ => selectedRegs (selectRegs p pub m) m a

/-- Memory obtained by publishing the selected record of this source. -/
def preparedMemory (p : Program) (pub : Fin 4 → Word w) (m : Memory w)
    (old : LiveEvaluatorEncoding.Code p.extra M) (a : Instruction p.extra) : Memory w :=
  scratchMemory (recordRegs p pub m old a) m

private theorem numeral_val {n : ℕ} (h : n < 2 ^ w) : (n : Word w).val = n :=
  Nat.mod_eq_of_lt h

private theorem head_values {p : Program} {pub : Fin 4 → Word w} {m : Memory w}
    {old : LiveEvaluatorEncoding.Code p.extra M} (hl : PrepLayout p pub M)
    (ho : ConfigAt m (pub 1) old) :
    (firstHead (selectRegs p pub m) m).val = (old.firstCell (windowCenter M)).val ∧
      (secondHead (selectRegs p pub m) m).val = (old.secondCell (windowCenter M)).val := by
  have hr : pub 0 = (M : Word w) := by rw [← hl.radius, Fin.cast_val_eq_self]
  have hlen : pub 0 + pub 0 + 1 = ((2*M+1 : ℕ) : Word w) := by
    rw [hr]
    push_cast
    ring
  change (m (pub 1 + 1 + pub 0).val).val = _ ∧
    (m (pub 1 + 1 + pub 0 + (pub 0 + pub 0 + 1)).val).val = _
  rw [hlen, hr, add_right_comm (pub 1 + 1) (M : Word w)]
  exact ⟨ho.first (windowCenter M), ho.second (windowCenter M)⟩

private theorem tableRow_eq {p : Program} {pub : Fin 4 → Word w} {m : Memory w}
    {c : ConfigWindow p.extra M} {hc : 2 ≤ c.state.val} (hl : PrepLayout p pub M)
    (ho : ConfigAt m (pub 1) (.running c hc)) :
    tableRow p (selectRegs p pub m) m = LiveEvaluatorStep.row p c := by
  let rs := selectRegs p pub m
  have h4 : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) hl.width
  have h2 : (rs 2).val = 2 := numeral_val (n := 2) (by omega)
  have h3 : (rs 3).val = 3 := numeral_val (n := 3) (by omega)
  have hstate : (rs 16).val = c.state.val := ho.state
  have ⟨hf, hs⟩ := head_values hl ho
  change (firstHead rs m).val = (c.firstTape.cells (windowCenter M)).val at hf
  change (secondHead rs m).val = (c.secondTape.cells (windowCenter M)).val at hs
  have hfit : ((rs 16).val - 2) * 9 + (firstHead rs m).val * 3 + (secondHead rs m).val < 2^w := by
    rw [hstate, hf, hs]
    have := c.state.isLt
    have := (c.firstTape.cells (windowCenter M)).isLt
    have := (c.secondTape.cells (windowCenter M)).isLt
    have := hl.rows
    omega
  change p.rows[(rowNumber rs m).val]?.getD .stop = _
  rw [rowNumber_val rs m h2 h3 (hstate ▸ hc) hfit, hstate, hf, hs]
  rfl

private theorem selected_iff {p : Program} {pub : Fin 4 → Word w} {m : Memory w}
    {old : LiveEvaluatorEncoding.Code p.extra M} (hl : PrepLayout p pub M)
    (ho : ConfigAt m (pub 1) old) (hpos : 0 < old.stateWord.val) (s : Regs w 32) (bs : List Bool) :
    (∃ fs, Selected p (selectRegs p pub m) m fs s ∧ choiceBits fs = bs) ↔
      ∃ bit a, LiveEvaluatorAction.pick p old bit = some a ∧ s = recordRegs p pub m old a ∧
        bs = LiveEvaluatorAction.branchBits p old bit := by
  let u := selectRegs p pub m
  have h4 : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) hl.width
  have hu1 : (u 1).val = 1 := numeral_val (n := 1) (by omega)
  have hu3 : (u 3).val = 3 := numeral_val (n := 3) (by omega)
  have hstate : (u 16).val = old.stateWord.val := ho.state
  cases old with
  | rejected => exact (Nat.lt_irrefl 0 hpos).elim
  | accepted =>
    change (u 16).val = 1 at hstate
    have heq : u 16 = u 1 := Fin.ext (hstate.trans hu1.symm)
    have hbits : choiceBits (.tick :: ticks (w := w) 5) = [] := rfl
    constructor
    · rintro ⟨fs, sel, hb⟩
      cases sel with
      | carry => exact ⟨false, LiveEvaluatorAction.carry _, rfl, rfl, hb.symm.trans hbits⟩
      | slot hne => exact (hne heq).elim
    · rintro ⟨bit, a, ha, rfl, rfl⟩
      exact ⟨_, .carry heq, hbits⟩
  | running c hc =>
    change (u 16).val = c.state.val at hstate
    have hne : u 16 ≠ u 1 := by intro he; rw [he, hu1] at hstate; omega
    have hrow := tableRow_eq hl ho
    have ⟨hv₁, hv₂⟩ := head_values hl ho
    have hf : firstHead u m < u 3 := by
      change (firstHead u m).val < (u 3).val
      rw [hu3, hv₁]
      exact (c.firstTape.cells _).isLt
    have hs : secondHead u m < u 3 := by
      change (secondHead u m).val < (u 3).val
      rw [hu3, hv₂]
      exact (c.secondTape.cells _).isLt
    have hbits (bit : Bool) (a : Instruction p.extra) :
        choiceBits (.tick :: (rowTrace u m ++
          LiveEvaluatorRAMDispatch.dispatchEvents (rowNumber u m).val (tableRow p u m) bit a)) =
        LiveEvaluatorAction.branchBits p (.running c hc) bit := by
      rw [LiveEvaluatorAction.branchBits, ← hrow]
      simp [u, choiceBits, rowTrace, LiveEvaluatorRAMDispatch.dispatchEvents_bits]
    constructor
    · rintro ⟨fs, sel, hb⟩
      cases sel with
      | carry heq => exact (hne heq).elim
      | slot _ _ _ bit a ha =>
        exact ⟨bit, a, by simpa only [LiveEvaluatorAction.pick, ← hrow] using ha, rfl,
          hb.symm.trans (hbits bit a)⟩
    · rintro ⟨bit, a, ha, rfl, rfl⟩
      exact ⟨_, .slot hne hf hs bit a (by simpa only [LiveEvaluatorAction.pick, ← hrow] using ha), hbits bit a⟩

private theorem record_fields {p : Program} {pub : Fin 4 → Word w} {m : Memory w}
    {old : LiveEvaluatorEncoding.Code p.extra M} {bit : Bool} {a : Instruction p.extra}
    (hl : PrepLayout p pub M) (ha : LiveEvaluatorAction.pick p old bit = some a) :
    let rs := recordRegs p pub m old a
    (rs 5).val = a.target.val ∧ (rs 6).val = a.firstSymbol.val ∧
      (rs 7).val = a.firstMove.val ∧ (rs 8).val = a.secondSymbol.val ∧
      (rs 9).val = a.secondMove.val := by
  cases old with
  | accepted =>
    cases bit <;> simp [LiveEvaluatorAction.pick] at ha
    subst a
    have h4 : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) hl.width
    exact ⟨numeral_val (n := 1) (by omega), rfl, rfl, rfl, rfl⟩
  | rejected => cases ha
  | running c hc => exact instructionRegs_fields (Function.update (rowRegs (selectRegs p pub m) m) 4 0) a hl.width hl.states

private theorem record_frame {p : Program} {pub : Fin 4 → Word w} {m : Memory w}
    (old : LiveEvaluatorEncoding.Code p.extra M) (a : Instruction p.extra) :
    let rs := recordRegs p pub m old a
    rs 0 = 0 ∧ rs 1 = 1 ∧ rs 24 = pub 2 ∧ rs 25 = pub 3 := by
  cases old <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Execution at cursor zero is equivalent to picking an occupied slot with
a nonrejecting target equal to the proposed state. Both the consumed bits and
the resulting external memory are specified. -/
theorem prepared_iff {p : Program} {pub : Fin 4 → Word w} {m mem : Memory w} {bs : List Bool}
    {old out : LiveEvaluatorEncoding.Code p.extra M} (hl : PrepLayout p pub M)
    (ho : ConfigAt m (pub 1) old) (hz : ConfigAt m (pub 2) out) :
    Prepared p pub m mem bs ↔
      ∃ bit a, LiveEvaluatorAction.pick p old bit = some a ∧ 0 < a.target.val ∧
        a.target = out.stateWord ∧ bs = LiveEvaluatorAction.branchBits p old bit ∧
        mem = preparedMemory p pub m old a := by
  rw [Prepared, Schedule.initial_choices_iff]
  let rs := entryRegs pub m
  have hstate : (rs 16).val = old.stateWord.val := ho.state
  have he := prepare_exec_iff p pub 0 rs m hl.width hl.states rfl rfl
  constructor
  · rintro ⟨es, reg, run, hb⟩
    obtain ⟨hp, -, fs, s, sel, hpt, hout, hes, -, hmem⟩ := (he _ _ _).mp run
    rw [hes, prepareTrace_bits] at hb
    rw [hstate] at hp
    obtain ⟨bit, a, ha, rfl, hbits⟩ := (selected_iff hl ho hp s bs).mp ⟨fs, sel, hb⟩
    obtain ⟨hs0, -, hs24, -⟩ := record_frame (pub := pub) (m := m) old a
    have ht := (record_fields (m := m) hl ha).1
    rw [hs0] at hpt
    rw [hs24] at hout
    exact ⟨bit, a, ha, ht ▸ hpt, Fin.ext (ht.symm.trans ((congrArg Fin.val hout).symm.trans hz.state)),
      hbits, hmem⟩
  · rintro ⟨bit, a, ha, hpt, hout, hb, rfl⟩
    have hp : 0 < old.stateWord.val := by
      cases old with
      | accepted => exact Nat.zero_lt_one
      | rejected => cases ha
      | running c hc => change 0 < c.state.val; omega
    let s := recordRegs p pub m old a
    obtain ⟨fs, sel, hbits⟩ := (selected_iff hl ho hp s bs).mpr ⟨bit, a, ha, rfl, hb⟩
    obtain ⟨hs0, -, hs24, -⟩ := record_frame (pub := pub) (m := m) old a
    have ht := (record_fields (m := m) hl ha).1
    have hlt : s 0 < s 5 := by
      rw [show s 0 = 0 from hs0]
      change 0 < (s 5).val
      rwa [show (s 5).val = _ from ht]
    have hm : m (s 24).val = s 5 := by
      apply Fin.ext
      rw [show s 24 = pub 2 from hs24, hz.state, ← hout]
      exact ht.symm
    have hrange := old.stateWord.isLt
    refine ⟨_, _, (he _ _ _).mpr ⟨hstate ▸ hp, by omega, fs, s, sel, hlt, hm, rfl, rfl, rfl⟩, ?_⟩
    rw [prepareTrace_bits, hbits]

/-- Publication preserves the two configuration images and installs the five
chosen instruction words at the address subsequently used by the cell scans. -/
theorem preparedMemory_images {p : Program} {pub : Fin 4 → Word w} {m : Memory w}
    {old out : LiveEvaluatorEncoding.Code p.extra M} {bit : Bool} {a : Instruction p.extra}
    (hl : PrepLayout p pub M) (ho : ConfigAt m (pub 1) old) (hz : ConfigAt m (pub 2) out)
    (ha : LiveEvaluatorAction.pick p old bit = some a) :
    let mem := preparedMemory p pub m old a
    ConfigAt mem (pub 1) old ∧ ConfigAt mem (pub 2) out ∧
      ActionAt mem (pub 3) a.target.val a.firstSymbol a.firstMove a.secondSymbol a.secondMove := by
  let s := recordRegs p pub m old a
  have h4 : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) hl.width
  obtain ⟨-, h1, -, h25⟩ := record_frame (pub := pub) (m := m) old a
  have hu : (s 1).val = 1 := (congrArg Fin.val h1).trans (numeral_val (n := 1) (by omega))
  have hbase : s 25 = pub 3 := h25
  have hfit : (s 25).val + 5 ≤ 2^w := hbase ▸ hl.scratchFit
  obtain ⟨h5, h6, h7, h8, h9⟩ := record_fields (m := m) hl ha
  refine ⟨ho.after_scratch s hu hfit hl.oldFit (hbase ▸ hl.oldDisjoint),
    hz.after_scratch s hu hfit hl.outFit (hbase ▸ hl.outDisjoint), ?_⟩
  rw [← hbase]
  exact actionAt_scratch hu hfit h5 h6 h7 h8 h9

end LiveEvaluatorRAM

end VPVNP
end Computability
end OAI
