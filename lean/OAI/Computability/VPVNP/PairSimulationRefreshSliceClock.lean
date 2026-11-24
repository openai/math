import OAI.Computability.VPVNP.PairSimulationPrivateSlices
import OAI.Computability.VPVNP.CompressorRecordRefreshReadback

/-!
# Reading and copying external segments at a refreshed port

The refresh directory stores widths and offsets in separate columns. Both local
directions use the same native copy code with their own column bases. Its six setup
instructions address the columns, read the interval and prepare the private copy.
The final loop test is executed even for an empty segment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshSliceClock

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.nil ReadPrefix.tick ReadPrefix.read ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r k : ℕ}

/-- Registers 0–4 use the private-copy ABI. Registers 5–7 hold the segment
ordinal and the two directory column heads. -/
def instruction (pc : Fin 6 → Fin p) (reg : Fin 8 ↪ Fin r) (copy : Fin p) :
    Fin 6 → Instr w p r k :=
  ![.binary .add (reg 4) (reg 6) (reg 5) (pc 1), .readExternal (reg 1) (reg 4) (pc 2),
    .binary .add (reg 4) (reg 7) (reg 5) (pc 3), .readExternal (reg 4) (reg 4) (pc 4),
    .binary .add (reg 0) (reg 0) (reg 4) (pc 5), .binary .add (reg 1) (reg 2) (reg 1) copy]

theorem resize_instruction (pc : Fin 6 → Fin p) (reg : Fin 8 ↪ Fin r) (copy : Fin p) (i : Fin 6) :
    (instruction (w := 1) (k := k) pc reg copy i).resize w = instruction pc reg copy i := by
  fin_cases i <;> rfl

/-- At the six supplied program counters the machine executes the refreshed segment's setup,
reading width and offset from their columns and entering the private copy loop. -/
def Linked (M : Machine w p r k) (pc : Fin 6 → Fin p) (reg : Fin 8 ↪ Fin r) (copy : Fin p) : Prop :=
  ∀ i, M.code (pc i) = instruction pc reg copy i

/-- Restrict the segment setup's eight-register allocation to the first five registers used by
the private copy loop. -/
def copyRegs (reg : Fin 8 ↪ Fin r) : Fin 5 ↪ Fin r := (Fin.castAddEmb 3).trans reg

/-- The six setup events for one refreshed segment, including reads at the width and offset
column heads plus the segment ordinal and the values returned there. -/
def headerEvents (mem : Memory w) (width offset ordinal : Word w) : List (Event w) :=
  [.tick, .read (width + ordinal) (mem (width + ordinal).val),
   .tick, .read (offset + ordinal) (mem (offset + ordinal).val), .tick, .tick]

/-- Trace for one refreshed segment from its two directory reads through the last copy-loop
test. It costs seven events plus five per bit and makes exactly two external probes. -/
def segmentEvents (mem : Memory w) (width offset ordinal : Word w) (bs : List Bool) :
    List (Event w) :=
  headerEvents mem width offset ordinal ++ PrivateFields.events .copy bs

theorem segment_work (mem : Memory w) (width offset ordinal : Word w) (bs : List Bool) :
    (segmentEvents mem width offset ordinal bs).length = 7 + 5 * bs.length ∧
    countProbes (segmentEvents mem width offset ordinal bs) = 2 := by
  have h := PrivateFields.events_work (w := w) .copy bs
  simp [segmentEvents, headerEvents, h.1, h.2, countProbes]
  omega

variable {M : Machine w p r k} {pc : Fin 6 → Fin p} {reg : Fin 8 ↪ Fin r} {copy : Fin p}

private theorem step_at (hl : Linked M pc reg copy) (i : Fin 6) {c : Config w p r}
    (hc : c.pc = pc i) : M.program.step c = (instruction pc reg copy i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

/-- Read the two actual cells and prepare the source, destination and end operands. -/
theorem execute_header (hl : Linked M pc reg copy) (c : Config w p r) (hc : c.pc = pc 0)
    (mem : Memory w) :
    let id := c.reg (reg 5)
    let wid := c.reg (reg 6)
    let off := c.reg (reg 7)
    ∃ d, d.pc = copy ∧ d.reg (reg 0) = c.reg (reg 0) + mem (off + id).val ∧
      d.reg (reg 1) = c.reg (reg 2) + mem (wid + id).val ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 1 → j ≠ reg 4 → d.reg j = c.reg j) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      ∀ fuel bs, execute M.program (fuel + 6) c mem bs =
        (execute M.program fuel d mem bs).map
          (fun rep => ⟨headerEvents mem wid off id ++ rep.events, rep.result⟩) := by
  intro id wid off
  let c₁ := c.put (pc 1) (reg 4) (wid + id)
  let c₂ := c₁.put (pc 2) (reg 1) (mem (wid + id).val)
  let c₃ := c₂.put (pc 3) (reg 4) (off + id)
  let c₄ := c₃.put (pc 4) (reg 4) (mem (off + id).val)
  let c₅ := c₄.put (pc 5) (reg 0) (c.reg (reg 0) + mem (off + id).val)
  let d := c₅.put copy (reg 1) (c.reg (reg 2) + mem (wid + id).val)
  have path : ReadPrefix M mem c (headerEvents mem wid off id) d := by
    refine ReadPrefix.tick (d := c₁) (step_at hl 0 hc)
      (ReadPrefix.read (g := fun v => c₁.put (pc 2) (reg 1) v) _ ?_
      (ReadPrefix.tick (d := c₃) ?_ (ReadPrefix.read (g := fun v => c₃.put (pc 4) (reg 4) v) _ ?_
      (ReadPrefix.tick (d := c₅) ?_ (ReadPrefix.tick ?_ (ReadPrefix.nil d))))))
    · rw [step_at hl 1 (c := c₁) rfl]
      change CallAction.read (c₁.reg (reg 4)) _ = _
      rw [Config.put_same]
    · rw [step_at hl 2 (c := c₂) rfl]
      change CallAction.localStep (c₂.put (pc 3) (reg 4) (c₂.reg (reg 7) + c₂.reg (reg 5))) = _
      simp [c₃, c₂, c₁, Config.put, off, id]
    · rw [step_at hl 3 (c := c₃) rfl]
      change CallAction.read (c₃.reg (reg 4)) _ = _
      rw [Config.put_same]
    · rw [step_at hl 4 (c := c₄) rfl]
      change CallAction.localStep (c₄.put (pc 5) (reg 0) (c₄.reg (reg 0) + c₄.reg (reg 4))) = _
      simp [c₅, c₄, c₃, c₂, c₁, Config.put]
    · rw [step_at hl 5 (c := c₅) rfl]
      change CallAction.localStep (c₅.put copy (reg 1) (c₅.reg (reg 2) + c₅.reg (reg 1))) = _
      simp [d, c₅, c₄, c₃, c₂, c₁, Config.put]
  refine ⟨d, rfl, by simp [d, c₅, Config.put], Config.put_same .., ?_, rfl, rfl,
    ReadPrefix.execute path⟩
  intro j h₀ h₁ h₄
  simp [d, c₅, c₄, c₃, c₂, c₁, Config.put, Function.update_of_ne h₀,
    Function.update_of_ne h₁, Function.update_of_ne h₄]

variable {arcPC : Fin 7 → Fin p} {done : Fin p}

/-- Exact native run for the independently supplied half-word at one port. -/
theorem execute_segment (hl : Linked M pc reg (arcPC 0))
    (hcopy : PrivateFields.Linked M .copy arcPC (copyRegs reg) done) (mem : Memory w)
    (c : Config w p r) (hc : c.pc = pc 0) (src dst : ℕ) (bs : List Bool)
    (hs : c.reg (reg 0) = (src : Word w)) (hd : c.reg (reg 2) = (dst : Word w))
    (hone : c.reg (reg 3) = 1)
    (len : (mem (c.reg (reg 6) + c.reg (reg 5)).val).val = bs.length)
    (dstFit : dst + bs.length < 2 ^ w) :
    let id := c.reg (reg 5)
    let wid := c.reg (reg 6)
    let off := c.reg (reg 7)
    let start := src + (mem (off + id).val).val
    start + bs.length ≤ 2 ^ w → (dst ≤ start ∨ start + bs.length ≤ dst) →
    (∀ i : Fin bs.length,
      c.privateMem ((start + i.val : ℕ) : Word w) = PrivateFields.bitValue w bs[i.val]) →
    ∃ out, out.pc = done ∧ out.persistent = c.persistent ∧
      out.privateMem = PrivateFields.storeBits dst bs c.privateMem ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 1 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j) ∧
      ∀ fuel tail, execute M.program (fuel + (7 + 5 * bs.length)) c mem tail =
        (execute M.program fuel out mem tail).map
          (fun rep => ⟨segmentEvents mem wid off id bs ++ rep.events, rep.result⟩) := by
  intro id wid off start srcFit safe data
  obtain ⟨d, dp, s, e, keep, dm, dt, run⟩ := execute_header hl c hc mem
  have s' : d.reg ((copyRegs reg) 0) = (start : Word w) := by
    change d.reg (reg 0) = _
    simp only [s, hs, start, Nat.cast_add, Fin.cast_val_eq_self, off, id]
  have e' : d.reg ((copyRegs reg) 1) = ((dst + bs.length : ℕ) : Word w) := by
    change d.reg (reg 1) = _
    rw [e, hd, ← len, Nat.cast_add, Fin.cast_val_eq_self]
  have fixReg (i : Fin 8) (h₀ : i ≠ 0) (h₁ : i ≠ 1) (h₄ : i ≠ 4) : d.reg (reg i) = c.reg (reg i) :=
    keep _ (reg.injective.ne h₀) (reg.injective.ne h₁) (reg.injective.ne h₄)
  obtain ⟨out, res, copyRun⟩ := PrivateFields.execute_copy hcopy d dp start dst bs s'
    ((fixReg 2 (by decide) (by decide) (by decide)).trans hd) e'
    ((fixReg 3 (by decide) (by decide) (by decide)).trans hone) dstFit srcFit safe (dm ▸ data)
  refine ⟨out, res.pc, res.persistent.trans dt, dm ▸ res.privateMem, ?_, ?_⟩
  · intro j h₀ h₁ h₂ h₄
    exact (res.frame j h₀ h₂ h₄).trans (keep j h₀ h₁ h₄)
  · intro fuel tail
    have h := run (fuel + (5 * bs.length + 1)) tail
    rw [copyRun] at h
    simpa only [segmentEvents, id, off, wid, Option.map_map, Function.comp_def, List.append_assoc,
      show fuel + (5 * bs.length + 1) + 6 = fuel + (7 + 5 * bs.length) by omega] using h

section Port

open CompressorRecords CompressorRecords.PortRefresh CompressorRecords.RefreshRAM
open CompressorRecords.PortRefresh.NewSlots
open Compression Compression.Refresh Compression.DegreeRefresh

variable {a g : ℕ} (X : State a (a + g)) (q : Fin 8 → BurstRAM.Word w) (mem : Memory w)
local notation "ord" => sites (D := 2 ^ a) X.baseIndex (bitWordFinEquiv g)
local notation "S" => Fintype.card X.Base * 2 ^ a * 2 ^ g * 2 ^ a

/-- Physically addressed traces for all segments in either local direction, including
the diagonal port. The bit index type is the length word read from that direction. -/
def portTrace (fit : S ≤ 2 ^ w) (outgoing : Bool) (e : DyadicArc X.Base (BitWord g) a)
    (bits : Fin (Readback.interval X q mem fit outgoing e).1 → Bool) : List (Event w) :=
  segmentEvents mem (if outgoing then q 1 else q 7) (if outgoing then q 5 else q 6)
    (idWord ord fit e) (List.ofFn bits)

/-- The native copy consumes the physical interval addressed by the port trace.
The header ABI takes the two column heads and the source-major port ordinal. -/
theorem execute_port {fit : S ≤ 2 ^ w} (outgoing : Bool) (e : DyadicArc X.Base (BitWord g) a)
    (bits : Fin (Readback.interval X q mem fit outgoing e).1 → Bool)
    (hl : Linked M pc reg (arcPC 0))
    (hcopy : PrivateFields.Linked M .copy arcPC (copyRegs reg) done)
    (c : Config w p r) (hc : c.pc = pc 0) (src dst : ℕ)
    (hs : c.reg (reg 0) = (src : BurstRAM.Word w)) (hd : c.reg (reg 2) = (dst : BurstRAM.Word w))
    (hone : c.reg (reg 3) = 1) (hi : c.reg (reg 5) = idWord ord fit e)
    (hw : c.reg (reg 6) = if outgoing then q 1 else q 7)
    (ho : c.reg (reg 7) = if outgoing then q 5 else q 6) :
    let interval := Readback.interval X q mem fit outgoing e
    let start := src + interval.2
    dst + interval.1 < 2 ^ w → start + interval.1 ≤ 2 ^ w →
    (dst ≤ start ∨ start + interval.1 ≤ dst) →
    (∀ i : Fin interval.1, c.privateMem ((start + i.val : ℕ) : BurstRAM.Word w) =
      PrivateFields.bitValue w (bits i)) →
    ∃ out, out.pc = done ∧ out.persistent = c.persistent ∧
      out.privateMem = PrivateFields.storeBits dst (List.ofFn bits) c.privateMem ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 1 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j) ∧
      ∀ fuel tail, execute M.program (fuel + (portTrace X q mem fit outgoing e bits).length)
          c mem tail = (execute M.program fuel out mem tail).map
            (fun rep => ⟨portTrace X q mem fit outgoing e bits ++ rep.events, rep.result⟩) := by
  intro interval start dstFit srcFit safe data
  have len : (mem (c.reg (reg 6) + c.reg (reg 5)).val).val = interval.1 := by
    rw [hw, hi]
    cases outgoing <;> rfl
  have offset : (mem (c.reg (reg 7) + c.reg (reg 5)).val).val = interval.2 := by
    rw [ho, hi]
    cases outgoing <;> rfl
  have exec := execute_segment hl hcopy mem c hc src dst (List.ofFn bits) hs hd hone
    (len.trans List.length_ofFn.symm) (by simpa only [List.length_ofFn] using dstFit)
  simp only [List.length_ofFn, List.getElem_ofFn, offset] at exec
  obtain ⟨out, exitPC, persistent, contents, frame, run⟩ :=
    exec srcFit safe (fun i => data ⟨i.val, by simpa using i.isLt⟩)
  refine ⟨out, exitPC, persistent, contents, frame, fun fuel tail => ?_⟩
  simpa only [portTrace, (segment_work ..).1, List.length_ofFn, hw, ho, hi] using run fuel tail

theorem port_group_clock {fit : S ≤ 2 ^ w} (stored : SegmentFields X q fit mem)
    (outgoing : Bool) (v : (X.Base × BitWord g) × Fin (2 ^ a))
    (bits : ∀ j, Fin (Readback.interval X q mem fit outgoing (v, j)).1 → Bool) :
    let traces := fun j => portTrace X q mem fit outgoing (v, j) (bits j)
    (∑ j, (traces j).length) ≤ 2 ^ a * (7 + 5 * X.maxWireWidth) ∧
    (∑ j, countProbes (traces j)) = 2 ^ a * 2 := by
  intro traces
  have hw (j : Fin (2 ^ a)) :
      (traces j).length ≤ 7 + 5 * X.maxWireWidth ∧ countProbes (traces j) = 2 := by
    let e := (v, j)
    have he := Readback.interval_spec X q mem stored e
    have hb : (Readback.interval X q mem fit outgoing e).1 ≤ X.maxWireWidth := by
      cases outgoing
      · rw [he.2]; exact X.width_le_maxWireWidth _
      · rw [he.1]; exact X.width_le_maxWireWidth _
    have h := segment_work mem (if outgoing then q 1 else q 7) (if outgoing then q 5 else q 6)
      (idWord ord fit e) (List.ofFn (bits j))
    have le : (List.ofFn (bits j)).length ≤ X.maxWireWidth := by simpa using hb
    exact ⟨h.1.le.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 5 le) 7), h.2⟩
  constructor
  · simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hw j).1)
  · rw [Finset.sum_congr rfl (fun j _ => (hw j).2)]
    simp

/-- The refresh kernel takes the outgoing and incoming segments independently. -/
theorem incident_clock {fit : S ≤ 2 ^ w} (stored : SegmentFields X q fit mem)
    (v : (X.Base × BitWord g) × Fin (2 ^ a))
    (bits : ∀ dir j, Fin (Readback.interval X q mem fit dir (v, j)).1 → Bool) :
    let traces := fun dir j => portTrace X q mem fit dir (v, j) (bits dir j)
    (∑ j, (traces true j).length) + (∑ j, (traces false j).length) ≤
      (2 * 2 ^ a) * (7 + 5 * X.maxWireWidth) ∧
    (∑ j, countProbes (traces true j)) + (∑ j, countProbes (traces false j)) =
      (2 * 2 ^ a) * 2 := by
  intro traces
  have out := port_group_clock X q mem stored true v (bits true)
  have inc := port_group_clock X q mem stored false v (bits false)
  rw [two_mul (2 ^ a), Nat.add_mul, Nat.add_mul]
  exact ⟨Nat.add_le_add out.1 inc.1, congrArg₂ Nat.add out.2 inc.2⟩

end Port

end PairSimulation.RefreshSliceClock

end VPVNP
end Computability
end OAI
