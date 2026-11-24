import OAI.Computability.VPVNP.PairSimulationPrivateFields
import OAI.Computability.VPVNP.CompressorSliceSchedule

/-!
# Reading slice records inside a final-site call

The setup reads the length at frame address plus two before using either
offset. A positive length selects the source and target offset reads,
adds these to the supplied private field bases and enters the copy loop.
An empty intersection returns immediately.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.PrivateSlices

open BurstRAM BurstRAM.PrivateRAM CompressorRecords.SliceSchedule
open scoped Fin.CommRing

variable {w p r k : ℕ}

private abbrev word (w n : ℕ) : Word w := (n : Word w)
private theorem val_word {n : ℕ} (hn : n < 2^w) : (word w n).val = n := Nat.mod_eq_of_lt hn

/-- Registers 0–4 share the copy-loop ABI. The sixth register is the
external address of the first offset and is preserved. -/
def instruction (pc : Fin 11 → Fin p) (reg : Fin 6 ↪ Fin r) (copy done : Fin p) :
    Fin 11 → Instr w p r k :=
  ![.binary .add (reg 4) (reg 5) (reg 3) (pc 1),
    .binary .add (reg 4) (reg 4) (reg 3) (pc 2),
    .readExternal (reg 1) (reg 4) (pc 3), .constant (reg 4) 0 (pc 4),
    .jumpEq (reg 1) (reg 4) done (pc 5),
    .readExternal (reg 4) (reg 5) (pc 6), .binary .add (reg 0) (reg 0) (reg 4) (pc 7),
    .binary .add (reg 4) (reg 5) (reg 3) (pc 8), .readExternal (reg 4) (reg 4) (pc 9),
    .binary .add (reg 2) (reg 2) (reg 4) (pc 10), .binary .add (reg 1) (reg 2) (reg 1) copy]

theorem resize_instruction (pc : Fin 11 → Fin p) (reg : Fin 6 ↪ Fin r) (copy done : Fin p) (i : Fin 11) :
    (instruction (w := 1) (k := k) pc reg copy done i).resize w = instruction pc reg copy done i := by
  fin_cases i <;> rfl

/-- The machine contains the eleven slice-setup instructions that check the length, return for
an empty slice, or apply both offsets and enter the copy loop. -/
def Linked (M : Machine w p r k) (pc : Fin 11 → Fin p) (reg : Fin 6 ↪ Fin r)
    (copy done : Fin p) : Prop := ∀ i, M.code (pc i) = instruction pc reg copy done i

/-- Restrict the slice-setup register allocation to the first five registers shared with the
private copy loop. -/
def copyRegs (reg : Fin 6 ↪ Fin r) : Fin 5 ↪ Fin r := (Fin.castAddEmb 1).trans reg

/-- Exact header trace. Empty records read only the length cell. -/
def headerEvents (mem : Memory w) (frame : Word w) : List (Event w) :=
  let addr := frame+1+1
  let len := mem addr.val
  [.tick,.tick,.read addr len,.tick,.tick] ++
    if len = 0 then [] else [.read frame (mem frame.val),.tick,.tick,.read (frame+1) (mem (frame+1).val),.tick,.tick]

/-- The header contains local instructions and external reads only. -/
private inductive ReadPrefix (M : Machine w p r k) (m : Memory w) :
    Config w p r → List (Event w) → Config w p r → Prop
  | nil (c) : ReadPrefix M m c [] c
  | tick {c d z es} (hs : M.program.step c = .localStep d) (tail : ReadPrefix M m d es z) :
      ReadPrefix M m c (.tick :: es) z
  | read {c g z es} (a : Word w) (hs : M.program.step c = .read a g)
      (tail : ReadPrefix M m (g (m a.val)) es z) : ReadPrefix M m c (.read a (m a.val) :: es) z

private theorem ReadPrefix.execute {M : Machine w p r k} {m : Memory w} {c d : Config w p r}
    {es : List (Event w)} (h : ReadPrefix M m c es d) (fuel : ℕ) (bs : List Bool) :
    BurstRAM.execute M.program (fuel+es.length) c m bs =
      (BurstRAM.execute M.program fuel d m bs).map (fun rep ↦ ⟨es ++ rep.events,rep.result⟩) := by
  induction h with
  | nil => simp
  | tick hs tail ih | read _ hs tail ih =>
    rw [List.length_cons, ← Nat.add_assoc]
    simp [BurstRAM.execute, hs, ih, Option.map_map, Function.comp_def, Report.prepend]

variable {M : Machine w p r k} {pc : Fin 11 → Fin p} {reg : Fin 6 ↪ Fin r} {copy done : Fin p}

private theorem step_at (hl : Linked M pc reg copy done) (i : Fin 11) (c : Config w p r)
    (hc : c.pc = pc i) : M.program.step c = (instruction pc reg copy done i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

/-- The header exit and its copy operands. On the empty branch the offsets
need no values, so the input field bases stay available. -/
structure HeaderResult (reg : Fin 6 ↪ Fin r) (copy done : Fin p) (c out : Config w p r)
    (frame : Word w) (m : Memory w) : Prop where
  pc : out.pc = if m (frame+1+1).val = 0 then done else copy
  args : m (frame+1+1).val ≠ 0 →
    out.reg (reg 0) = c.reg (reg 0) + m frame.val ∧
    out.reg (reg 2) = c.reg (reg 2) + m (frame+1).val ∧
    out.reg (reg 1) = out.reg (reg 2) + m (frame+1+1).val
  frameRegs : ∀ j, j ≠ reg 0 → j ≠ reg 1 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j
  memory : out.privateMem = c.privateMem
  persistent : out.persistent = c.persistent

/-- Execute the length-first header read and pass the resulting registers to
the linked copy or to the empty-slice continuation. -/
theorem execute_header (hl : Linked M pc reg copy done) (c : Config w p r) (hc : c.pc = pc 0)
    (h1 : c.reg (reg 3) = 1) (mem : Memory w) :
    ∃ out, HeaderResult reg copy done c out (c.reg (reg 5)) mem ∧ ∀ fuel bs,
      execute M.program (fuel+(headerEvents mem (c.reg (reg 5))).length) c mem bs =
        (execute M.program fuel out mem bs).map (fun rep ↦ ⟨headerEvents mem (c.reg (reg 5)) ++ rep.events,rep.result⟩) := by
  let f := c.reg (reg 5)
  let len := mem (f+1+1).val
  let c₁ := c.put (pc 1) (reg 4) (f+1)
  let c₂ := c₁.put (pc 2) (reg 4) (f+1+1)
  let c₃ := c₂.put (pc 3) (reg 1) len
  let c₄ := c₃.put (pc 4) (reg 4) 0
  have s₀ : M.program.step c = .localStep c₁ := by
    rw [step_at hl 0 c hc]
    change CallAction.localStep (c.put (pc 1) (reg 4) (f+c.reg (reg 3))) = _
    rw [h1]
  have s₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step_at hl 1 c₁ rfl]
    change CallAction.localStep (c₁.put (pc 2) (reg 4) (c₁.reg (reg 4)+c₁.reg (reg 3))) = _
    simp [c₂,c₁,Config.put,h1]
  have s₂ : M.program.step c₂ = .read (f+1+1) (fun v ↦ c₂.put (pc 3) (reg 1) v) := by
    rw [step_at hl 2 c₂ rfl]
    change CallAction.read (c₂.reg (reg 4)) _ = _
    rw [Config.put_same]
  have s₃ : M.program.step c₃ = .localStep c₄ := step_at hl 3 c₃ rfl
  have s₄ : M.program.step c₄ = .localStep {c₄ with pc := if len = 0 then done else pc 5} := by
    rw [step_at hl 4 c₄ rfl]
    change CallAction.localStep {c₄ with pc := if c₄.reg (reg 1) = c₄.reg (reg 4) then done else pc 5} = _
    simp [c₄,c₃,Config.put]
  let tested (dest : Fin p) := {c₄ with pc := dest}
  let first : List (Event w) := [.tick,.tick,.read (f+1+1) len,.tick,.tick]
  have test {es : List (Event w)} {out : Config w p r}
      (tail : ReadPrefix M mem (tested (if len=0 then done else pc 5)) es out) :
      ReadPrefix M mem c (first ++ es) out :=
    .tick s₀ (.tick s₁ (.read _ s₂ (.tick s₃ (.tick s₄ tail))))
  by_cases hz : len = 0
  · let out := tested done
    have tail : ReadPrefix M mem (tested (if len=0 then done else pc 5)) [] out := by
      rw [ite_eq_left hz]; exact .nil _
    have ht : headerEvents mem f = first ++ [] := by simp [headerEvents, ← show mem (f+1+1).val = len from rfl, hz,first,len]
    refine ⟨out, ⟨?_, ?_, ?_, rfl, rfl⟩, ?_⟩
    · change done = if len=0 then done else copy
      simp [hz]
    · exact fun h ↦ (h hz).elim
    · intro j _ hj₁ _ hj₄
      simp [out,tested,c₄,c₃,c₂,c₁,Config.put,Function.update_of_ne hj₄, Function.update_of_ne hj₁]
    · intro fuel bs
      change execute M.program (fuel+(headerEvents mem f).length) c mem bs = _
      rw [ht]
      exact (test tail).execute fuel bs
  · let c₅ := tested (pc 5)
    let c₆ := c₅.put (pc 6) (reg 4) (mem f.val)
    let c₇ := c₆.put (pc 7) (reg 0) (c.reg (reg 0) + mem f.val)
    let c₈ := c₇.put (pc 8) (reg 4) (f+1)
    let c₉ := c₈.put (pc 9) (reg 4) (mem (f+1).val)
    let dst := c.reg (reg 2) + mem (f+1).val
    let c₁₀ := c₉.put (pc 10) (reg 2) dst
    let out := c₁₀.put copy (reg 1) (dst+len)
    have s₅ : M.program.step c₅ = .read f (fun v ↦ c₅.put (pc 6) (reg 4) v) := by
      rw [step_at hl 5 c₅ rfl]
      change CallAction.read (c₅.reg (reg 5)) _ = _
      simp [c₅,tested,c₄,c₃,c₂,c₁,Config.put,f]
    have s₆ : M.program.step c₆ = .localStep c₇ := by
      rw [step_at hl 6 c₆ rfl]
      change CallAction.localStep (c₆.put (pc 7) (reg 0) (c₆.reg (reg 0)+c₆.reg (reg 4))) = _
      simp [c₇,c₆,c₅,tested,c₄,c₃,c₂,c₁,Config.put]
    have s₇ : M.program.step c₇ = .localStep c₈ := by
      rw [step_at hl 7 c₇ rfl]
      change CallAction.localStep (c₇.put (pc 8) (reg 4) (c₇.reg (reg 5)+c₇.reg (reg 3))) = _
      simp [c₈,c₇,c₆,c₅,tested,c₄,c₃,c₂,c₁,Config.put,f,h1]
    have s₈ : M.program.step c₈ = .read (f+1) (fun v ↦ c₈.put (pc 9) (reg 4) v) := by
      rw [step_at hl 8 c₈ rfl]
      change CallAction.read (c₈.reg (reg 4)) _ = _
      rw [Config.put_same]
    have s₉ : M.program.step c₉ = .localStep c₁₀ := by
      rw [step_at hl 9 c₉ rfl]
      change CallAction.localStep (c₉.put (pc 10) (reg 2) (c₉.reg (reg 2)+c₉.reg (reg 4))) = _
      simp [c₁₀,c₉,c₈,c₇,c₆,c₅,tested,c₄,c₃,c₂,c₁,Config.put,dst]
    have s₁₀ : M.program.step c₁₀ = .localStep out := by
      rw [step_at hl 10 c₁₀ rfl]
      change CallAction.localStep (c₁₀.put copy (reg 1) (c₁₀.reg (reg 2)+c₁₀.reg (reg 1))) = _
      simp [out,c₁₀,c₉,c₈,c₇,c₆,c₅,tested,c₄,c₃,Config.put]
    let es : List (Event w) := [.read f (mem f.val),.tick,.tick,.read (f+1) (mem (f+1).val),.tick,.tick]
    have tail : ReadPrefix M mem (tested (if len=0 then done else pc 5)) es out := by
      rw [ite_eq_right hz]
      exact .read _ s₅ (.tick s₆ (.tick s₇ (.read _ s₈ (.tick s₉ (.tick s₁₀ (.nil _))))))
    have ht : headerEvents mem f = first ++ es := by
      change first ++ (if len = 0 then [] else es) = _
      rw [ite_eq_right hz]
    refine ⟨out, ⟨?_, ?_, ?_, rfl, rfl⟩, ?_⟩
    · change copy = if len=0 then done else copy
      simp [hz]
    · intro _
      simp [out,c₁₀,c₉,c₈,c₇,Config.put, dst, f, len]
    · intro j hj₀ hj₁ hj₂ hj₄
      simp [out,c₁₀,c₉,c₈,c₇,c₆,c₅,tested,c₄,c₃,c₂,c₁,Config.put,Function.update_of_ne hj₀,
        Function.update_of_ne hj₁,Function.update_of_ne hj₂,Function.update_of_ne hj₄]
    · intro fuel bs
      change execute M.program (fuel+(headerEvents mem f).length) c mem bs = _
      rw [ht]
      exact (test tail).execute fuel bs

/-- A zero-length frame returns directly. A nonempty frame also executes
the full private-copy loop after its three header reads. -/
def frameEvents (mem : Memory w) (frame : Word w) (bs : List Bool) : List (Event w) :=
  headerEvents mem frame ++ if bs.isEmpty then [] else PrivateFields.events .copy bs

theorem frame_work (mem : Memory w) (frame : Word w) (bs : List Bool)
    (h : (mem (frame+1+1).val).val = bs.length) :
    (frameEvents mem frame bs).length = (if bs.isEmpty then 5 else 5*bs.length+12) ∧
    countProbes (frameEvents mem frame bs) = (if bs.isEmpty then 1 else 3) := by
  cases bs with
  | nil =>
    have hz : mem (frame+1+1).val = 0 := Fin.ext h
    simp [frameEvents, headerEvents, hz, countProbes]
  | cons b bs =>
    have hne : mem (frame+1+1).val ≠ 0 := by
      intro hz
      rw [hz] at h
      simp at h
    have hw := PrivateFields.events_work (w := w) .copy (b::bs)
    simp only [ite_false, reduceCtorEq] at hw
    simp [frameEvents, headerEvents, hne, countProbes, hw.1, hw.2]

variable {arcPC : Fin 7 → Fin p}

/-- Read a completed frame and copy its declared bits. Fit, source contents
and forward-copy overlap conditions are needed only for positive lengths.
Outside its destination interval the entire private memory is preserved. -/
theorem execute_frame (hl : Linked M pc reg (arcPC 0) done)
    (hcopy : PrivateFields.Linked M .copy arcPC (copyRegs reg) done)
    (c : Config w p r) (hc : c.pc = pc 0) (h1 : c.reg (reg 3) = 1)
    {pub : Fin 6 → Word w} {old new : List ℕ} {initial mem : Memory w} {completed : ℕ}
    (frames : FramesAt pub old new initial mem completed) (a : Fin completed)
    (frameFit : (pub 5).val+3*a.val+2 < 2^w) (src dst : ℕ)
    (hf : c.reg (reg 5) = word w ((pub 5).val+3*a.val))
    (hs : c.reg (reg 0) = word w src) (hd : c.reg (reg 2) = word w dst)
    (bs : List Bool) (hlen : bs.length = (sliceAt old new a.val).length)
    (fit : 0 < bs.length → src + (sliceAt old new a.val).sourceOffset + bs.length ≤ 2^w ∧
      dst + (sliceAt old new a.val).targetOffset + bs.length < 2^w)
    (safe : 0 < bs.length → dst + (sliceAt old new a.val).targetOffset ≤ src + (sliceAt old new a.val).sourceOffset ∨
      src + (sliceAt old new a.val).sourceOffset + bs.length ≤ dst + (sliceAt old new a.val).targetOffset)
    (data : ∀ i : Fin bs.length,
      c.privateMem (word w (src+(sliceAt old new a.val).sourceOffset+i.val)) = PrivateFields.bitValue w bs[i.val]) :
    ∃ out, out.pc = done ∧ out.persistent = c.persistent ∧
      out.privateMem = PrivateFields.storeBits (dst+(sliceAt old new a.val).targetOffset) bs c.privateMem ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 1 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j) ∧
      (∀ fuel more, execute M.program (fuel+(frameEvents mem (c.reg (reg 5)) bs).length) c mem more =
        (execute M.program fuel out mem more).map
          (fun rep ↦ ⟨frameEvents mem (c.reg (reg 5)) bs ++ rep.events,rep.result⟩)) ∧
      (frameEvents mem (c.reg (reg 5)) bs).length = (if bs.isEmpty then 5 else 5*bs.length+12) ∧
      countProbes (frameEvents mem (c.reg (reg 5)) bs) = (if bs.isEmpty then 1 else 3) := by
  let base := (pub 5).val+3*a.val
  let frame := c.reg (reg 5)
  let s := sliceAt old new a.val
  have ha₀ : frame.val = base := by rw [show frame = word w base from hf, val_word (by dsimp [base]; omega)]
  have ha₁ : (frame+1).val = base+1 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2^w), ha₀,
      Nat.mod_eq_of_lt (by dsimp [base]; omega)]
  have ha₂ : (frame+1+1).val = base+2 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2^w), ha₁,
      Nat.mod_eq_of_lt (by dsimp [base]; omega)]
  have hlenWord : (mem (frame+1+1).val).val = bs.length := by
    rw [ha₂, hlen]
    exact frames.lengths a.val a.isLt
  obtain ⟨prepared, prep, run⟩ := execute_header hl c hc h1 mem
  obtain ⟨work, probes⟩ := frame_work mem frame bs hlenWord
  cases bs with
  | nil =>
    have hz : mem (frame+1+1).val = 0 := Fin.ext hlenWord
    have hpc : prepared.pc = done := prep.pc.trans (ite_eq_left hz)
    refine ⟨prepared,hpc,prep.persistent,prep.memory,prep.frameRegs,?_,work,probes⟩
    intro fuel more
    simpa [frameEvents] using run fuel more
  | cons b bs =>
    let bits := b :: bs
    have hp : 0 < bits.length := Nat.succ_pos _
    have hnz : mem (frame+1+1).val ≠ 0 := by
      intro he
      rw [he] at hlenWord
      simp at hlenWord
    have hpc : prepared.pc = arcPC 0 := prep.pc.trans (ite_eq_right hnz)
    obtain ⟨pa,pb,pe⟩ := prep.args hnz
    obtain ⟨hso,hto⟩ := frames.offsets a.val a.isLt (by rw [← hlen]; exact hp)
    have hsrc : mem frame.val = word w s.sourceOffset := by
      rw [ha₀]
      apply Fin.ext
      rw [show (mem base).val = s.sourceOffset from hso]
      exact (Nat.mod_eq_of_lt (hso ▸ (mem base).isLt)).symm
    have hdst : mem (frame+1).val = word w s.targetOffset := by
      rw [ha₁]
      apply Fin.ext
      rw [show (mem (base+1)).val = s.targetOffset from hto]
      exact (Nat.mod_eq_of_lt (hto ▸ (mem (base+1)).isLt)).symm
    have hlen' : mem (frame+1+1).val = word w bits.length := by
      apply Fin.ext
      rw [show (mem (frame+1+1).val).val = bits.length from hlenWord]
      exact (Nat.mod_eq_of_lt (hlenWord ▸ (mem (frame+1+1).val).isLt)).symm
    have hs' : prepared.reg ((copyRegs reg) 0) = word w (src+s.sourceOffset) := by
      change prepared.reg (reg 0) = _
      rw [pa, hs, hsrc]; simp [word]
    have hd' : prepared.reg ((copyRegs reg) 2) = word w (dst+s.targetOffset) := by
      change prepared.reg (reg 2) = _
      rw [pb, hd, hdst]; simp [word]
    have he' : prepared.reg ((copyRegs reg) 1) = word w (dst+s.targetOffset+bits.length) := by
      change prepared.reg (reg 1) = _
      rw [pe, show prepared.reg (reg 2) = word w (dst+s.targetOffset) from hd', hlen']; simp [word]
    have hone : prepared.reg ((copyRegs reg) 3) = 1 :=
      (prep.frameRegs (reg 3) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
        (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans h1
    obtain ⟨out,res,crun⟩ := PrivateFields.execute_copy hcopy prepared hpc (src+s.sourceOffset)
      (dst+s.targetOffset) bits hs' hd' he' hone (fit hp).2 (fit hp).1 (safe hp)
      (by rw [prep.memory]; exact data)
    refine ⟨out,res.pc,res.persistent.trans prep.persistent,?_,?_,?_,work,probes⟩
    · rw [res.privateMem, prep.memory]
    · intro j h₀ h₁ h₂ h₄
      exact (res.frame j h₀ h₂ h₄).trans (prep.frameRegs j h₀ h₁ h₂ h₄)
    · intro fuel more
      have hrun := run (fuel+(5*bits.length+1)) more
      rw [crun] at hrun
      have hframe : frameEvents mem frame bits = headerEvents mem frame ++ PrivateFields.events .copy bits := rfl
      rw [show frameEvents mem (c.reg (reg 5)) (b :: bs) = _ from hframe, List.length_append,
        (PrivateFields.events_work (w := w) .copy bits).1]
      simp only [reduceCtorEq, ite_false]
      simpa [Option.map_map, Function.comp_def, frame, List.append_assoc, Nat.add_assoc,
        Nat.add_comm (headerEvents mem (c.reg (reg 5))).length] using hrun

end PairSimulation.PrivateSlices

end VPVNP
end Computability
end OAI
