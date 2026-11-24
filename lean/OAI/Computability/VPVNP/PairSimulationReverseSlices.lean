import OAI.Computability.VPVNP.PairSimulationPrivateSlices

/-!
# Reading a subdivision slice from the new supply field

The frame stores the old-field offset first and the new-field offset second.
Recovering an old argument from a surviving supply field copies in the
opposite direction. The header reads the same three addresses in the same
order, then enters the ordinary private copy loop with the new field as source.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ReverseSlices

open BurstRAM BurstRAM.PrivateRAM CompressorRecords.SliceSchedule
open PrivateSlices (copyRegs headerEvents frameEvents frame_work)
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.nil ReadPrefix.tick ReadPrefix.read ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r k : ℕ}

/-- Exchange the two offset-add instructions. Register 0 is still the
private source cursor and register 2 the private destination cursor. -/
def instruction (pc : Fin 11 → Fin p) (reg : Fin 6 ↪ Fin r) (copy done : Fin p)
    (i : Fin 11) : Instr w p r k :=
  if i = 6 then .binary .add (reg 2) (reg 2) (reg 4) (pc 7)
  else if i = 9 then .binary .add (reg 0) (reg 0) (reg 4) (pc 10)
  else PrivateSlices.instruction pc reg copy done i

theorem resize_instruction (pc : Fin 11 → Fin p) (reg : Fin 6 ↪ Fin r) (copy done : Fin p)
    (i : Fin 11) :
    (instruction (w := 1) (k := k) pc reg copy done i).resize w =
      instruction pc reg copy done i := by
  fin_cases i <;> rfl

/-- The eleven assigned instructions implement reverse frame setup, adding the new offset to
the source and the old offset to the destination before copying a nonempty slice. -/
def Linked (M : Machine w p r k) (pc : Fin 11 → Fin p) (reg : Fin 6 ↪ Fin r)
    (copy done : Fin p) : Prop := ∀ i, M.code (pc i) = instruction pc reg copy done i

variable {M : Machine w p r k} {pc : Fin 11 → Fin p} {reg : Fin 6 ↪ Fin r} {copy done : Fin p}

private theorem step_at (hl : Linked M pc reg copy done) (i : Fin 11) (c : Config w p r)
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc reg copy done i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

private structure Prepared (reg : Fin 6 ↪ Fin r) (copy done : Fin p)
    (c d : Config w p r) (f srcOff dstOff : Word w) (m : Memory w) : Prop where
  pc : d.pc = if m (f + 1 + 1).val = 0 then done else copy
  args : m (f + 1 + 1).val ≠ 0 →
    d.reg (reg 0) = c.reg (reg 0) + srcOff ∧
    d.reg (reg 2) = c.reg (reg 2) + dstOff ∧
    d.reg (reg 1) = d.reg (reg 2) + m (f + 1 + 1).val
  regs : ∀ j, j ≠ reg 0 → j ≠ reg 1 → j ≠ reg 2 → j ≠ reg 4 → d.reg j = c.reg j
  memory : d.privateMem = c.privateMem
  persistent : d.persistent = c.persistent

private theorem header (hl : Linked M pc reg copy done) (c : Config w p r) (hc : c.pc = pc 0)
    (h1 : c.reg (reg 3) = 1) (m : Memory w) :
    let f := c.reg (reg 5)
    ∃ d, Prepared reg copy done c d f (m (f + 1).val) (m f.val) m ∧
      ReadPrefix M m c (headerEvents m f) d := by
  intro f
  let len := m (f + 1 + 1).val
  let u₁ := c.put (pc 1) (reg 4) (f + 1)
  let u₂ := u₁.put (pc 2) (reg 4) (f + 1 + 1)
  let u₃ := u₂.put (pc 3) (reg 1) len
  let u₄ := u₃.put (pc 4) (reg 4) 0
  let tested := {u₄ with pc := if len = 0 then done else pc 5}
  let first : List (Event w) := [.tick, .tick, .read (f + 1 + 1) len, .tick, .tick]
  have test {es : List (Event w)} {out : Config w p r} (tail : ReadPrefix M m tested es out) :
      ReadPrefix M m c (first ++ es) out := by
    refine ReadPrefix.tick (d := u₁) ?_ (ReadPrefix.tick (d := u₂) ?_
      (ReadPrefix.read (g := fun v ↦ u₂.put (pc 3) (reg 1) v) _ ?_
        (ReadPrefix.tick (d := u₄) ?_ (ReadPrefix.tick ?_ tail))))
    · rw [step_at hl 0 c hc]
      change CallAction.localStep (c.put _ _ (f + c.reg (reg 3))) = _
      rw [h1]
    · rw [step_at hl 1 u₁ rfl]
      change CallAction.localStep (u₁.put _ _ (u₁.reg (reg 4) + u₁.reg (reg 3))) = _
      simp [u₂, u₁, Config.put, h1]
    · rw [step_at hl 2 u₂ rfl]
      change CallAction.read (u₂.reg (reg 4)) (fun v ↦ u₂.put (pc 3) (reg 1) v) = _
      rw [Config.put_same]
    · exact step_at hl 3 u₃ rfl
    · rw [step_at hl 4 u₄ rfl]
      change CallAction.localStep {u₄ with
        pc := if u₄.reg (reg 1) = u₄.reg (reg 4) then done else pc 5} = _
      simp [tested, u₄, u₃, Config.put]
  by_cases hz : len = 0
  · refine ⟨tested, ⟨?_, fun h ↦ (h hz).elim, ?_, rfl, rfl⟩, ?_⟩
    · change (if len = 0 then done else pc 5) = if len = 0 then done else copy
      simp [hz]
    · intro j _ hj₁ _ hj₄
      simp [tested, u₄, u₃, u₂, u₁, Config.put,
        Function.update_of_ne hj₄, Function.update_of_ne hj₁]
    · simpa [headerEvents, first, len, show m (f + 1 + 1).val = 0 from hz] using
        test (ReadPrefix.nil tested)
  · let u₆ := tested.put (pc 6) (reg 4) (m f.val)
    let dst := c.reg (reg 2) + m f.val
    let u₇ := u₆.put (pc 7) (reg 2) dst
    let u₈ := u₇.put (pc 8) (reg 4) (f + 1)
    let u₉ := u₈.put (pc 9) (reg 4) (m (f + 1).val)
    let u₁₀ := u₉.put (pc 10) (reg 0) (c.reg (reg 0) + m (f + 1).val)
    let out := u₁₀.put copy (reg 1) (dst + len)
    let last : List (Event w) :=
      [.read f (m f.val), .tick, .tick, .read (f + 1) (m (f + 1).val), .tick, .tick]
    have tail : ReadPrefix M m tested last out := by
      refine ReadPrefix.read (g := fun v ↦ tested.put (pc 6) (reg 4) v) _ ?_
        (ReadPrefix.tick (d := u₇) ?_ (ReadPrefix.tick (d := u₈) ?_
          (ReadPrefix.read (g := fun v ↦ u₈.put (pc 9) (reg 4) v) _ ?_
            (ReadPrefix.tick (d := u₁₀) ?_ (ReadPrefix.tick ?_ (ReadPrefix.nil out))))))
      · rw [step_at hl 5 tested (by simp [tested, hz])]
        change CallAction.read (tested.reg (reg 5)) (fun v ↦ tested.put (pc 6) (reg 4) v) = _
        simp [tested, u₄, u₃, u₂, u₁, Config.put, f]
      · rw [step_at hl 6 u₆ rfl]
        change CallAction.localStep (u₆.put _ _ (u₆.reg (reg 2) + u₆.reg (reg 4))) = _
        simp [u₇, u₆, dst, tested, u₄, u₃, u₂, u₁, Config.put]
      · rw [step_at hl 7 u₇ rfl]
        change CallAction.localStep (u₇.put _ _ (u₇.reg (reg 5) + u₇.reg (reg 3))) = _
        simp [u₈, u₇, u₆, tested, u₄, u₃, u₂, u₁, Config.put, h1, f]
      · rw [step_at hl 8 u₈ rfl]
        change CallAction.read (u₈.reg (reg 4)) (fun v ↦ u₈.put (pc 9) (reg 4) v) = _
        rw [Config.put_same]
      · rw [step_at hl 9 u₉ rfl]
        change CallAction.localStep (u₉.put _ _ (u₉.reg (reg 0) + u₉.reg (reg 4))) = _
        simp [u₁₀, u₉, u₈, u₇, u₆, tested, u₄, u₃, u₂, u₁, Config.put]
      · rw [step_at hl 10 u₁₀ rfl]
        change CallAction.localStep (u₁₀.put _ _ (u₁₀.reg (reg 2) + u₁₀.reg (reg 1))) = _
        simp [out, u₁₀, u₉, u₈, u₇, u₆, tested, u₄, u₃, Config.put]
    refine ⟨out, ⟨?_, ?_, ?_, rfl, rfl⟩, ?_⟩
    · change copy = if len = 0 then done else copy
      simp [hz]
    · intro _
      simp [out, u₁₀, u₉, u₈, u₇, dst, len, Config.put]
    · intro j h₀ h₁ h₂ h₄
      simp [out, u₁₀, u₉, u₈, u₇, u₆, tested, u₄, u₃, u₂, u₁, Config.put,
        Function.update_of_ne h₀, Function.update_of_ne h₁, Function.update_of_ne h₂,
        Function.update_of_ne h₄]
    · simpa [headerEvents, first, last, len, show m (f + 1 + 1).val ≠ 0 from hz] using test tail

private theorem oriented_header (reverse : Bool)
    (hl : if reverse then Linked M pc reg copy done else PrivateSlices.Linked M pc reg copy done)
    (c : Config w p r) (hc : c.pc = pc 0) (h1 : c.reg (reg 3) = 1) (m : Memory w) :
    let f := c.reg (reg 5)
    ∃ d, Prepared reg copy done c d f
      (if reverse then m (f + 1).val else m f.val) (if reverse then m f.val else m (f + 1).val) m ∧
      ∀ fuel more, execute M.program (fuel + (headerEvents m f).length) c m more =
        (execute M.program fuel d m more).map
          (fun rep ↦ ⟨headerEvents m f ++ rep.events, rep.result⟩) := by
  cases reverse with
  | false =>
    obtain ⟨d, h, run⟩ := PrivateSlices.execute_header hl c hc h1 m
    exact ⟨d, ⟨h.pc, h.args, h.frameRegs, h.memory, h.persistent⟩, run⟩
  | true =>
    obtain ⟨d, h, pre⟩ := header hl c hc h1 m
    exact ⟨d, h, ReadPrefix.execute pre⟩

/-- The exact continuation of a slice copy in either direction. -/
abbrev FrameResult (M : Machine w p r k) (reg : Fin 6 ↪ Fin r) (done : Fin p)
    (c : Config w p r) (m : Memory w) (f : Word w) (dst : ℕ) (bs : List Bool) : Prop :=
  ∃ out, out.pc = done ∧ out.persistent = c.persistent ∧
    out.privateMem = PrivateFields.storeBits dst bs c.privateMem ∧
    (∀ j, j ≠ reg 0 → j ≠ reg 1 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j) ∧
    (∀ fuel more, execute M.program (fuel + (frameEvents m f bs).length) c m more =
      (execute M.program fuel out m more).map
        (fun rep ↦ ⟨frameEvents m f bs ++ rep.events, rep.result⟩)) ∧
    (frameEvents m f bs).length = (if bs.isEmpty then 5 else 5 * bs.length + 12) ∧
    countProbes (frameEvents m f bs) = (if bs.isEmpty then 1 else 3)

private theorem word_of_val {u : Word w} {n : ℕ} (h : u.val = n) : u = (n : Word w) := by
  apply Fin.ext
  exact h.trans (Nat.mod_eq_of_lt (h ▸ u.isLt)).symm

variable {arcPC : Fin 7 → Fin p}

/-- Use only the three words of the resident frame. The first offset belongs
to the old field and the second to the new one. The selected direction determines
which is used as the private source offset. Empty frames need only their length. -/
theorem execute_stored_frame (reverse : Bool)
    (hl : if reverse then Linked M pc reg (arcPC 0) done
      else PrivateSlices.Linked M pc reg (arcPC 0) done)
    (hcopy : PrivateFields.Linked M .copy arcPC (copyRegs reg) done)
    (c : Config w p r) (hc : c.pc = pc 0) (h1 : c.reg (reg 3) = 1)
    (m : Memory w) (f : Word w) (hf : c.reg (reg 5) = f)
    (src dst srcOff dstOff : ℕ)
    (hs : c.reg (reg 0) = (src : Word w)) (hd : c.reg (reg 2) = (dst : Word w))
    (bs : List Bool) (hlen : (m (f + 1 + 1).val).val = bs.length)
    (offsets : 0 < bs.length →
      (if reverse then m (f + 1).val else m f.val).val = srcOff ∧
      (if reverse then m f.val else m (f + 1).val).val = dstOff)
    (fit : 0 < bs.length → src + srcOff + bs.length ≤ 2 ^ w ∧ dst + dstOff + bs.length < 2 ^ w)
    (safe : 0 < bs.length → dst + dstOff ≤ src + srcOff ∨ src + srcOff + bs.length ≤ dst + dstOff)
    (data : ∀ i : Fin bs.length, c.privateMem ((src + srcOff + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w bs[i.val]) :
    FrameResult M reg done c m f (dst + dstOff) bs := by
  obtain ⟨d, h, head⟩ := oriented_header reverse hl c hc h1 m
  rw [hf] at h head
  obtain ⟨work, probes⟩ := frame_work m f bs hlen
  cases bs with
  | nil =>
    have hz : m (f + 1 + 1).val = 0 := Fin.ext hlen
    refine ⟨d, h.pc.trans (ite_eq_left hz), h.persistent, h.memory, h.regs, ?_, work, probes⟩
    simpa [frameEvents] using head
  | cons b bs =>
    let bits := b :: bs
    have hp : 0 < bits.length := Nat.succ_pos _
    have hz : m (f + 1 + 1).val ≠ 0 := by intro eq; rw [eq] at hlen; simp at hlen
    obtain ⟨hsrc, hdst, hend⟩ := h.args hz
    obtain ⟨sOff, dOff⟩ := offsets hp
    have source : d.reg ((copyRegs reg) 0) = ((src + srcOff : ℕ) : Word w) := by
      change d.reg (reg 0) = _
      rw [hsrc, hs, word_of_val sOff, Nat.cast_add]
    have dest : d.reg ((copyRegs reg) 2) = ((dst + dstOff : ℕ) : Word w) := by
      change d.reg (reg 2) = _
      rw [hdst, hd, word_of_val dOff, Nat.cast_add]
    have limit : d.reg ((copyRegs reg) 1) = ((dst + dstOff + bits.length : ℕ) : Word w) := by
      change d.reg (reg 1) = _
      rw [hend, show d.reg (reg 2) = _ from dest, word_of_val hlen]
      simp [bits]
    have one : d.reg ((copyRegs reg) 3) = 1 :=
      (h.regs _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
        (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans h1
    obtain ⟨out, pref, res⟩ := PrivateFields.copy_prefix hcopy d (h.pc.trans (ite_eq_right hz))
      (src + srcOff) (dst + dstOff) bits source dest limit one (fit hp).2 (fit hp).1 (safe hp)
      (by rw [h.memory]; exact data)
    refine ⟨out, res.pc, res.persistent.trans h.persistent, ?_, ?_, ?_, work, probes⟩
    · rw [res.privateMem, h.memory]
    · intro j h₀ h₁ h₂ h₄
      exact (res.frame j h₀ h₂ h₄).trans (h.regs j h₀ h₁ h₂ h₄)
    · intro fuel more
      let es := PrivateFields.events (w := w) .copy bits
      have crun := pref.execute fuel m more
      simp only [PrivateFields.events_bits, reduceCtorEq, ite_false, List.nil_append] at crun
      change execute M.program (fuel + (headerEvents m f ++ es).length) c m more = _
      rw [List.length_append,
        show fuel + (_ + es.length) = (fuel + es.length) + (headerEvents m f).length by omega,
        head, show execute M.program (fuel + es.length) d m more = _ from crun]
      simp [frameEvents, bits, Option.map_map, Function.comp_def, List.append_assoc]

/-- Convert the three consecutive natural addresses of a fitted frame to native word
addresses. Empty records need no offset equalities. -/
theorem oriented_frame_words (reverse : Bool) (m : Memory w) (f : Word w)
    (n oldOffset newOffset len : ℕ) (hf : f = (n : Word w)) (fit : n + 2 < 2 ^ w)
    (hlen : (m (n + 2)).val = len)
    (offsets : 0 < len → (m n).val = oldOffset ∧ (m (n + 1)).val = newOffset) :
    (m (f + 1 + 1).val).val = len ∧
      (0 < len →
        (if reverse then m (f + 1).val else m f.val).val =
          (if reverse then newOffset else oldOffset) ∧
        (if reverse then m f.val else m (f + 1).val).val =
          (if reverse then oldOffset else newOffset)) := by
  subst f
  have h₀ : (n : Word w).val = n := Nat.mod_eq_of_lt (by omega)
  have h₁ : ((n : Word w) + 1).val = n + 1 := by
    rw [← Nat.cast_add_one]
    exact Nat.mod_eq_of_lt (by omega)
  have h₂ : ((n : Word w) + 1 + 1).val = n + 2 := by
    rw [← Nat.cast_add_one, ← Nat.cast_add_one]
    exact Nat.mod_eq_of_lt fit
  rw [h₀, h₁, h₂]
  refine ⟨hlen, fun positive ↦ ?_⟩
  cases reverse
  · exact offsets positive
  · exact (offsets positive).symm

/-- Reverse a completed source-major frame, copying from its new private field
back into its old private field at the recorded offset. -/
theorem execute_frame (hl : Linked M pc reg (arcPC 0) done)
    (hcopy : PrivateFields.Linked M .copy arcPC (copyRegs reg) done)
    (c : Config w p r) (hc : c.pc = pc 0) (h1 : c.reg (reg 3) = 1)
    {pub : Fin 6 → Word w} {old new : List ℕ} {initial m : Memory w} {completed : ℕ}
    (frames : FramesAt pub old new initial m completed) (a : Fin completed)
    (frameFit : (pub 5).val + 3 * a.val + 2 < 2 ^ w) (src dst : ℕ)
    (hf : c.reg (reg 5) = (((pub 5).val + 3 * a.val : ℕ) : Word w))
    (hs : c.reg (reg 0) = (src : Word w)) (hd : c.reg (reg 2) = (dst : Word w))
    (bs : List Bool) (hlen : bs.length = (sliceAt old new a.val).length)
    (fit : 0 < bs.length → src + (sliceAt old new a.val).targetOffset + bs.length ≤ 2 ^ w ∧
      dst + (sliceAt old new a.val).sourceOffset + bs.length < 2 ^ w)
    (safe : 0 < bs.length →
      dst + (sliceAt old new a.val).sourceOffset ≤ src + (sliceAt old new a.val).targetOffset ∨
      src + (sliceAt old new a.val).targetOffset + bs.length ≤
        dst + (sliceAt old new a.val).sourceOffset)
    (data : ∀ i : Fin bs.length,
      c.privateMem ((src + (sliceAt old new a.val).targetOffset + i.val : ℕ) : Word w) =
        PrivateFields.bitValue w bs[i.val]) :
    FrameResult M reg done c m (c.reg (reg 5)) (dst + (sliceAt old new a.val).sourceOffset) bs := by
  let s := sliceAt old new a.val
  obtain ⟨len, off⟩ := oriented_frame_words true m (c.reg (reg 5))
    ((pub 5).val + 3 * a.val) s.sourceOffset s.targetOffset bs.length hf frameFit
    ((frames.lengths a.val a.isLt).trans hlen.symm)
    (fun hp ↦ frames.offsets a.val a.isLt (hlen ▸ hp))
  exact execute_stored_frame true hl hcopy c hc h1 m (c.reg (reg 5)) rfl src dst
    s.targetOffset s.sourceOffset hs hd bs len off fit safe data

end PairSimulation.ReverseSlices

end VPVNP
end Computability
end OAI
