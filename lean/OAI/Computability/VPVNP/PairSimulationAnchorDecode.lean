import OAI.Computability.VPVNP.PairSimulationSelectorLookupClock

/-!
# Native scan of the anchor's selector sequence

A vertex call reads selectors from the high end of the anchor wire and
writes each decoded ordinal in its original copy position. Its control
table is independent of the repetition count. The output cells may be on
either side of the input slice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.AnchorDecode

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM MotifEntry
open scoped Fin.CommRing

variable {X : Type*} {w p r k b payload u : ℕ}

private abbrev word (w n : ℕ) : Word w := (n : Word w)

private theorem val_word {n : ℕ} (h : n < 2 ^ w) : (word w n).val = n := Nat.mod_eq_of_lt h

/-- The first six registers of the loop belong to the padded field reader. -/
def fieldRegs (reg : Fin 9 ↪ Fin r) : Fin 6 ↪ Fin r :=
  (Fin.castLEEmb (by decide : 6 ≤ 9)).trans reg

/-- Registers 6 and 7 are the descending output cursor and its lower bound.
Register 8 contains the fixed selector width. -/
structure Program (X : Type*) (p r k : ℕ) where
  /-- Selectors in the order tested by the lookup. -/
  xs : List X
  /-- Public port of each selector's encoded tag. -/
  key : X → Fin k
  /-- Public port of the ordinal stored after a successful lookup. -/
  name : X → Fin k
  /-- Nine registers for the reader, cursor pair and selector width. -/
  reg : Fin 9 ↪ Fin r
  /-- Control locations for the five outer loop instructions. -/
  pc : Fin 5 → Fin p
  /-- Control locations of the padded bit-field reader. -/
  reader : Fin 7 → Fin p
  /-- Physical location of each instruction in the fixed lookup table. -/
  label : (ReadDecode.selectorFlow xs key name (fieldRegs reg) (reg 0)).Label → Fin p
  /-- Continuation after all selectors have been written. -/
  done : Fin p
  /-- Failure continuation for an unused selector code. -/
  bad : Fin p

namespace Program

variable (P : Program X p r k)

/-- Lookup flow for the field reader's raw tag. -/
def selector := ReadDecode.selectorFlow P.xs P.key P.name (fieldRegs P.reg) (P.reg 0)

/-- Test the cursor, prepare the descending field read, and store its ordinal. -/
def instruction : Fin 5 → Instr w p r k :=
  ![.jumpEq (P.reg 6) (P.reg 7) P.done (P.pc 1),
    .binary .sub (P.reg 6) (P.reg 6) (P.reg 4) (P.pc 2),
    .binary .sub (P.reg 2) (P.reg 1) (P.reg 8) (P.pc 3),
    .constant (P.reg 0) 0 (P.reader 0), .storePrivate (P.reg 6) (P.reg 0) (P.pc 0)]

theorem resize_instruction (i : Fin 5) :
    (P.instruction (w := 1) i).resize w = P.instruction i := by fin_cases i <;> rfl

/-- All links for the five outer rows, the padded reader and the fixed selector table. -/
structure Linked (M : Machine w p r k) : Prop where
  outer : ∀ i, M.code (P.pc i) = P.instruction i
  reader : FieldRead.Linked M P.reader (fieldRegs P.reg) (P.label P.selector.entry)
  lookup : Flow.Linked M P.selector P.label (P.pc 4) P.bad

/-- Input register and private slice invariant with n remaining copies. -/
structure Ready (bits : Fin (payload + u * b) → Bool) (base dest n : ℕ)
    (c : Config w p r) : Prop where
  pc : c.pc = P.pc 0
  cursor : c.reg (P.reg 1) = word w (base + (payload + b * n))
  dataEnd : c.reg (P.reg 3) = word w (base + (payload + u * b))
  one : c.reg (P.reg 4) = 1
  output : c.reg (P.reg 6) = word w (dest + n)
  stop : c.reg (P.reg 7) = word w dest
  width : c.reg (P.reg 8) = word w b
  data : ∀ i : Fin (payload + u * b),
    c.privateMem (word w (base + i.val)) = encodeBit w (bits i)

/-- Only the designated scratch registers and output interval may change. -/
structure Frame (dest n : ℕ) (c d : Config w p r) : Prop where
  regs : ∀ a, a ≠ P.reg 0 → a ≠ P.reg 1 → a ≠ P.reg 2 → a ≠ P.reg 5 → a ≠ P.reg 6 →
    d.reg a = c.reg a
  memory : ∀ a : Word w, a.val < dest ∨ dest + n ≤ a.val → d.privateMem a = c.privateMem a
  persistent : d.persistent = c.persistent

/-- The partial scan either decoded all remaining positions, or hit a
particular unused selector code. -/
def Outcome (M : Machine w p r k) (code : X ↪ Word b) (bits : Fin (payload + u * b) → Bool)
    (dest n : ℕ) (d : Config w p r) : Prop :=
  (d.pc = P.done ∧ ∀ i : Fin u, i.val < n → ∃ x,
    decode P.xs code (readTag bits i) = some x ∧
      d.privateMem (word w (dest + i.val)) = M.publicData (P.name x)) ∨
  (d.pc = P.bad ∧ ∃ i : Fin u, i.val < n ∧ decode P.xs code (readTag bits i) = none)

variable {P} {M : Machine w p r k}

private theorem step_at (link : P.Linked M) (i : Fin 5) {c : Config w p r} (hc : c.pc = P.pc i) :
    M.program.step c = (P.instruction i).run M.publicData c := by
  simp [Machine.program, hc, link.outer i]

private theorem prepare (link : P.Linked M) (bits : Fin (payload + u * b) → Bool)
    (base dest n : ℕ) (c : Config w p r) (h : P.Ready bits base dest (n + 1) c)
    (hd : dest + (n + 1) < 2 ^ w) :
    ∃ start, Prefix M c (List.replicate 4 .tick) start ∧ start.pc = P.reader 0 ∧
      start.reg (P.reg 0) = 0 ∧ start.reg (P.reg 2) = word w (base + (payload + b * n)) ∧
      start.reg (P.reg 6) = word w (dest + n) ∧
      (∀ a, a ≠ P.reg 0 → a ≠ P.reg 2 → a ≠ P.reg 6 → start.reg a = c.reg a) ∧
      start.privateMem = c.privateMem ∧ start.persistent = c.persistent := by
  let c₁ := {c with pc := P.pc 1}
  let c₂ := c₁.put (P.pc 2) (P.reg 6) (word w (dest + n))
  let c₃ := c₂.put (P.pc 3) (P.reg 2) (word w (base + (payload + b * n)))
  let start := c₃.put (P.reader 0) (P.reg 0) 0
  have ne : c.reg (P.reg 6) ≠ c.reg (P.reg 7) := by
    rw [h.output, h.stop]
    intro he
    have hv := congrArg Fin.val he
    rw [val_word hd, val_word (by omega : dest < 2 ^ w)] at hv
    omega
  have s₀ : M.program.step c = .localStep c₁ := by
    rw [step_at link 0 h.pc]
    simp [instruction, Instr.run, ne, c₁]
  have s₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step_at link 1 rfl]
    change CallAction.localStep (c₁.put (P.pc 2) (P.reg 6) (c.reg (P.reg 6) - c.reg (P.reg 4))) = _
    simp [c₂, h.output, h.one, word, ← add_assoc]
  have s₂ : M.program.step c₂ = .localStep c₃ := by
    rw [step_at link 2 rfl]
    change CallAction.localStep
      (c₂.put (P.pc 3) (P.reg 2) (c₂.reg (P.reg 1) - c₂.reg (P.reg 8))) = _
    simp [c₃, c₂, c₁, Config.put, h.cursor, h.width, Nat.mul_succ, word, ← add_assoc]
  have s₃ : M.program.step c₃ = .localStep start := step_at link 3 rfl
  refine ⟨_, .tick s₀ (.tick s₁ (.tick s₂ (.tick s₃ (.nil _)))), rfl, by simp [start],
    by simp [start, c₃, Config.put], by simp [start, c₃, c₂, Config.put], ?_, rfl, rfl⟩
  intro a h₀ h₂ h₆
  simp [start, c₃, c₂, c₁, Config.put, Function.update_of_ne, h₀, h₂, h₆]

/-- Native bound for the control, reading, decoding and store of one anchor copy. -/
def visitCap (P : Program X p r k) (b : ℕ) := (6 * b + 1) + (2 * P.xs.length + 1) + 5

private theorem iteration (link : P.Linked M) (fits : b ≤ w) (code : X ↪ Word b)
    (hk : ∀ x, M.publicData (P.key x) = MapLookup.widen fits (code x))
    (bits : Fin (payload + u * b) → Bool) (base dest : ℕ) (i : Fin u)
    (c : Config w p r) (ready : P.Ready bits base dest (i.val + 1) c)
    (hi : base + (payload + u * b) < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : base + (payload + u * b) ≤ dest ∨ dest + u ≤ base) :
    ∃ ticks d, ticks ≤ P.visitCap b ∧ Prefix M c (List.replicate ticks .tick) d ∧
      P.Frame (dest + i.val) 1 c d ∧
      ((decode P.xs code (readTag bits i) = none ∧ d.pc = P.bad) ∨
       (∃ x, decode P.xs code (readTag bits i) = some x ∧ P.Ready bits base dest i.val d ∧
         d.privateMem (word w (dest + i.val)) = M.publicData (P.name x) ∧
         ticks = 5 + ((6*b+1) + MapLookup.selectorTicks code (readTag bits i) P.xs))) := by
  have hit := i.isLt
  obtain ⟨start, prep, hs, hz, hl, ho, rest, hm, hp⟩ :=
    prepare link bits base dest i.val c ready (by omega)
  let fr := fieldRegs P.reg
  have hh : start.reg (fr 1) = word w (base + (payload + b * i.val) + b) := by
    change start.reg (P.reg 1) = _
    rw [rest, ready.cursor, Nat.mul_succ, Nat.add_assoc, Nat.add_assoc] <;> simp
  have de : start.reg (fr 3) = word w (base + (payload + u * b)) := by
    change start.reg (P.reg 3) = _
    rw [rest, ready.dataEnd] <;> simp
  have one : start.reg (fr 4) = 1 := by
    change start.reg (P.reg 4) = _
    rw [rest, ready.one] <;> simp
  let t := (6*b+1) + MapLookup.selectorTicks code (readTag bits i) P.xs
  have bound : t ≤ (6*b+1) + (2*P.xs.length+1) :=
    Nat.add_le_add_left (MapLookup.selectorTicks_le ..) _
  obtain ⟨mid, run, exit, cur, keep, mem, pers⟩ :=
    ReadDecode.native_tag_exact M P.reader fr (P.reg 0) (P.reg.injective.ne (by decide))
      P.xs code P.key P.name fits hk P.label (P.pc 4) P.bad link.reader link.lookup
      bits base i start hs hi hz hh hl de one (hm ▸ ready.data)
  have pre : Prefix M c (List.replicate (4 + t) .tick) mid := by
    rw [List.replicate_add]
    exact prep.append run
  have regKeep (a : Fin r) (h₀ : a ≠ P.reg 0) (h₁ : a ≠ P.reg 1)
      (h₂ : a ≠ P.reg 2) (h₅ : a ≠ P.reg 5) (h₆ : a ≠ P.reg 6) : mid.reg a = c.reg a :=
    (keep a h₀ h₁ h₅ h₀).trans (rest a h₀ h₂ h₆)
  have memEq := mem.trans hm
  have perEq := pers.trans hp
  cases hx : decode P.xs code (readTag bits i) with
  | none =>
    rw [hx] at exit
    exact ⟨_, _, by unfold visitCap; omega, pre,
      ⟨regKeep, fun a _ ↦ congrFun memEq a, perEq⟩, Or.inl ⟨rfl, exit⟩⟩
  | some x =>
    rw [hx] at exit
    obtain ⟨pcStore, ordinal⟩ := exit
    have addr : mid.reg (P.reg 6) = word w (dest + i.val) :=
      (keep _ (P.reg.injective.ne (by decide)) (P.reg.injective.ne (by decide))
        (P.reg.injective.ne (by decide)) (P.reg.injective.ne (by decide))).trans ho
    let d := mid.store (P.pc 0) (word w (dest + i.val)) (M.publicData (P.name x))
    have store : M.program.step mid = .localStep d := by
      rw [step_at link 4 pcStore]
      change CallAction.localStep (mid.store (P.pc 0) (mid.reg (P.reg 6)) (mid.reg (P.reg 0))) = _
      rw [addr, ordinal]
    have away (a : Word w) (ha : a.val < dest + i.val ∨ dest + i.val + 1 ≤ a.val) :
        d.privateMem a = c.privateMem a := by
      have ha' : a ≠ word w (dest + i.val) := by
        intro he
        have hv := congrArg Fin.val he
        rw [val_word (by omega : dest + i.val < 2 ^ w)] at hv
        omega
      exact (Config.store_other mid (P.pc 0) (word w (dest + i.val)) a _ ha').trans
        (congrFun memEq a)
    refine ⟨4 + t + 1, d, by unfold visitCap; omega, ?_, ⟨regKeep, away, perEq⟩,
      Or.inr ⟨x, rfl, ?_, Config.store_same .., by unfold t; omega⟩⟩
    · rw [List.replicate_add]
      exact pre.append (.tick store (.nil _))
    · refine ⟨rfl, cur, ?_, ?_, addr, ?_, ?_, ?_⟩
      · exact (regKeep _ (by simp) (by simp) (by simp) (by simp) (by simp)).trans ready.dataEnd
      · exact (regKeep _ (by simp) (by simp) (by simp) (by simp) (by simp)).trans ready.one
      · exact (regKeep _ (by simp) (by simp) (by simp) (by simp) (by simp)).trans ready.stop
      · exact (regKeep _ (by simp) (by simp) (by simp) (by simp) (by simp)).trans ready.width
      · intro j
        have hj := j.isLt
        have hval : (word w (base + j.val)).val = base + j.val := val_word (by omega)
        exact (away _ (by rw [hval]; omega)).trans (ready.data j)

/-- The physical loop scans the remaining n slots. A successful suffix is
kept in its original positions while the lower-index slots are filled. -/
theorem loop (link : P.Linked M) (fits : b ≤ w) (code : X ↪ Word b)
    (hk : ∀ x, M.publicData (P.key x) = MapLookup.widen fits (code x))
    (bits : Fin (payload + u * b) → Bool) (base dest n : ℕ) (hn : n ≤ u)
    (c : Config w p r) (ready : P.Ready bits base dest n c)
    (hi : base + (payload + u * b) < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : base + (payload + u * b) ≤ dest ∨ dest + u ≤ base) :
    ∃ ticks d, ticks ≤ P.visitCap b * n + 1 ∧ Prefix M c (List.replicate ticks .tick) d ∧
      P.Frame dest n c d ∧ P.Outcome M code bits dest n d := by
  induction n generalizing c with
  | zero =>
    let d := {c with pc := P.done}
    have eq : c.reg (P.reg 6) = c.reg (P.reg 7) := ready.output.trans ready.stop.symm
    have hs : M.program.step c = .localStep d := by
      rw [step_at link 0 ready.pc]
      simp [instruction, Instr.run, eq, d]
    exact ⟨1, d, by simp, .tick hs (.nil _), ⟨fun _ _ _ _ _ _ ↦ rfl, fun _ _ ↦ rfl, rfl⟩,
      Or.inl ⟨rfl, fun i h ↦ (Nat.not_lt_zero i.val h).elim⟩⟩
  | succ n ih =>
    let i : Fin u := ⟨n, hn⟩
    obtain ⟨t, mid, bound, pre, frame, result⟩ :=
      iteration link fits code hk bits base dest i c ready hi hd sep
    rcases result with ⟨invalid, bad⟩ | ⟨x, ok, next, value, _⟩
    · refine ⟨t, mid, ?_, pre, ⟨frame.regs, ?_, frame.persistent⟩,
        Or.inr ⟨bad, i, by simp [i], invalid⟩⟩
      · rw [Nat.mul_succ]
        omega
      · intro a ha
        apply frame.memory
        change a.val < dest + n ∨ dest + n + 1 ≤ a.val
        omega
    · obtain ⟨s, d, budget, tail, frame', result'⟩ := ih (by omega) mid next
      refine ⟨t + s, d, ?_, ?_, ?_, ?_⟩
      · rw [Nat.mul_succ]
        omega
      · rw [List.replicate_add]
        exact pre.append tail
      · refine ⟨fun a h₀ h₁ h₂ h₅ h₆ ↦ (frame'.regs a h₀ h₁ h₂ h₅ h₆).trans
            (frame.regs a h₀ h₁ h₂ h₅ h₆), ?_, frame'.persistent.trans frame.persistent⟩
        intro a ha
        exact (frame'.memory a (by omega)).trans
          (frame.memory a (by change a.val < dest + n ∨ dest + n + 1 ≤ a.val; omega))
      · rcases result' with ⟨done, values⟩ | ⟨bad, j, hj, invalid⟩
        · refine Or.inl ⟨done, fun j hj ↦ ?_⟩
          by_cases he : j = i
          · subst j
            refine ⟨x, ok, (frame'.memory _ (Or.inr ?_)).trans value⟩
            rw [val_word (by change dest + n < 2 ^ w; omega)]
          · have hj' : j.val ≠ n := fun h ↦ he (Fin.ext h)
            exact values j (by omega)
        · exact Or.inr ⟨bad, j, by omega, invalid⟩

/-- Every decoded ordinal is available at dest+i when the complete anchor
sequence is valid. An unused code transfers control to the bad exit. The
cap also holds for a rejection partway through the scan. -/
theorem native (link : P.Linked M) (fits : b ≤ w) (code : X ↪ Word b)
    (hk : ∀ x, M.publicData (P.key x) = MapLookup.widen fits (code x))
    (bits : Fin (payload + u * b) → Bool) (base dest : ℕ)
    (c : Config w p r) (ready : P.Ready bits base dest u c)
    (hi : base + (payload + u * b) < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : base + (payload + u * b) ≤ dest ∨ dest + u ≤ base) :
    ∃ ticks d, ticks ≤ P.visitCap b * u + 1 ∧ Prefix M c (List.replicate ticks .tick) d ∧
      P.Frame dest u c d ∧
      (match selectors? P.xs code (readTag bits) with
       | none => d.pc = P.bad
       | some θ => d.pc = P.done ∧
         ∀ i, d.privateMem (word w (dest + i.val)) = M.publicData (P.name (θ i))) := by
  obtain ⟨t, d, bound, pre, frame, result⟩ :=
    loop link fits code hk bits base dest u le_rfl c ready hi hd sep
  refine ⟨t, d, bound, pre, frame, ?_⟩
  rcases result with ⟨done, readback⟩ | ⟨bad, i, _, invalid⟩
  · choose θ dec val using fun i : Fin u ↦ readback i i.isLt
    have hs : selectors? P.xs code (readTag bits) = some θ := by
      simp [selectors?, Vector.getElem_ofFn, dec]
    rw [hs]
    exact ⟨done, val⟩
  · have hs : selectors? P.xs code (readTag bits) = none := by
      simp only [selectors?, Vector.getElem_ofFn]
      apply dite_eq_right
      intro h
      have hh := h i
      simp [invalid] at hh
    rw [hs]
    exact bad

/-- An invalid sequence rejects the genuine interpreter on every branch
stream, for every amount of fuel. -/
theorem native_reject (link : P.Linked M) (fits : b ≤ w) (code : X ↪ Word b)
    (hk : ∀ x, M.publicData (P.key x) = MapLookup.widen fits (code x))
    (bits : Fin (payload + u * b) → Bool) (base dest : ℕ)
    (c : Config w p r) (ready : P.Ready bits base dest u c)
    (hi : base + (payload + u * b) < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : base + (payload + u * b) ≤ dest ∨ dest + u ≤ base)
    (invalid : selectors? P.xs code (readTag bits) = none) (hb : M.code P.bad = .reject)
    (fuel : ℕ) (mem : Memory w) (bs : List Bool) : execute M.program fuel c mem bs = none := by
  obtain ⟨_, _, _, pre, _, endPC⟩ := native link fits code hk bits base dest c ready hi hd sep
  rw [invalid] at endPC
  exact MapLookup.reject_after_ticks pre (fun e he ↦ List.eq_of_mem_replicate he)
    (endPC ▸ hb) fuel mem bs

end Program
end PairSimulation.AnchorDecode

end VPVNP
end Computability
end OAI
