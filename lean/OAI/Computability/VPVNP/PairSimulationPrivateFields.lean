import OAI.Computability.VPVNP.PairSimulationHistory
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Private bit fields in a final-site call

A guess writes each consumed branch bit to one private word. A copy uses the
same storage order and takes each bit from an existing private slice. The two
fragments accept arbitrary program labels and leave the external memory and
the registers of the enclosing traversal available to their continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.PrivateFields

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Source of the bits written to a private field. Guess mode consumes branch bits and copy
mode loads an existing private slice. -/
inductive Mode
  | guess | copy
  deriving DecidableEq

private abbrev word (w n : ℕ) : Word w := (n : Word w)
private theorem val_word {n : ℕ} (hn : n < 2^w) : (word w n).val = n := Nat.mod_eq_of_lt hn

/-- Each private cell holds the word zero or one. -/
def bitValue (w : ℕ) (b : Bool) : Word w := if b then 1 else 0

/-- Registers are source cursor, exclusive destination end, destination
cursor, one and temporary. Only the two cursors and the temporary are written. -/
def instruction (mode : Mode) (pc : Fin 7 → Fin p) (reg : Fin 5 ↪ Fin r) (done : Fin p) :
    Fin 7 → Instr w p r k :=
  ![.jumpEq (reg 2) (reg 1) done (pc 1),
    (match mode with | .guess => .choose (pc 2) (pc 3) | .copy => .loadPrivate (reg 4) (reg 0) (pc 4)),
    .constant (reg 4) 1 (pc 4), .constant (reg 4) 0 (pc 4),
    .storePrivate (reg 2) (reg 4) (pc 5), .binary .add (reg 2) (reg 2) (reg 3) (pc 6),
    .binary .add (reg 0) (reg 0) (reg 3) (pc 0)]

theorem resize_instruction (mode : Mode) (pc : Fin 7 → Fin p) (reg : Fin 5 ↪ Fin r)
    (done : Fin p) (i : Fin 7) :
    (instruction (w := 1) (k := k) mode pc reg done i).resize w = instruction mode pc reg done i := by
  cases mode <;> fin_cases i <;> rfl

/-- The machine contains the seven instructions of the selected guess or copy loop at the
specified labels, with the given registers and continuation. -/
def Linked (M : Machine w p r k) (mode : Mode) (pc : Fin 7 → Fin p) (reg : Fin 5 ↪ Fin r)
    (done : Fin p) : Prop := ∀ i, M.code (pc i) = instruction mode pc reg done i

/-- A private-memory slice in increasing physical-address order. -/
def storeBits (dst : ℕ) : List Bool → (Word w → Word w) → Word w → Word w
  | [], old => old
  | b :: bs, old => storeBits (dst+1) bs (Function.update old (word w dst) (bitValue w b))

theorem storeBits_outside (dst : ℕ) (bs : List Bool) (old : Word w → Word w) (a : Word w)
    (fit : dst+bs.length ≤ 2^w) (outside : a.val < dst ∨ dst+bs.length ≤ a.val) :
    storeBits dst bs old a = old a := by
  induction bs generalizing dst old with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons] at fit outside
    rw [storeBits, ih _ _ (by omega) (by omega)]
    apply Function.update_of_ne
    intro he
    have h := congrArg Fin.val he
    rw [val_word (by omega : dst < 2^w)] at h
    omega

theorem storeBits_read (dst : ℕ) (bs : List Bool) (old : Word w → Word w)
    (fit : dst+bs.length ≤ 2^w) (i : Fin bs.length) :
    storeBits dst bs old (word w (dst+i.val)) = bitValue w bs[i.val] := by
  induction bs generalizing dst old with
  | nil => exact i.elim0
  | cons b bs ih =>
    have hfit : dst+bs.length+1 ≤ 2^w := by simpa [Nat.add_assoc] using fit
    induction i using Fin.cases with
    | zero =>
      change storeBits (dst+1) bs (Function.update old (word w dst) (bitValue w b)) (word w dst) = _
      rw [storeBits_outside _ _ _ _ (by omega) (.inl (by rw [val_word (by omega)]; omega))]
      exact Function.update_self ..
    | succ i =>
      simpa [storeBits, Nat.add_assoc, Nat.add_comm 1] using ih (dst+1) _ (by omega) i

private def headEvents (mode : Mode) (b : Bool) : List (Event w) :=
  match mode with
  | .guess => [.tick, .choice b, .tick]
  | .copy => [.tick, .tick]

/-- The exact local trace, including the final range test. -/
def events (mode : Mode) : List Bool → List (Event w)
  | [] => [.tick]
  | b :: bs => (headEvents mode b ++ [.tick,.tick,.tick]) ++ events mode bs

theorem events_bits (mode : Mode) (bs : List Bool) :
    choiceBits (events (w := w) mode bs) = if mode = .guess then bs else [] := by
  cases mode <;> induction bs with
  | nil => rfl
  | cons b bs ih => simp [events, headEvents, choiceBits, ih]

theorem events_work (mode : Mode) (bs : List Bool) :
    (events (w := w) mode bs).length = (if mode = .guess then 6 else 5)*bs.length+1 ∧
      countProbes (events (w := w) mode bs) = 0 := by
  cases mode <;> induction bs with
  | nil => exact ⟨rfl,rfl⟩
  | cons b bs ih => simp [events, headEvents, countProbes, ih.1, ih.2]; omega

variable {M : Machine w p r k} {mode : Mode} {pc : Fin 7 → Fin p} {reg : Fin 5 ↪ Fin r} {done : Fin p}

private theorem step_at (hl : Linked M mode pc reg done) (i : Fin 7) (c : Config w p r)
    (hc : c.pc = pc i) : M.program.step c = (instruction mode pc reg done i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

/-- Exact state transition for one bit. The copy reads its value before
either cursor advances. -/
private theorem iteration (hl : Linked M mode pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (b : Bool) (h1 : c.reg (reg 3) = 1) (hne : c.reg (reg 2) ≠ c.reg (reg 1))
    (hload : mode = .copy → c.privateMem (c.reg (reg 0)) = bitValue w b) :
    ∃ out, Prefix M c (headEvents mode b ++ [.tick,.tick,.tick]) out ∧ out.pc = pc 0 ∧
      out.reg (reg 0) = c.reg (reg 0) + 1 ∧ out.reg (reg 2) = c.reg (reg 2) + 1 ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j) ∧
      out.privateMem = Function.update c.privateMem (c.reg (reg 2)) (bitValue w b) ∧
      out.persistent = c.persistent := by
  let c₁ := {c with pc := pc 1}
  let loaded := c.put (pc 4) (reg 4) (bitValue w b)
  let stored := loaded.store (pc 5) (c.reg (reg 2)) (bitValue w b)
  let next := stored.put (pc 6) (reg 2) (c.reg (reg 2) + 1)
  let out := next.put (pc 0) (reg 0) (c.reg (reg 0) + 1)
  have s₀ : M.program.step c = .localStep c₁ := by
    rw [step_at hl 0 c hc]
    simp [instruction, Instr.run, hne, c₁]
  have pre : Prefix M c (headEvents mode b) loaded := by
    cases mode with
    | copy =>
      refine .tick s₀ (.tick ?_ (.nil _))
      rw [step_at hl 1 c₁ rfl]
      change CallAction.localStep (c.put (pc 4) (reg 4) (c.privateMem (c.reg (reg 0)))) = _
      rw [hload rfl]
    | guess =>
      have s₁ : M.program.step c₁ = .branch (fun b ↦ {c₁ with pc := if b then pc 2 else pc 3}) :=
        step_at hl 1 c₁ rfl
      cases b with
      | false => exact .tick s₀ (.choice (b := false) s₁ (.tick (step_at hl 3 _ rfl) (.nil _)))
      | true => exact .tick s₀ (.choice (b := true) s₁ (.tick (step_at hl 2 _ rfl) (.nil _)))
  have s₄ : M.program.step loaded = .localStep stored := by
    rw [step_at hl 4 loaded rfl]
    simp [instruction, Instr.run, loaded, stored, Config.put]
  have s₅ : M.program.step stored = .localStep next := by
    rw [step_at hl 5 stored rfl]
    simp [instruction, Instr.run, next, stored, loaded, Config.store, Config.put, BinaryOp.eval, h1]
  have s₆ : M.program.step next = .localStep out := by
    rw [step_at hl 6 next rfl]
    simp [instruction, Instr.run, out, next, stored, loaded, Config.store, Config.put, BinaryOp.eval, h1]
  refine ⟨out, pre.append (.tick s₄ (.tick s₅ (.tick s₆ (.nil _)))), rfl, by simp [out],
    by simp [out, next, Config.put], ?_, rfl, rfl⟩
  intro j h₀ h₂ h₄
  simp [out, next, stored, loaded, Config.store, Config.put, Function.update_of_ne h₀,
    Function.update_of_ne h₂, Function.update_of_ne h₄]

/-- The frame and exit data shared by guessing and copying. -/
structure Result (reg : Fin 5 ↪ Fin r) (done : Fin p) (c out : Config w p r)
    (src dst : ℕ) (bs : List Bool) : Prop where
  pc : out.pc = done
  source : out.reg (reg 0) = word w (src+bs.length)
  destination : out.reg (reg 2) = word w (dst+bs.length)
  frame : ∀ j, j ≠ reg 0 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j
  privateMem : out.privateMem = storeBits dst bs c.privateMem
  persistent : out.persistent = c.persistent

private theorem field_loop (hl : Linked M mode pc reg done) (c : Config w p r)
    (hc : c.pc = pc 0) (src dst : ℕ) (bs : List Bool) (hs : c.reg (reg 0) = word w src)
    (hd : c.reg (reg 2) = word w dst) (he : c.reg (reg 1) = word w (dst+bs.length))
    (hone : c.reg (reg 3) = 1) (fit : dst+bs.length < 2^w)
    (safe : mode = .copy → src+bs.length ≤ 2^w ∧ (dst ≤ src ∨ src+bs.length ≤ dst))
    (data : mode = .copy → ∀ i : Fin bs.length, c.privateMem (word w (src+i.val)) = bitValue w bs[i.val]) :
    ∃ out, Prefix M c (events mode bs) out ∧ Result reg done c out src dst bs := by
  induction bs generalizing c src dst with
  | nil =>
    let out := {c with pc := done}
    have eq : c.reg (reg 2) = c.reg (reg 1) := hd.trans he.symm
    have s : M.program.step c = .localStep out := by
      rw [step_at hl 0 c hc]
      simp [instruction, Instr.run, eq, out]
    exact ⟨out, .tick s (.nil _), rfl, hs, hd, fun _ _ _ _ ↦ rfl, rfl, rfl⟩
  | cons b bs ih =>
    have hlen : dst+1+bs.length = dst+(b::bs).length := by simp; omega
    have neq : c.reg (reg 2) ≠ c.reg (reg 1) := by
      rw [hd, he]
      intro h
      have e := congrArg Fin.val h
      rw [val_word (by simp at fit; omega : dst < 2^w), val_word fit] at e
      simp at e
    have hload (h : mode = .copy) : c.privateMem (c.reg (reg 0)) = bitValue w b := by
      simpa [hs] using data h 0
    obtain ⟨next, pre, hn, hsrc, hdst, hframe, hmem, hp⟩ := iteration hl c hc b hone neq hload
    have hs' : next.reg (reg 0) = word w (src+1) := by simp [hsrc, hs, word]
    have hd' : next.reg (reg 2) = word w (dst+1) := by simp [hdst, hd, word]
    have keep (j : Fin 5) (h₀ : j ≠ 0) (h₂ : j ≠ 2) (h₄ : j ≠ 4) :
        next.reg (reg j) = c.reg (reg j) :=
      hframe _ (reg.injective.ne h₀) (reg.injective.ne h₂) (reg.injective.ne h₄)
    have data' (h : mode = .copy) (i : Fin bs.length) :
        next.privateMem (word w (src+1+i.val)) = bitValue w bs[i.val] := by
      have hsafe := safe h
      have hi := i.isLt
      have hfit : src+1+i.val < 2^w := by simp only [List.length_cons] at hsafe; omega
      have hne : word w (src+1+i.val) ≠ word w dst := by
        intro eq
        have e := congrArg Fin.val eq
        rw [val_word hfit, val_word (by simp at fit; omega)] at e
        simp only [List.length_cons] at hsafe
        omega
      rw [hmem, hd, Function.update_of_ne hne]
      simpa [Nat.add_assoc, Nat.add_comm 1] using data h ⟨i.val+1, by simp⟩
    obtain ⟨out, tail, result⟩ := ih next hn (src+1) (dst+1) hs' hd'
      ((keep 1 (by decide) (by decide) (by decide)).trans (hlen ▸ he))
      ((keep 3 (by decide) (by decide) (by decide)).trans hone)
      (hlen ▸ fit) (fun h ↦ by have hh := safe h; simp only [List.length_cons] at hh; omega) data'
    refine ⟨out, pre.append tail, result.pc, ?_, ?_, ?_, ?_, result.persistent.trans hp⟩
    · simpa [Nat.add_assoc, Nat.add_comm 1] using result.source
    · simpa [hlen] using result.destination
    · intro j h₀ h₂ h₄
      exact (result.frame j h₀ h₂ h₄).trans (hframe j h₀ h₂ h₄)
    · rw [result.privateMem, hmem, hd, storeBits]

/-- One fresh binary branch for each field bit, in address order. -/
theorem guess_prefix (hl : Linked M .guess pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (dst : ℕ) (bs : List Bool) (hd : c.reg (reg 2) = word w dst)
    (he : c.reg (reg 1) = word w (dst+bs.length)) (hone : c.reg (reg 3) = 1)
    (fit : dst+bs.length < 2^w) :
    ∃ out, Prefix M c (events .guess bs) out ∧ Result reg done c out (c.reg (reg 0)).val dst bs :=
  field_loop hl c hc _ dst bs (Fin.ext (Nat.mod_eq_of_lt (c.reg (reg 0)).isLt).symm)
    hd he hone fit (by simp) (by simp)

/-- A private-to-private forward slice copy. The permitted overlap includes
the identical slice and moving the slice toward lower addresses. -/
theorem copy_prefix (hl : Linked M .copy pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (src dst : ℕ) (bs : List Bool) (hs : c.reg (reg 0) = word w src)
    (hd : c.reg (reg 2) = word w dst) (he : c.reg (reg 1) = word w (dst+bs.length))
    (hone : c.reg (reg 3) = 1) (fit : dst+bs.length < 2^w) (hsrc : src+bs.length ≤ 2^w)
    (safe : dst ≤ src ∨ src+bs.length ≤ dst)
    (data : ∀ i : Fin bs.length, c.privateMem (word w (src+i.val)) = bitValue w bs[i.val]) :
    ∃ out, Prefix M c (events .copy bs) out ∧ Result reg done c out src dst bs :=
  field_loop hl c hc src dst bs hs hd he hone fit (fun _ ↦ ⟨hsrc,safe⟩) (fun _ ↦ data)

/-- The abstract reader serializes the bits in exactly the native store order. -/
theorem bitField_encode {n : ℕ} (f : Fin n → Bool) :
    (LocalHistory.bitField n).encode f = List.ofFn f := by
  let x := (RAMSerialization.wordBits n).symm f
  change List.ofFn (RAMSerialization.wordBits n (Fin.ofNat _ x.val)) = _
  rw [show Fin.ofNat (2^n) x.val = x from Fin.ext (Nat.mod_eq_of_lt x.isLt)]
  exact congrArg List.ofFn ((RAMSerialization.wordBits n).apply_symm_apply f)

/-- Exact suffix, fuel, stored bits and frame when reading one field of a
compression kernel. The enclosing vertex may immediately read its next field. -/
theorem execute_guess (hl : Linked M .guess pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (dst n : ℕ) (hd : c.reg (reg 2) = word w dst) (he : c.reg (reg 1) = word w (dst+n))
    (hone : c.reg (reg 3) = 1) (fit : dst+n < 2^w) (f : Fin n → Bool) :
    ∃ out, Result reg done c out (c.reg (reg 0)).val dst (List.ofFn f) ∧
      (∀ i : Fin n, out.privateMem (word w (dst+i.val)) = bitValue w (f i)) ∧
      ∀ fuel mem tail, execute M.program (fuel+(6*n+1)) c mem ((LocalHistory.bitField n).encode f ++ tail) =
        (execute M.program fuel out mem tail).map (fun rep ↦ ⟨events .guess (List.ofFn f) ++ rep.events, rep.result⟩) := by
  obtain ⟨out, pref, res⟩ := guess_prefix hl c hc dst (List.ofFn f) hd (by simpa using he)
    hone (by simpa using fit)
  refine ⟨out, res, ?_, ?_⟩
  · intro i
    rw [res.privateMem]
    simpa using storeBits_read dst (List.ofFn f) c.privateMem (by simpa using fit.le)
      ⟨i.val, by simp⟩
  · intro fuel mem tail
    simpa [events_bits, (events_work .guess (w := w) (List.ofFn f)).1, bitField_encode] using pref.execute fuel mem tail

/-- A copy has no branch bits or external probes and takes five local
steps per bit plus the final test. -/
theorem execute_copy (hl : Linked M .copy pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (src dst : ℕ) (bs : List Bool) (hs : c.reg (reg 0) = word w src)
    (hd : c.reg (reg 2) = word w dst) (he : c.reg (reg 1) = word w (dst+bs.length))
    (hone : c.reg (reg 3) = 1) (fit : dst+bs.length < 2^w) (hsrc : src+bs.length ≤ 2^w)
    (safe : dst ≤ src ∨ src+bs.length ≤ dst)
    (data : ∀ i : Fin bs.length, c.privateMem (word w (src+i.val)) = bitValue w bs[i.val]) :
    ∃ out, Result reg done c out src dst bs ∧ ∀ fuel mem tail,
      execute M.program (fuel+(5*bs.length+1)) c mem tail =
        (execute M.program fuel out mem tail).map (fun rep ↦ ⟨events .copy bs ++ rep.events,rep.result⟩) := by
  obtain ⟨out,pref,res⟩ := copy_prefix hl c hc src dst bs hs hd he hone fit hsrc safe data
  exact ⟨out, res, fun fuel mem tail ↦ by
    simpa [events_bits, (events_work .copy (w := w) bs).1] using pref.execute fuel mem tail⟩

/-- The RAM rejects a short field independently of the linked continuation. -/
theorem guess_short (hl : Linked M .guess pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (dst n : ℕ) (hd : c.reg (reg 2) = word w dst) (he : c.reg (reg 1) = word w (dst+n))
    (hone : c.reg (reg 3) = 1) (fit : dst+n < 2^w)
    (bits : List Bool) (h : bits.length < n) (fuel : ℕ) (mem : Memory w) :
    execute M.program fuel c mem bits = none := by
  let rest := List.replicate (n-bits.length-1) false
  let full := bits ++ false :: rest
  have hlen : full.length = n := by simp [full,rest]; omega
  obtain ⟨out, pref, res⟩ := guess_prefix hl c hc dst full hd (hlen ▸ he) hone (hlen ▸ fit)
  apply pref.execute_short fuel mem bits rest false
  simp [events_bits, full]

/-- With an accepting continuation, complete native paths are in bijection
with the independent assignments of the declared field bits. -/
theorem guess_accepts_iff (hl : Linked M .guess pc reg done) (c : Config w p r) (hc : c.pc = pc 0)
    (dst n : ℕ) (hd : c.reg (reg 2) = word w dst) (he : c.reg (reg 1) = word w (dst+n))
    (hone : c.reg (reg 3) = 1) (fit : dst+n < 2^w)
    (finish : ∀ out : Config w p r, out.pc = done → M.program.step out = .finish none)
    (mem : Memory w) (bits : List Bool) :
    (execute M.program (1+(6*n+1)) c mem bits).isSome ↔ ∃! f : Fin n → Bool, bits = List.ofFn f := by
  constructor
  · intro accepted
    have hlen : n ≤ bits.length := by
      by_contra! h
      rw [guess_short hl c hc dst n hd he hone fit bits h] at accepted
      contradiction
    let field := bits.take n
    have len : field.length = n := by simp [field,hlen]
    have hsplit : bits = field ++ bits.drop n := (List.take_append_drop ..).symm
    obtain ⟨out,pref,res⟩ := guess_prefix hl c hc dst field hd (len ▸ he) hone (len ▸ fit)
    have hrun := pref.execute 1 mem (bits.drop n)
    rw [events_bits, (events_work .guess (w := w) field).1, len] at hrun
    simp only [ite_true, ← hsplit] at hrun
    rw [hrun] at accepted
    have hempty : bits.drop n = [] := by
      by_contra h
      simp [execute, finish out res.pc, h] at accepted
    have hbits : bits = field := by simpa [hempty] using hsplit
    have eqLen := hbits ▸ len
    let f (i : Fin n) := bits[i.val]'(by rw [eqLen]; exact i.isLt)
    have hef : bits = List.ofFn f := List.ext_getElem (by simpa using eqLen) (by simp [f])
    exact ⟨f, hef, fun g hg ↦ List.ofFn_injective (hg.symm.trans hef)⟩
  · rintro ⟨f, rfl, _⟩
    obtain ⟨out,res,_,run⟩ := execute_guess hl c hc dst n hd he hone fit f
    have h := run 1 mem []
    simp only [bitField_encode, List.append_nil] at h
    rw [h]
    simp [execute, finish out res.pc]

end PairSimulation.PrivateFields

end VPVNP
end Computability
end OAI
