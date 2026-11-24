import OAI.Computability.VPVNP.RAMUniform
import OAI.Computability.VPVNP.RAMWordBits
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases

/-!
# Native binary-word choice subroutine

Three registers hold the partial value, the weight of the next bit, and zero.
Doubling the weight wraps to zero exactly after the last of the machine word's
bits. The eight-opcode fragment works at every word width, including zero, and
may be embedded at arbitrary program counters with an arbitrary continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.GuessWord

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {p r k w : ℕ}

/-- A local prefix of genuine native steps. The relation records every consumed
branch bit and tick, and performs no external probe. -/
inductive Prefix (M : Machine w p r k) : Config w p r → List (Event w) → Config w p r → Prop
  | nil (c) : Prefix M c [] c
  | tick {c next last es} (step : M.program.step c = .localStep next) (tail : Prefix M next es last) :
      Prefix M c (.tick :: es) last
  | choice {c g b last es} (step : M.program.step c = .branch g) (tail : Prefix M (g b) es last) :
      Prefix M c (.choice b :: es) last

variable {M : Machine w p r k} {c c' c'' : Config w p r} {es fs : List (Event w)}

theorem Prefix.append (h : Prefix M c es c') (h' : Prefix M c' fs c'') :
    Prefix M c (es ++ fs) c'' := by
  induction h with
  | nil => exact h'
  | tick hs _ ih => exact .tick hs (ih h')
  | choice hs _ ih => exact .choice hs (ih h')

/-- A valid prefix composes with the genuine RAM interpreter on every
continuation, preserving the external memory and every unconsumed bit. -/
theorem Prefix.execute (h : Prefix M c es c') (fuel : ℕ) (mem : Memory w) (more : List Bool) :
    BurstRAM.execute M.program (fuel + es.length) c mem (choiceBits es ++ more) =
      (BurstRAM.execute M.program fuel c' mem more).map (fun rep => ⟨es ++ rep.events, rep.result⟩) := by
  induction h with
  | nil c => cases hh : BurstRAM.execute M.program fuel c mem more <;> simp [choiceBits, hh]
  | tick hs ht ih | choice hs ht ih =>
    rw [List.length_cons, ← Nat.add_assoc]
    simp [choiceBits, BurstRAM.execute, hs, ih, Option.map_map, Function.comp_def, Report.prepend]

/-- A stream that stops before the last required binary choice rejects,
independently of the continuation and the available instruction fuel. -/
theorem Prefix.execute_short (h : Prefix M c es c') (fuel : ℕ) (mem : Memory w)
    (bits rest : List Bool) (b : Bool) (hs : choiceBits es = bits ++ b :: rest) :
    BurstRAM.execute M.program fuel c mem bits = none := by
  induction h generalizing bits fuel with
  | nil =>
    have hh := congrArg List.length hs
    simp [choiceBits] at hh
  | tick hstep _ ih =>
    cases fuel with
    | zero => rfl
    | succ fuel => simp [BurstRAM.execute, hstep, ih fuel bits hs]
  | @choice c g bit last es hstep htail ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases bits with
      | nil => simp [BurstRAM.execute, hstep]
      | cons t bits =>
        obtain ⟨rfl, he⟩ := List.cons.inj hs
        simp [BurstRAM.execute, hstep, ih fuel bits he]

/-- Eight fixed instruction slots. Register zero is the result, register one
is the binary weight, and register two is zero. -/
def instruction (w : ℕ) (pc : Fin 8 → Fin p) (reg : Fin 3 ↪ Fin r) (done : Fin p) :
    Fin 8 → Instr w p r k :=
  ![.constant (reg 2) 0 (pc 1), .constant (reg 0) 0 (pc 2), .constant (reg 1) 1 (pc 3),
    .jumpLt (reg 2) (reg 1) (pc 4) done, .choose (pc 5) (pc 6),
    .binary .add (reg 0) (reg 0) (reg 1) (pc 7), .binary .add (reg 0) (reg 0) (reg 2) (pc 7),
    .binary .add (reg 1) (reg 1) (reg 1) (pc 3)]

/-- The instantiated table embeds the same fragment in any larger program. -/
theorem resize_instruction (pc : Fin 8 → Fin p) (reg : Fin 3 ↪ Fin r) (done : Fin p) (i : Fin 8) :
    (instruction (k := k) 1 pc reg done i).resize w = instruction w pc reg done i := by
  fin_cases i <;> rfl

/-- The host machine implements the eight word-guess instructions at the specified labels and
registers with the specified continuation. -/
def Contains (M : Machine w p r k) (pc : Fin 8 → Fin p) (reg : Fin 3 ↪ Fin r) (done : Fin p) : Prop :=
  ∀ i, M.code (pc i) = instruction w pc reg done i

/-- Value of a little-endian bit string, independently of the RAM word modulus. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => (finTwoEquiv.symm b).val + 2 * value bs

@[simp] private theorem digit_false : (finTwoEquiv.symm false).val = 0 := rfl
@[simp] private theorem digit_true : (finTwoEquiv.symm true).val = 1 := rfl

private theorem value_ofFn {z : ℕ} (f : Fin z → Bool) :
    value (List.ofFn f) = ∑ i, (finTwoEquiv.symm (f i)).val * 2 ^ i.val := by
  induction z with
  | zero => simp [value]
  | succ z ih =>
    rw [List.ofFn_succ, value, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, ← Nat.mul_assoc,
      ← Finset.sum_mul, Nat.mul_comm 2]

@[simp] theorem value_wordBits (v : Word w) : value (wordBits v) = v.val := by
  rw [wordBits, value_ofFn]
  exact (finFunctionFinEquiv_apply (fun i => finTwoEquiv.symm (RAMSerialization.wordBits w v i))).symm.trans
    (congrArg Fin.val ((RAMSerialization.wordBits w).symm_apply_apply v))

/-- Loop events for guessing the supplied little-endian bit sequence, including one choice per
bit and the final exit tick. -/
def events {w : ℕ} : List Bool → List (Event w)
  | [] => [.tick]
  | b :: bs => [.tick, .choice b, .tick, .tick] ++ events bs

@[simp] theorem length_events (bs : List Bool) : (events (w := w) bs).length = 4 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [events, ih]; omega

@[simp] theorem choiceBits_events (bs : List Bool) : choiceBits (events (w := w) bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [events, choiceBits] using congrArg (b :: ·) ih

private theorem step_at {pc : Fin 8 → Fin p} {reg : Fin 3 ↪ Fin r} {done : Fin p}
    (hc : Contains M pc reg done) (i : Fin 8) (hpc : c.pc = pc i) :
    M.program.step c = (instruction w pc reg done i).run M.publicData c := by
  simp [Machine.program, hpc, hc i]

private theorem next_bit {pc : Fin 8 → Fin p} {reg : Fin 3 ↪ Fin r} {done : Fin p}
    (hc : Contains M pc reg done) (hpc : c.pc = pc 3) (hz : c.reg (reg 2) = 0)
    (hplace : c.reg (reg 1) ≠ 0) (b : Bool) :
    let gain := if b then c.reg (reg 1) else c.reg (reg 2)
    let ca := c.put (pc 7) (reg 0) (c.reg (reg 0) + gain)
    let cb := ca.put (pc 3) (reg 1) (ca.reg (reg 1) + ca.reg (reg 1))
    Prefix M c [.tick, .choice b, .tick, .tick] cb := by
  dsimp only
  have ht : M.program.step c = .localStep {c with pc := pc 4} := by
    rw [step_at hc 3 hpc]
    change CallAction.localStep {c with pc := if c.reg (reg 2) < c.reg (reg 1) then pc 4 else done} = _
    have hpos : 0 < c.reg (reg 1) := Fin.pos_iff_ne_zero.mpr hplace
    simp [hz, hpos]
  apply Prefix.tick ht
  let ct := {c with pc := pc 4}
  have hb : M.program.step ct = .branch (fun b => {ct with pc := if b then pc 5 else pc 6}) :=
    step_at hc 4 rfl
  apply Prefix.choice hb
  cases b with
  | false =>
    apply Prefix.tick (step_at hc 6 rfl)
    exact Prefix.tick (step_at hc 7 rfl) (.nil _)
  | true =>
    apply Prefix.tick (step_at hc 5 rfl)
    exact Prefix.tick (step_at hc 7 rfl) (.nil _)

private theorem weight_ne_zero {i : ℕ} (hi : i < w) : ((2^i : ℕ) : Word w) ≠ 0 := by
  intro h
  have he := congrArg Fin.val h
  rw [Fin.val_natCast, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hi)] at he
  exact (Nat.two_pow_pos i).ne' he

/-- Execute the exact choices remaining at a loop entry. -/
private theorem loop {pc : Fin 8 → Fin p} {reg : Fin 3 ↪ Fin r} {done : Fin p}
    (hc : Contains M pc reg done) (bits : List Bool) (c : Config w p r)
    (i : ℕ) (hwidth : i + bits.length = w) (hpc : c.pc = pc 3)
    (hz : c.reg (reg 2) = 0) (hp : c.reg (reg 1) = ((2^i : ℕ) : Word w)) :
    ∃ out, Prefix M c (events bits) out ∧ out.pc = done ∧
      out.reg (reg 0) = c.reg (reg 0) + c.reg (reg 1) * (value bits : Word w) ∧
      (∀ j, j ∉ Set.range reg → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧ out.reg (reg 1) = 0 ∧ out.reg (reg 2) = 0 := by
  induction bits generalizing i c with
  | nil =>
    have he : c.reg (reg 1) = 0 := by
      simp only [List.length_nil, Nat.add_zero] at hwidth
      rw [hp, hwidth]
      exact Fin.ext (Nat.mod_self _)
    refine ⟨{c with pc := done}, Prefix.tick ?_ (.nil _), rfl, by simp [value], fun _ _ => rfl, rfl, rfl, he, hz⟩
    rw [step_at hc 3 hpc]
    change CallAction.localStep {c with pc := if c.reg (reg 2) < c.reg (reg 1) then pc 4 else done} = _
    simp [he, hz]
  | cons b bits ih =>
    let gain := if b then c.reg (reg 1) else c.reg (reg 2)
    let ca := c.put (pc 7) (reg 0) (c.reg (reg 0) + gain)
    let cb := ca.put (pc 3) (reg 1) (ca.reg (reg 1) + ca.reg (reg 1))
    have hv : i < w := by simp only [List.length_cons] at hwidth; omega
    have pref := next_bit hc hpc hz (hp ▸ weight_ne_zero hv) b
    have hpow : ((2^(i+1) : ℕ) : Word w) = ((2^i : ℕ) : Word w) + ((2^i : ℕ) : Word w) := by
      rw [pow_succ, Nat.mul_two, Nat.cast_add]
    have hplace : cb.reg (reg 1) = ((2^(i+1) : ℕ) : Word w) := by
      simp [cb, ca, Config.put, hp, hpow]
    obtain ⟨out, hpref, hdone, hacc, hother, hpriv, hpersist, hzero⟩ := ih cb (i+1)
      (by simp only [List.length_cons] at hwidth; omega) rfl
      (by simp [cb, ca, Config.put, hz]) hplace
    refine ⟨out, pref.append hpref, hdone, ?_, ?_, hpriv, hpersist, hzero⟩
    · rw [hacc]
      cases b <;>
        simp [cb, ca, Config.put, gain, hz, value] <;> ring
    · intro j hj
      have hj₀ : j ≠ reg 0 := fun e => hj ⟨0, e.symm⟩
      have hj₁ : j ≠ reg 1 := fun e => hj ⟨1, e.symm⟩
      rw [hother j hj]
      simp [cb, ca, Config.put, Function.update_of_ne hj₀, Function.update_of_ne hj₁]

/-- The complete event list including the three register initializations. -/
def trace (v : Word w) : List (Event w) := [.tick, .tick, .tick] ++ events (wordBits v)

/-- Exact register file at loop exit. Both temporary registers contain zero. -/
def resultRegs (reg : Fin 3 ↪ Fin r) (rs : Fin r → Word w) (v : Word w) : Fin r → Word w :=
  Function.update (Function.update (Function.update rs (reg 2) 0) (reg 1) 0) (reg 0) v

/-- From its entry the native subroutine consumes exactly the canonical bits of
the output word, uses `4*w+4` private instructions, and returns to its chosen
continuation. Every external address and every other register is preserved. -/
theorem native_exact (M : Machine w p r k) (pc : Fin 8 → Fin p) (reg : Fin 3 ↪ Fin r) (done : Fin p)
    (hc : Contains M pc reg done) (c : Config w p r) (hpc : c.pc = pc 0) (v : Word w) :
    Prefix M c (trace v) ⟨done, c.persistent, resultRegs reg c.reg v, c.privateMem⟩ := by
  let z := c.put (pc 1) (reg 2) 0
  let a := z.put (pc 2) (reg 0) 0
  let start := a.put (pc 3) (reg 1) 1
  have hinit : Prefix M c [.tick, .tick, .tick] start :=
    .tick (step_at hc 0 hpc) (.tick (step_at hc 1 rfl) (.tick (step_at hc 2 rfl) (.nil _)))
  obtain ⟨out, pref, he, hr, hrest, hp, hs, hw, hz⟩ := loop hc (wordBits v) start 0 (by simp) rfl
    (by simp [start, a, z, Config.put]) (by simp [start])
  have hr₀ : out.reg (reg 0) = v := by simpa [start, a, Config.put] using hr
  have hout : out = ⟨done, c.persistent, resultRegs reg c.reg v, c.privateMem⟩ := by
    have hregs : out.reg = resultRegs reg c.reg v := by
      funext j
      by_cases hj : j ∈ Set.range reg
      · obtain ⟨i, rfl⟩ := hj
        fin_cases i <;> simp [resultRegs, hr₀, hw, hz]
      · have hnot (i : Fin 3) : j ≠ reg i := fun e => hj ⟨i, e.symm⟩
        rw [hrest j hj]
        simp [resultRegs, start, a, z, Config.put, Function.update_of_ne (hnot _)]
    cases out
    congr
  rw [← hout]
  exact hinit.append pref

theorem native (M : Machine w p r k) (pc : Fin 8 → Fin p) (reg : Fin 3 ↪ Fin r) (done : Fin p)
    (hc : Contains M pc reg done) (c : Config w p r) (hpc : c.pc = pc 0) (v : Word w) :
    ∃ out es, Prefix M c es out ∧ es.length = 4*w+4 ∧ choiceBits es = wordBits v ∧
      out.pc = done ∧ out.reg (reg 0) = v ∧ (∀ j, j ∉ Set.range reg → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  refine ⟨_, _, native_exact M pc reg done hc c hpc v, by simp [trace], by simp [trace, choiceBits],
    rfl, by simp [resultRegs], ?_, rfl, rfl⟩
  intro j hj
  have hnot (i : Fin 3) : j ≠ reg i := fun e => hj ⟨i, e.symm⟩
  simp [resultRegs, Function.update_of_ne (hnot _)]

/-- Every complete word-width string is the encoding of its unique output. -/
theorem exists_wordBits (bs : List Bool) (h : bs.length = w) : ∃ v : Word w, wordBits v = bs := by
  let f (i : Fin w) := bs.get (i.cast h.symm)
  refine ⟨(RAMSerialization.wordBits w).symm f, ?_⟩
  rw [wordBits, Equiv.apply_symm_apply]
  apply List.ext_getElem (List.length_ofFn.trans h.symm)
  intro i hi hi'
  simp [f]

theorem native_short {M : Machine w p r k} {pc : Fin 8 → Fin p} {reg : Fin 3 ↪ Fin r} {done : Fin p}
    (hc : Contains M pc reg done) (c : Config w p r) (hpc : c.pc = pc 0) (bits : List Bool)
    (hs : bits.length < w) (fuel : ℕ) (mem : Memory w) :
    BurstRAM.execute M.program fuel c mem bits = none := by
  let tail := List.replicate (w - bits.length - 1) false
  obtain ⟨v, hv⟩ := exists_wordBits (w := w) (bits ++ false :: tail) (by simp [tail]; omega)
  obtain ⟨out, es, he, _, hb, _⟩ := native M pc reg done hc c hpc v
  exact he.execute_short fuel mem bits tail false (hb.trans hv)

end PrimedCounter.GuessWord

end VPVNP
end Computability
end OAI
