import OAI.Computability.VPVNP.PairSimulationPrivateFields
import OAI.Computability.VPVNP.PairSimulationStackMemory

/-!
# Moving a logical-order half-wire field into a private bit stack

The selected half-wire is stored in increasing logical order. A stack grows
upwards with its first logical bit at the highest occupied address. This
fixed five-row fragment therefore advances the source and retreats the
destination. Missing chain endpoints use the same loop with a zero source.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafFieldCopy

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {bits p r k : ℕ}

/-- Encode a natural address in a machine word. -/
abbrev word (bits n : ℕ) : Word bits := (n : Word bits)

/-- Read a resident half-wire cell or supply the clamped zero bit. -/
inductive Source | resident | zero deriving DecidableEq

/-- Word returned by this source at the current cursor. -/
def Source.value (m : Word bits → Word bits) (a : Word bits) : Source → Word bits
  | .resident => m a
  | .zero => 0

/-- Source cursor, destination base, exclusive destination cursor, unit, temporary. -/
def instruction (source : Source) (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (done : Fin p) :
    Fin 5 → Instr bits p r k :=
  ![.jumpEq (reg 2) (reg 1) done (pc 1),
    .binary .sub (reg 2) (reg 2) (reg 3) (pc 2),
    (match source with
      | .resident => .loadPrivate (reg 4) (reg 0) (pc 3)
      | .zero => .constant (reg 4) 0 (pc 3)),
    .storePrivate (reg 2) (reg 4) (pc 4),
    .binary .add (reg 0) (reg 0) (reg 3) (pc 0)]

theorem resize_instruction (source : Source) (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r)
    (done : Fin p) (i : Fin 5) :
    (instruction (bits := 1) (k := k) source pc reg done i).resize bits =
      instruction source pc reg done i := by cases source <;> fin_cases i <;> rfl

/-- The host instruction table contains the five-row descending copy loop. -/
def Linked (M : Machine bits p r k) (source : Source) (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r)
    (done : Fin p) := ∀ i, M.code (pc i) = instruction source pc reg done i

/-- Write a bit list into private stack memory with its head at the highest address. -/
def place (lo : ℕ) : List Bool → (Word bits → Word bits) → Word bits → Word bits
  | [], m => m
  | b :: bs, m => place lo bs (Function.update m (word bits (lo+bs.length)) (PrivateFields.bitValue bits b))

theorem place_outside (lo : ℕ) (bs : List Bool) (m : Word bits → Word bits) (a : Word bits)
    (fit : lo+bs.length ≤ 2^bits) (ha : a.val < lo ∨ lo+bs.length ≤ a.val) :
    place lo bs m a = m a := by
  induction bs generalizing m with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons] at fit ha
    rw [place, ih _ (by omega) (by omega)]
    apply Function.update_of_ne
    intro h
    have e := congrArg Fin.val h
    change a.val = (lo+bs.length) % 2^bits at e
    rw [Nat.mod_eq_of_lt (by omega)] at e
    omega

theorem place_at (lo : ℕ) (pre : List Bool) (b : Bool) (tail : List Bool) (m : Word bits → Word bits)
    (fit : lo+(pre++b::tail).length ≤ 2^bits) :
    place lo (pre++b::tail) m (word bits (lo+tail.length)) = PrivateFields.bitValue bits b := by
  induction pre generalizing m with
  | nil =>
    change place lo tail _ _ = _
    simp only [List.nil_append, List.length_cons] at fit
    have hf : lo+tail.length < 2^bits := by omega
    rw [place_outside _ _ _ _ hf.le (.inr (by change _ ≤ _ % _; rw [Nat.mod_eq_of_lt hf]))]
    exact Function.update_self ..
  | cons x pre ih =>
    apply ih
    simp only [List.length_append, List.length_cons] at *
    omega

variable {M : Machine bits p r k} {source : Source} {pc : Fin 5 → Fin p} {reg : Fin 5 ↪ Fin r} {done : Fin p}

private theorem step_at (link : Linked M source pc reg done) (i : Fin 5) (c : Config bits p r)
    (hc : c.pc = pc i) : M.program.step c = (instruction source pc reg done i).run M.publicData c := by
  simp [Machine.program, hc, link i]

private theorem iteration {src dst : ℕ} (link : Linked M source pc reg done) (c : Config bits p r)
    (hc : c.pc = pc 0) (hs : c.reg (reg 0) = word bits src)
    (hd : c.reg (reg 2) = word bits (dst+1)) (hneq : c.reg (reg 2) ≠ c.reg (reg 1))
    (h1 : c.reg (reg 3) = 1) (b : Bool)
    (value : (source.value c.privateMem (word bits src)) =
      PrivateFields.bitValue bits b) :
    ∃ out, Prefix M c (List.replicate 5 .tick) out ∧ out.pc = pc 0 ∧
      out.reg (reg 0) = word bits (src+1) ∧ out.reg (reg 2) = word bits dst ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j) ∧
      out.privateMem = Function.update c.privateMem (word bits dst) (PrivateFields.bitValue bits b) ∧
      out.persistent = c.persistent := by
  let a := { c with pc := pc 1 }
  let d := a.put (pc 2) (reg 2) (word bits dst)
  let v := d.put (pc 3) (reg 4) (PrivateFields.bitValue bits b)
  let m := v.store (pc 4) (word bits dst) (PrivateFields.bitValue bits b)
  let out := m.put (pc 0) (reg 0) (word bits (src+1))
  have s0 : M.program.step c = .localStep a := by
    rw [step_at link 0 c hc]
    simp [instruction, Instr.run, hneq, a]
  have s1 : M.program.step a = .localStep d := by
    rw [step_at link 1 a rfl]
    simp [instruction, Instr.run, BinaryOp.eval, d, a, hd, h1, word]
  have s2 : M.program.step d = .localStep v := by
    rw [step_at link 2 d rfl]
    cases source <;> simp_all [instruction, Instr.run, d, v, a, Config.put, Source.value]
  have s3 : M.program.step v = .localStep m := by
    rw [step_at link 3 v rfl]
    simp [instruction, Instr.run, v, m, d, Config.put]
  have s4 : M.program.step m = .localStep out := by
    rw [step_at link 4 m rfl]
    simp [instruction, Instr.run, BinaryOp.eval, m, out, v, d, a, Config.store, Config.put, hs, h1, word]
  refine ⟨out, .tick s0 (.tick s1 (.tick s2 (.tick s3 (.tick s4 (.nil _))))),
    rfl, by simp [out], by simp [out,m,v,d,Config.put,Config.store], ?_, rfl, rfl⟩
  intro j h0 h2 h4
  simp [out,m,v,d,a,Config.put,Config.store,Function.update_of_ne h0,Function.update_of_ne h2,
    Function.update_of_ne h4]

/-- Exact native result, with the unrelated registers and cells framed. -/
structure Result (reg : Fin 5 ↪ Fin r) (done : Fin p) (c out : Config bits p r)
    (src lo : ℕ) (bs : List Bool) : Prop where
  pc : out.pc = done
  source : out.reg (reg 0) = word bits (src+bs.length)
  destination : out.reg (reg 2) = word bits lo
  frame : ∀ j, j ≠ reg 0 → j ≠ reg 2 → j ≠ reg 4 → out.reg j = c.reg j
  privateMem : out.privateMem = place lo bs c.privateMem
  persistent : out.persistent = c.persistent

theorem run (link : Linked M source pc reg done) (c : Config bits p r) (hc : c.pc = pc 0)
    (src lo : ℕ) (bs : List Bool) (hs : c.reg (reg 0) = word bits src)
    (hb : c.reg (reg 1) = word bits lo) (he : c.reg (reg 2) = word bits (lo+bs.length))
    (h1 : c.reg (reg 3) = 1) (fit : lo+bs.length < 2^bits)
    (safe : source = .resident → src+bs.length ≤ 2^bits ∧
      (src+bs.length ≤ lo ∨ lo+bs.length ≤ src))
    (data : ∀ i : Fin bs.length,
      (source.value c.privateMem (word bits (src+i.val))) =
        PrivateFields.bitValue bits bs[i.val]) :
    ∃ out, Prefix M c (List.replicate (5*bs.length+1) .tick) out ∧ Result reg done c out src lo bs := by
  induction bs generalizing c src with
  | nil =>
    have eq : c.reg (reg 2) = c.reg (reg 1) := he.trans hb.symm
    let out := {c with pc := done}
    have s : M.program.step c = .localStep out := by
      rw [step_at link 0 c hc]
      simp [instruction, Instr.run, eq, out]
    exact ⟨out, .tick s (.nil _), rfl, hs, he, fun _ _ _ _ ↦ rfl, rfl, rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons, ← Nat.add_assoc] at he fit
    have neq : c.reg (reg 2) ≠ c.reg (reg 1) := by
      rw [he,hb]
      intro h
      have e := congrArg Fin.val h
      change (lo+bs.length+1) % 2^bits = lo % 2^bits at e
      rw [Nat.mod_eq_of_lt fit, Nat.mod_eq_of_lt (by omega)] at e
      omega
    have val := data ⟨0, by simp⟩
    simp only [Nat.add_zero,List.getElem_cons_zero] at val
    obtain ⟨next,pref,hpc,hsrc,hdst,frame,hm,hper⟩ := iteration link c hc hs he neq h1 b val
    have data' (i : Fin bs.length) :
        (source.value next.privateMem (word bits (src+1+i.val))) =
          PrivateFields.bitValue bits bs[i.val] := by
      have e := data ⟨i.val+1, by simp⟩
      simp only [List.getElem_cons_succ] at e
      cases source with
      | zero => exact e
      | resident =>
        have ss := safe rfl
        simp only [List.length_cons] at ss
        have hi := i.isLt
        have ne : word bits (src+1+i.val) ≠ word bits (lo+bs.length) := by
          intro h
          have eq := congrArg Fin.val h
          change _ % 2^bits = _ % 2^bits at eq
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at eq
          omega
        simp only [Source.value] at e ⊢
        rw [hm, Function.update_of_ne ne]
        simpa [Nat.add_assoc, Nat.add_comm 1] using e
    have keep (i : Fin 5) (a : i ≠ 0) (b : i ≠ 2) (d : i ≠ 4) :=
      frame _ (reg.injective.ne a) (reg.injective.ne b) (reg.injective.ne d)
    obtain ⟨out,tail,res⟩ := ih next hpc (src+1) hsrc
      ((keep 1 (by decide) (by decide) (by decide)).trans hb) hdst
      ((keep 3 (by decide) (by decide) (by decide)).trans h1) (by omega)
      (fun h ↦ by have e := safe h; simp only [List.length_cons] at e; omega) data'
    refine ⟨out, ?_, res.pc, ?_, res.destination, ?_, ?_, res.persistent.trans hper⟩
    · convert pref.append tail using 1
      rw [← List.replicate_add]
      congr 1
      simp; omega
    · simpa [Nat.add_assoc, Nat.add_comm 1] using res.source
    · intro j h0 h2 h4
      exact (res.frame j h0 h2 h4).trans (frame j h0 h2 h4)
    · rw [res.privateMem, hm, place]

end PairSimulation.LeafFieldCopy

end VPVNP
end Computability
end OAI
