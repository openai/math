import OAI.Computability.VPVNP.PairSimulationRouteLoop

/-!
# Concatenated fixed-width field ranges in the cursor checker

Successor fields have one common width, as do the steps of any sorting
phase. At the return from each field the scheduler advances the running
offset. The final mask expresses the conjunction of all tests in the range.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteRange

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Registers retained by the range, and its unmodified memories. -/
structure Frame (keep : Fin r → Prop) (c d : Config w p r) : Prop where
  regs : ∀ a, keep a → d.reg a = c.reg a
  memory : d.privateMem = c.privateMem
  persistent : d.persistent = c.persistent

theorem Frame.refl {keep : Fin r → Prop} (c : Config w p r) : Frame keep c c :=
  ⟨fun _ _ ↦ rfl,rfl,rfl⟩

theorem Frame.trans {keep : Fin r → Prop} {a b c : Config w p r}
    (f : Frame keep a b) (g : Frame keep b c) : Frame keep a c :=
  ⟨fun j h ↦ (g.regs j h).trans (f.regs j h), g.memory.trans f.memory,
    g.persistent.trans f.persistent⟩

theorem Frame.put {keep : Fin r → Prop} {c d : Config w p r} (f : Frame keep c d)
    (pc : Fin p) (i : Fin r) (x : Word w) (skip : ∀ a, keep a → a ≠ i) :
    Frame keep c (d.put pc i x) :=
  ⟨fun a h ↦ (Function.update_of_ne (skip a h) ..).trans (f.regs a h), f.memory, f.persistent⟩

/-- One field's returned mask and untouched registers, before advancing
the offset and loop index. -/
structure Field (keep : Fin r → Prop) (index off mask : Fin r) (good : Prop)
    (c d : Config w p r) : Prop extends Frame keep c d where
  indexEq : d.reg index = c.reg index
  offset : d.reg off = c.reg off
  maskEq : d.reg mask = 0 ↔ c.reg mask = 0 ∧ good

/-- Prefix of the range, after the first i fields have been visited. -/
structure Partial {n : ℕ} (keep : Fin r → Prop) (off mask : Fin r) (width i : ℕ)
    (test : Fin n → Prop) (c d : Config w p r) : Prop extends Frame keep c d where
  offset : d.reg off = c.reg off + ((i * width : ℕ) : Word w)
  maskEq : d.reg mask = 0 ↔ c.reg mask = 0 ∧ ∀ j : Fin n, j.val < i → test j

/-- A range visit executes the proven native field call at each index and
counts the actual offset addition and counted-loop instructions. -/
theorem run_exact {M : Machine w p r k} {pc : Fin 3 → Fin p}
    {index bound one off widthReg mask : Fin r} {body add done : Fin p}
    (hl : RouteLoop.Linked M pc index bound one body done)
    (ha : M.code add = .binary .add off off widthReg (pc 2))
    (n width : ℕ) (cost : Fin n → ℕ) (hn : n < 2 ^ w) (test : Fin n → Prop)
    (keep : Fin r → Prop) (hb : keep bound) (h1 : keep one) (hw : keep widthReg)
    (skip : ∀ a, keep a → a ≠ index ∧ a ≠ off)
    (hio : index ≠ off) (hmi : mask ≠ index) (hmo : mask ≠ off)
    (c : Config w p r) (hc : c.pc = pc 0) (hbound : c.reg bound = (n : Word w))
    (hone : c.reg one = 1) (hwidth : c.reg widthReg = (width : Word w))
    (call : ∀ i : Fin n, ∀ q : Config w p r, q.pc = body → q.reg index = (i.val : Word w) →
      Partial keep off mask width i.val test c q → ∃ d,
        Prefix M q (List.replicate (cost i) .tick) d ∧ d.pc = add ∧
        Field keep index off mask (test i) q d) :
    ∃ d, Prefix M c (List.replicate (2 + ∑ i, (cost i + 3)) .tick) d ∧
      d.pc = done ∧ d.reg index = (n : Word w) ∧
      Partial keep off mask width n test c d := by
  let I i d := Partial keep off mask width i test c d
  have start : I 0 (c.put (pc 1) index 0) := by
    refine ⟨(Frame.refl c).put _ _ _ (fun a h ↦ (skip a h).1), ?_, ?_⟩
    · simp [Config.put, Function.update_of_ne hio.symm]
    · simp [Config.put, Function.update_of_ne hmi]
  have visit (i : Fin n) (q : Config w p r) (hp : q.pc = body) (hi : q.reg index = (i.val : Word w))
      (hI : I i.val q) :
      ∃ d, Prefix M q (List.replicate (cost i + 1) .tick) d ∧ d.pc = pc 2 ∧
        d.reg index = (i.val : Word w) ∧ d.reg one = 1 ∧
        I (i.val+1) (d.put (pc 1) index ((i.val+1 : ℕ) : Word w)) := by
    obtain ⟨mid, pre, hm, f⟩ := call i q hp hi hI
    let value := mid.reg off + mid.reg widthReg
    let next := mid.put (pc 2) off value
    have hs : M.program.step mid = .localStep next := by
      simp [Machine.program, hm, ha, Instr.run, BinaryOp.eval, value, next]
    have both := hI.toFrame.trans f.toFrame
    have g := both.put (pc 2) off value fun a h ↦ (skip a h).2
    refine ⟨next, ?_, rfl, ?_, (g.regs one h1).trans hone, ?_⟩
    · rw [List.replicate_add]
      exact pre.append (.tick hs (.nil _))
    · change Function.update mid.reg off value index = _
      rw [Function.update_of_ne hio, f.indexEq, hi]
    refine ⟨g.put _ _ _ (fun a h ↦ (skip a h).1), ?_, ?_⟩
    · have hcur := hI.offset
      change Function.update next.reg index _ off = _
      rw [Function.update_of_ne hio.symm]
      simp [next, value, f.offset, hcur, both.regs widthReg hw, hwidth, Nat.add_mul, add_assoc]
    · change Function.update next.reg index _ mask = 0 ↔ _
      rw [Function.update_of_ne hmi]
      change Function.update mid.reg off _ mask = 0 ↔ _
      rw [Function.update_of_ne hmo, f.maskEq, hI.maskEq]
      constructor
      · rintro ⟨⟨hz, hprefix⟩, hlast⟩
        refine ⟨hz, fun j hj ↦ ?_⟩
        by_cases he : j = i
        · simpa [he] using hlast
        · exact hprefix j (by have hne : j.val ≠ i.val := fun h ↦ he (Fin.ext h); omega)
      · rintro ⟨hz, hprefix⟩
        exact ⟨⟨hz, fun j hj ↦ hprefix j (by omega)⟩, hprefix i (by omega)⟩
  exact RouteLoop.run_exact hl n (fun i ↦ cost i + 1) hn I
    (fun _ _ h ↦ (h.regs bound hb).trans hbound)
    (fun _ _ _ h ↦ ⟨⟨h.regs, h.memory, h.persistent⟩, h.offset, h.maskEq⟩)
    visit c hc start

end PairSimulation.RouteRange

end VPVNP
end Computability
end OAI
