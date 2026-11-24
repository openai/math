import OAI.Computability.VPVNP.PairSimulationMapDriver

/-!
# Dispatching a resident map by its demand grid and party

Each fixed grid row and party has a distinct matrix image. The selected term
stores the demand ordinal, and the resident directory supplies the party. Two
finite comparison chains decrement these ordinals until they reach their own
images. No public constants beyond the zero and one registers are needed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentMapDispatch

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {X Z J : Type*} {w p r k : ℕ}

/-- A separate test and subtraction instruction for each fixed alternative. -/
structure Cases (X : Type*) (p r : ℕ) where
  /-- Cases in ordinal order, starting at zero. -/
  items : List X
  /-- Address of each case's test for a zero index. -/
  test : X → Fin p
  /-- Address of the decrement that skips each unmatched case. -/
  subtract : X → Fin p
  /-- Destination when the corresponding case matches. -/
  target : X → Fin p
  /-- Destination when the case list is exhausted. -/
  bad : Fin p
  /-- Register holding the remaining ordinal. -/
  index : Fin r
  /-- Register used as zero by the comparison instruction. -/
  zero : Fin r
  /-- Register used as one by the decrement instruction. -/
  one : Fin r

namespace Cases

variable (C : Cases X p r)

/-- Enter the first case test, or the rejecting continuation if the list is empty. -/
def start : List X → Fin p
  | [] => C.bad
  | x :: _ => C.test x

/-- The machine tests the current index and decrements it before testing the next case. -/
def Linked (M : Machine w p r k) : List X → Prop
  | [] => True
  | x :: xs => M.code (C.test x) = .jumpEq C.index C.zero (C.target x) (C.subtract x) ∧
    M.code (C.subtract x) = .binary .sub C.index C.index C.one (C.start xs) ∧ Linked M xs

/-- Dispatch takes two ticks per skipped case and one for a matching case. -/
def ticks (size i : ℕ) : ℕ := 2 * min size i + if i < size then 1 else 0

theorem ticks_le (size i : ℕ) : ticks size i ≤ 2 * size + 1 := by
  unfold ticks
  have := min_le_left size i
  split <;> omega

/-- A valid ordinal reaches precisely its own table image. Any unused ordinal
exhausts the chain and enters the rejecting continuation. -/
theorem run (M : Machine w p r k) (items : List X) (link : C.Linked M items)
    (i : ℕ) (fit : i < 2 ^ w) (c : Config w p r) (pc : c.pc = C.start items)
    (val : c.reg C.index = (i : Word w)) (zero : c.reg C.zero = 0) (one : c.reg C.one = 1)
    (z : C.zero ≠ C.index) (o : C.one ≠ C.index) :
    ∃ d, Prefix M c (List.replicate (ticks items.length i) .tick) d ∧
      d.pc = (items[i]?.elim C.bad C.target) ∧
      (∀ q, q ≠ C.index → d.reg q = c.reg q) ∧ d.privateMem = c.privateMem ∧
      d.persistent = c.persistent := by
  induction items generalizing i c with
  | nil => exact ⟨c, by simpa [ticks] using Prefix.nil (M := M) c, pc, fun _ _ ↦ rfl, rfl, rfl⟩
  | cons x xs ih =>
    have head : M.program.step c =
        .localStep {c with pc := if (i : Word w) = 0 then C.target x else C.subtract x} := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, pc, start, link.1]
      change CallAction.localStep {c with pc := if c.reg C.index = c.reg C.zero then _ else _} = _
      rw [val, zero]
    cases i with
    | zero =>
      have h : M.program.step c = .localStep {c with pc := C.target x} := by simpa using head
      exact ⟨{c with pc := C.target x}, by simpa [ticks] using Prefix.tick h (.nil _),
        rfl, fun _ _ ↦ rfl, rfl, rfl⟩
    | succ i =>
      have nz : ((i + 1 : ℕ) : Word w) ≠ 0 := by
        intro eq
        have hv := congrArg Fin.val eq
        change (i + 1) % (2 ^ w) = 0 at hv
        rw [Nat.mod_eq_of_lt fit] at hv
        omega
      let a := {c with pc := C.subtract x}
      let b := a.put (C.start xs) C.index (i : Word w)
      have first : M.program.step c = .localStep a := head.trans (by rw [ite_eq_right nz])
      have second : M.program.step a = .localStep b := by
        rw [show M.program.step a = (M.code (C.subtract x)).run M.publicData a from rfl, link.2.1]
        change CallAction.localStep (a.put (C.start xs) C.index (c.reg C.index - c.reg C.one)) = _
        simp [b, val, one]
      have keep (q) (h : q ≠ C.index) : b.reg q = c.reg q := by
        simp [a, b, Config.put, Function.update_of_ne h]
      obtain ⟨d, run, outPC, frame, mem, per⟩ := ih link.2.2 i (by omega) b rfl
        (Config.put_same ..) ((keep C.zero z).trans zero) ((keep C.one o).trans one)
      have hlen : ticks (x :: xs).length (i + 1) = 2 + ticks xs.length i := by
        simp only [ticks, List.length_cons, Nat.succ_lt_succ_iff, min_add_add_right]
        omega
      refine ⟨d, ?_, outPC, fun q h ↦ (frame q h).trans (keep q h), mem, per⟩
      rw [hlen, List.replicate_add]
      exact .tick first (.tick second run)

end Cases

/-- The first fixed table transfers to the selected grid's party table. -/
structure Program (Z J : Type*) (p r : ℕ) where
  /-- First-stage table indexed by the demand-grid ordinal. -/
  grids : Cases Z p r
  /-- Second-stage party table for each grid. -/
  parties : Z → Cases J p r
  enter : ∀ z, grids.target z = (parties z).start (parties z).items
  bad : ∀ z, (parties z).bad = grids.bad

namespace Program

variable (P : Program Z J p r)

/-- The two-stage native dispatch uses the stored grid and party ordinals.
All registers outside those two operand words survive both comparison chains. -/
theorem hit (M : Machine w p r k) (gridLink : P.grids.Linked M P.grids.items)
    (partyLink : ∀ z, (P.parties z).Linked M (P.parties z).items)
    (g : Fin P.grids.items.length) (j : Fin (P.parties P.grids.items[g.val]).items.length)
    (c : Config w p r) (pc : c.pc = P.grids.start P.grids.items)
    (grid : c.reg P.grids.index = (g.val : Word w))
    (party : c.reg (P.parties P.grids.items[g.val]).index = (j.val : Word w))
    (zero : c.reg P.grids.zero = 0) (one : c.reg P.grids.one = 1)
    (gfit : g.val < 2 ^ w) (jfit : j.val < 2 ^ w)
    (g₀ : P.grids.zero ≠ P.grids.index) (g₁ : P.grids.one ≠ P.grids.index)
    (separate : ∀ z, (P.parties z).index ≠ P.grids.index ∧
      (P.parties z).zero = P.grids.zero ∧ (P.parties z).one = P.grids.one ∧
      (P.parties z).zero ≠ (P.parties z).index ∧ (P.parties z).one ≠ (P.parties z).index) :
    let z := P.grids.items[g.val]
    let C := P.parties z
    ∃ d, Prefix M c (List.replicate ((2 * g.val + 1) + (2 * j.val + 1)) .tick) d ∧
      d.pc = C.target C.items[j.val] ∧
      (∀ q, q ≠ P.grids.index → q ≠ C.index → d.reg q = c.reg q) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  intro z C
  obtain ⟨a, first, ha, frame, mem, per⟩ := P.grids.run M _ gridLink g.val gfit c pc grid
    zero one g₀ g₁
  rw [List.getElem?_eq_getElem g.isLt, Option.elim_some, P.enter] at ha
  obtain ⟨i, hz, ho, cz, co⟩ := separate z
  obtain ⟨d, tail, hd, saved, dm, dp⟩ := C.run M _ (partyLink z) j.val jfit a ha
    ((frame _ i).trans party) (hz ▸ (frame _ g₀).trans zero) (ho ▸ (frame _ g₁).trans one) cz co
  rw [List.getElem?_eq_getElem j.isLt, Option.elim_some] at hd
  refine ⟨d, ?_, hd, fun q hq hq' ↦ (saved q hq').trans (frame q hq), dm.trans mem, dp.trans per⟩
  simp only [Cases.ticks, Nat.min_eq_right g.isLt.le, ite_eq_left g.isLt] at first
  have hj : j.val < (P.parties z).items.length := j.isLt
  simp only [Cases.ticks, Nat.min_eq_right hj.le, ite_eq_left hj] at tail
  rw [List.replicate_add]
  exact first.append tail

end Program
end PairSimulation.ResidentMapDispatch

end VPVNP
end Computability
end OAI
