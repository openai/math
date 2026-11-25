import OAI.Computability.BorderVNP.CubeISALocalRowFinish
import OAI.Computability.BorderVNP.CubeISALocalRowFrame

/-! # Verifying the subtotal of a diagonal symbol row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open Cube Cube.Physical Cube.Physical.Owned VPVNP.BurstRAM CubeLengths

/-- The diagonal singleton orientation computes the full physical subtotal. Comparing it
against the preserved claim returns precisely when every coordinate agrees. Every return
restores the vertex cursor and preserves all memory outside the computed row. -/
theorem diagonalTail_run {w n d blocks K h : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (i : Fin (n+1)) (a : Fin d)
    (B s base claim saved : ℕ) (select : Packet n d blocks → Selector n K h)
    (declared : Fin (n+1) → ℕ) (cfg : SingleTally.Config i a a base (blocks*(h*B)) (.ofWords r m))
    (ctr : singlePairTrials n d < 2^w) (labelFit : d^(n+1) ≤ 2^w) (dim : n+1 < 2^w)
    (baseFit : base+(n+1) ≤ 2^w)
    (fit : ∀ j : Fin (n+1), subtotals itemRow (crossCount B s select) i (Sym2.mk a a) j < 2^w)
    (clear : ∀ j : Fin (n+1), readings m (base+j.val) = 0)
    (h59 : readings r 59 = claim) (h61 : readings r 61 = saved)
    (claimWords : ∀ j : Fin (n+1), readings m (claim+j.val) = declared j)
    (outside : ∀ j : Fin (n+1), claim+j.val < base ∨ base+(n+1) ≤ claim+j.val)
    (claimFit : claim+(n+1) ≤ 2^w) :
    TestRun pub mac (.seq (SingleTally.oriented n) (.seq finish compare)) r m
      ((4+SingleTally.rowCost i a a (blocks*(h*B)))+(5+((n+1)*(rowBody.slots+1)+1)))
      (∀ j, subtotals itemRow (crossCount B s select) i (Sym2.mk a a) j = declared j)
      (fun z => z.reg 7 = saved ∧ (∀ j : Fin (n+1), z.mem (base+j.val) =
        subtotals itemRow (crossCount B s select) i (Sym2.mk a a) j) ∧
        ∀ x, x < base ∨ base+(n+1) ≤ x → z.mem x = readings m x) := by
  let count := subtotals itemRow (crossCount B s select) i (Sym2.mk a a)
  obtain ⟨es,t,mt,run,cost,rows,untouched⟩ := DeclaredRow.diagonal_run pub mac r m i a B s base select
    cfg ctr labelFit dim baseFit (fun j => by simpa only [clear,Nat.zero_add] using fit j)
  have tallied : BoundedRun pub mac (SingleTally.oriented n) r m (4+SingleTally.rowCost i a a (blocks*(h*B)))
      (fun z => (∀ j : Fin (n+1), z.mem (base+j.val) = count j) ∧
        (∀ x, x < base ∨ base+(n+1) ≤ x → z.mem x = readings m x) ∧
        ∀ k : Reg, k ∈ ([0,1,5,9,22,23,59,61] : List Reg) → z.reg k = readings r k) :=
    ⟨es,t,mt,run,cost,fun j => by simpa only [clear,Nat.zero_add,count] using rows j,untouched,
      fun k hk => congrArg Fin.val (run.keepsReg (diagonalTally_keeps n k hk))⟩
  apply ((tallied.asTest (diagonalTally_deterministic n)).seq
    (b := .seq finish compare) (cb := 5+((n+1)*(rowBody.slots+1)+1)) (ob := ∀ j, count j = declared j)
    (Q := fun z => z.reg 7 = saved ∧ (∀ j : Fin (n+1), z.mem (base+j.val) = count j) ∧
      ∀ x, x < base ∨ base+(n+1) ≤ x → z.mem x = readings m x) ?_).mono le_rfl
    (by simp only [true_and,count]) (fun _ hz => hz)
  rintro u mu ⟨actual,keepMem,regs⟩
  change ∀ j : Fin (n+1), readings mu (base+j.val) = count j at actual
  have claimed (j : Fin (n+1)) : readings mu (claim+j.val) = declared j :=
    (keepMem _ (outside j)).trans (claimWords j)
  apply (finishCompare_run pub mac u mu n base claim saved
    ((regs 0 (by decide)).trans cfg.zero) ((regs 1 (by decide)).trans cfg.one)
    ((regs 5 (by decide)).trans cfg.dim) ((regs 9 (by decide)).trans cfg.row)
    ((regs 59 (by decide)).trans h59) ((regs 61 (by decide)).trans h61) dim baseFit claimFit).mono le_rfl
  · simp only [actual,claimed]
  · rintro z ⟨mem,cursor⟩
    exact ⟨cursor,fun j => (congrFun mem _).trans (actual j),fun x hx => (congrFun mem x).trans (keepMem x hx)⟩

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
