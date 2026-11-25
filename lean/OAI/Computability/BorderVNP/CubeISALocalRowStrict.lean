import OAI.Computability.BorderVNP.CubeISALocalRowFinish
import OAI.Computability.BorderVNP.CubeISALocalRowFrame

/-! # Exact verification of one strict local cube row

Starting with the cleared row and the packet bank's stored selectors, the
three native traversals count the selected packet edges and both orientations
of singleton endpoints. The final comparison reads the preserved declaration
and restores the vertex cursor on every returning path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open Cube Cube.Physical Cube.Physical.Owned VPVNP.BurstRAM CubeLengths

/-- The native strict-row traversal and comparison return exactly for an accurate
declaration. Each returned path has the true subtotal in every coordinate and
preserves all memory outside the row and the decoded selector scratch. -/
theorem strictTail_run {w n d blocks K h : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (i : Fin (n+1)) (sym : Symbols d)
    (B s base scratch bank stride claim saved : ℕ)
    (select : Packet n d blocks → Selector n K h) (declared : Fin (n+1) → ℕ)
    (ready : Owned.packetReady (blocks := blocks) i sym stride bank 0 (.ofWords r m))
    (cfg : SingleTally.Config i sym.val.1 sym.val.2 base (blocks*(h*B)) (.ofWords r m))
    (header : PacketTally.Header (readings m) (readings r 8) n K h base scratch s)
    (room : PacketTally.Rooms w n d blocks K h base scratch (readings r 8) bank stride)
    (ctr : singlePairTrials n d < 2^w) (labelFit : d^(n+1) ≤ 2^w) (dim : n+1 < 2^w)
    (packetFit : packetTrials n d blocks*(h*s) < 2^w)
    (stored : ∀ p : {p : Packet n d blocks // p.1.1 i = sym},
      SelectorRead.Stored (readings m) (bank+packetIndex p.val*stride) (select p.val))
    (fit : ∀ j : Fin (n+1), subtotals itemRow (crossCount B s select) i
      (Sym2.mk sym.val.1 sym.val.2) j < 2^w)
    (cleared : ∀ j : Fin (n+1), readings m (base+j.val) = 0)
    (h59 : readings r 59 = claim) (h61 : readings r 61 = saved)
    (claimWords : ∀ j : Fin (n+1), readings m (claim+j.val) = declared j)
    (outside : ∀ j : Fin (n+1), PacketTally.Outside n h base scratch (claim+j.val))
    (claimFit : claim+(n+1) ≤ 2^w) :
    TestRun pub mac (.seq (DeclaredRow.strict n) (.seq SingleTally.swap (.seq finish compare))) r m
      (DeclaredRow.strictCost i sym blocks B K h + (3+(5+((n+1)*(rowBody.slots+1)+1))))
      (∀ j, subtotals itemRow (crossCount B s select) i (Sym2.mk sym.val.1 sym.val.2) j = declared j)
      (fun z => z.reg 7 = saved ∧
        (∀ j : Fin (n+1), z.mem (base+j.val) =
          subtotals itemRow (crossCount B s select) i (Sym2.mk sym.val.1 sym.val.2) j) ∧
        ∀ x, PacketTally.Outside n h base scratch x → z.mem x = readings m x) := by
  let count := subtotals itemRow (crossCount B s select) i (Sym2.mk sym.val.1 sym.val.2)
  obtain ⟨es,t,mt,run,cost,rows,untouched⟩ := DeclaredRow.strict_run pub mac r m i sym B s
    base scratch bank stride select ready cfg header room ctr labelFit dim
    (fun j => by simpa only [cleared,Nat.zero_add] using packetFit)
    stored (fun j => by simpa only [cleared,Nat.zero_add] using fit j)
  have tallied : BoundedRun pub mac (DeclaredRow.strict n) r m (DeclaredRow.strictCost i sym blocks B K h)
      (fun z => (∀ j : Fin (n+1), z.mem (base+j.val) = count j) ∧
        (∀ x, PacketTally.Outside n h base scratch x → z.mem x = readings m x) ∧
        ∀ k : Reg, k ∈ ([0,1,5,9,22,23,59,61] : List Reg) → z.reg k = readings r k) :=
    ⟨es,t,mt,run,cost,fun j => by simpa only [cleared,Nat.zero_add,count] using rows j,untouched,
      fun k hk => congrArg Fin.val (run.keepsReg (strictTally_keeps n k hk))⟩
  apply ((tallied.asTest (strictTally_deterministic n)).seq
    (b := .seq SingleTally.swap (.seq finish compare)) (cb := 3+(5+((n+1)*(rowBody.slots+1)+1)))
    (ob := ∀ j, count j = declared j)
    (Q := fun z => z.reg 7 = saved ∧ (∀ j : Fin (n+1), z.mem (base+j.val) = count j) ∧
      ∀ x, PacketTally.Outside n h base scratch x → z.mem x = readings m x) ?_).mono le_rfl
    (by simp only [true_and,count]) (fun _ hz => hz)
  intro t mt ht
  obtain ⟨trueRow,keepMem,regs⟩ := ht
  change ∀ j : Fin (n+1), readings mt (base+j.val) = count j at trueRow
  have claimed (j : Fin (n+1)) : readings mt (claim+j.val) = declared j :=
    (keepMem _ (outside j)).trans (claimWords j)
  apply (swapFinishCompare_run pub mac t mt n base claim saved
    ((regs 0 (by decide)).trans cfg.zero) ((regs 1 (by decide)).trans cfg.one)
    ((regs 5 (by decide)).trans cfg.dim) ((regs 9 (by decide)).trans cfg.row)
    ((regs 59 (by decide)).trans h59) ((regs 61 (by decide)).trans h61) dim room.rowWords claimFit).mono le_rfl
  · simp only [trueRow,claimed]
  · rintro z ⟨hm,cursor⟩
    exact ⟨cursor, fun j => (congrFun hm _).trans (trueRow j),
      fun x hx => (congrFun hm x).trans (keepMem x hx)⟩

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
