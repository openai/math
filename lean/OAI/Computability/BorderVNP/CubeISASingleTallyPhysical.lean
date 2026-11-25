import OAI.Computability.BorderVNP.CubeISASingleTallyRow

/-! # Preparing one physical orientation and computing its subtotal

The ordered row traversal starts from two specified grouping symbols. Before
a scan the native code loads its radix powers and resets its candidate cursor.
The opposite orientation uses the same row array and swaps the two symbols.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SingleTally

open Cube Cube.Physical Cube.Physical.Owned VPVNP.BurstRAM

variable {n d : ℕ}

/-- Persistent row metadata shared by the scans of both orientations. -/
structure Config (i : Fin (n+1)) (a b : Fin d) (rowBase bits : ℕ) (z : NatState) : Prop where
  zero : z.reg 0 = 0
  one : z.reg 1 = 1
  dim : z.reg 5 = n
  tail : z.reg 6 = d^n
  place : z.reg 7 = d^i.val
  row : z.reg 9 = rowBase
  radix : z.reg 10 = d
  left : z.reg 14 = a.val
  right : z.reg 15 = b.val
  count : z.reg 21 = bits

/-- Carry the configuration across a fragment preserving its registers. -/
theorem Config.transfer {i : Fin (n+1)} {a b : Fin d} {base bits : ℕ} {x y : NatState}
    (hx : Config i a b base bits x) (keep : ∀ r : Reg, r.val < 24 → r ≠ 18 → r ≠ 20 → y.reg r = x.reg r) :
    Config i a b base bits y :=
  ⟨(keep 0 (by decide) (by decide) (by decide)).trans hx.zero,
   (keep 1 (by decide) (by decide) (by decide)).trans hx.one,
   (keep 5 (by decide) (by decide) (by decide)).trans hx.dim,
   (keep 6 (by decide) (by decide) (by decide)).trans hx.tail,
   (keep 7 (by decide) (by decide) (by decide)).trans hx.place,
   (keep 9 (by decide) (by decide) (by decide)).trans hx.row,
   (keep 10 (by decide) (by decide) (by decide)).trans hx.radix,
   (keep 14 (by decide) (by decide) (by decide)).trans hx.left,
   (keep 15 (by decide) (by decide) (by decide)).trans hx.right,
   (keep 21 (by decide) (by decide) (by decide)).trans hx.count⟩

/-- Restore the ordered label loop's radix and dimensions and reset its cursor. -/
def reset : Code := .block [.copy 11 6,.copy 12 7,.copy 18 0,.binary .mul 19 11 11]

/-- Swap the endpoint groups before running the second orientation of a strict row. -/
def swap : Code := .block [.copy 50 14,.copy 14 15,.copy 15 50]

/-- The complete ordered orientation starting with the common metadata. -/
def oriented (n : ℕ) : Code := .seq reset (row n)

/-- Mathematical width contributed at a cut by the physical slots in this orientation. -/
def countAt {blocks K h : ℕ} (B s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (a b : Fin d) (j : Fin (n+1)) : ℕ :=
  ∑ k : SingleScan blocks (h*B) i a b, crossCount B s select (.inr (singleOrderedEquiv blocks (h*B) i a b k).val) j

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)

/-- The actual orientation computes precisely the physical singleton subtotal. -/
theorem oriented_run {blocks K h : ℕ} (i : Fin (n+1)) (a b : Fin d) (base B s : ℕ)
    (select : Packet n d blocks → Selector n K h) (r : Bank w) (m : Memory w)
    (cfg : Config i a b base (blocks*(h*B)) (.ofWords r m))
    (ctr : singlePairTrials n d < 2^w) (labelFit : d^(n+1) ≤ 2^w)
    (dim : n+1 < 2^w) (room : base+(n+1) ≤ 2^w)
    (cap : ∀ j : Fin (n+1), readings m (base+j.val)+countAt B s select i a b j < 2^w) :
    BoundedRun pub mac (oriented n) r m (4+rowCost i a b (blocks*(h*B))) fun z =>
      Config i a b base (blocks*(h*B)) z ∧
      (∀ j : Fin (n+1), z.mem (base+j.val) = readings m (base+j.val)+countAt B s select i a b j) ∧
      ∀ x, x < base ∨ base+(n+1) ≤ x → z.mem x = readings m x := by
  let st := NatState.ofWords r m
  have safe : reset.fixedSafe w (readings pub) st := by
    simpa (config := {decide := true}) [reset,Code.block,Code.fixedSafe,Code.safeReadOnly,
      Code.fixedEval,Code.evalNat,addressOpFits,st,cfg.tail,singlePairTrials] using ctr
  apply (reset.runFixed pub mac r m safe).seq
  intro u mm hu
  have hu' : NatState.ofWords u mm = reset.fixedEval (readings pub) st := hu
  have hm : readings mm = readings m := congrArg NatState.mem hu'
  have c : Config i a b base (blocks*(h*B)) (.ofWords u mm) := by
    rw [hu']
    rcases cfg with ⟨h0,h1,h5,h6,h7,h9,h10,h14,h15,h21⟩
    constructor <;> simp (config := {decide := true}) [reset,Code.block,Code.fixedEval,Code.evalNat,st, h0,h1,h5,h6,h7,h9,h10,h14,h15,h21]
  have ready : Owned.singleReady i a b 0 (.ofWords u mm) := by
    rw [hu']
    rcases cfg with ⟨h0,h1,h5,h6,h7,h9,h10,h14,h15,h21⟩
    simp (config := {decide := true}) [Owned.singleReady,reset,Code.block,Code.fixedEval,Code.evalNat,
      st,addressOp,singlePairTrials, h0,h1,h6,h7,h10,h14,h15]
  have wordfit (j : ℕ) (hj : j < n+1) :
      prefixImage i a b base (blocks*(h*B)) (readings mm) (singlePairTrials n d) (base+j) < 2^w := by
    exact (final_cut i a b base B s (readings mm) select ⟨j,hj⟩).trans_lt (hm ▸ cap ⟨j,hj⟩)
  apply ((row_run pub mac u mm i a b base (blocks*(h*B)) ready c.dim c.row c.count
    ctr labelFit dim room wordfit).complete trivial).mono le_rfl
  intro z hz
  refine ⟨c.transfer hz.2, fun j => ?_, fun x hx => ?_⟩
  · rw [hz.1,hm]
    exact final_cut i a b base B s (readings m) select j
  · rw [hz.1,hm]
    exact final_outside i a b base (blocks*(h*B)) (readings m) (singlePairTrials n d) x hx

/-- The reverse orientation reuses the same subtotal array and all numeric metadata. -/
theorem swap_run (i : Fin (n+1)) (a b : Fin d) (base bits : ℕ) (r : Bank w) (m : Memory w)
    (cfg : Config i a b base bits (.ofWords r m)) :
    BoundedRun pub mac swap r m 3 fun z => Config i b a base bits z ∧ z.mem = readings m := by
  apply (swap.runFixed pub mac r m (by simp [swap,Code.block,Code.fixedSafe,Code.safeReadOnly])).mono le_rfl
  rintro z rfl
  refine ⟨?_,rfl⟩
  rcases cfg with ⟨h0,h1,h5,h6,h7,h9,h10,h14,h15,h21⟩
  constructor <;> simp (config := {decide := true}) [swap,Code.block,Code.fixedEval,Code.evalNat, h0,h1,h5,h6,h7,h9,h10,h14,h15,h21]

end RoutingISA.SingleTally

end BorderVNP
end Computability
end OAI
