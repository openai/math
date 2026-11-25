import OAI.Computability.BorderVNP.CubePhysicalDeclaration
import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Counting the selected directions of one physical cube packet

The selector supplies one directed edge per slot. A word encodes its vertex
followed by its direction in mixed radix, so its remainder modulo the cube
dimension is the candidate cut. Each slot causes one increment by the edge
width in the contiguous row array, irrespective of the size of the tensor table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RowAccum

open RoutingISA VPVNP.BurstRAM VPVNP.MotifBase Physical
open scoped BigOperators

/-- The physical edge-width sum in a direction is the sum of selector slots in that direction. -/
theorem packet_direction_sum {n d blocks h K : ℕ} (b s : ℕ)
    (select : Packet n d blocks → Selector n K h) (p : Packet n d blocks) (j : Fin (n+1)) :
    crossCount b s select (.inl p) j = ∑ k : Fin h, if ((select p).2 k).2 = j then s else 0 := by
  classical
  simp only [crossCount,payload]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨v,c⟩ := (select p).2 k
  by_cases eq : c = j
  · subst c
    simp [onEdge]
  · simp [onEdge, Ne.symm eq,eq]

/-- RAM image after the first `i` selected directions have been tallied. -/
def packetImage (original : ℕ → ℕ) (base width : ℕ) (dir : ℕ → ℕ) (i a : ℕ) : ℕ :=
  original a + ∑ k ∈ Finset.range i, if a = base + dir k then width else 0

private theorem packetImage_succ (old : ℕ → ℕ) (base width : ℕ) (dir : ℕ → ℕ) (i : ℕ) :
    Function.update (packetImage old base width dir i) (base+dir i)
      (packetImage old base width dir i (base+dir i) + width) =
      packetImage old base width dir (i+1) := by
  funext a
  by_cases eq : a = base+dir i <;>
    simp [packetImage,eq,Finset.sum_range_succ,Nat.add_assoc]

/-- The final RAM image adds exactly the physical packet's contribution in each candidate cut. -/
theorem packetImage_crossCount {n d blocks K h : ℕ} (b s base : ℕ)
    (select : Packet n d blocks → Selector n K h) (p : Packet n d blocks) (old dir : ℕ → ℕ)
    (digits : ∀ k : Fin h, dir k = ((select p).2 k).2.val) (j : Fin (n+1)) :
    packetImage old base s dir h (base+j) = old (base+j) + crossCount b s select (.inl p) j := by
  rw [packet_direction_sum, packetImage, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [digits, Nat.add_left_cancel_iff, Fin.val_inj]
  split <;> split <;> simp_all

/-- A fixed packet step. Registers 45–49 contain row base, dimension, selector base,
slot count and width. The cursor is 50, and 55 holds one. -/
def packetStep : RoutingISA.Code := .block [
  .binary .add 51 47 50, .load 52 51, .binary .mod 52 52 46,
  .binary .add 53 45 52, .load 54 53, .binary .add 54 54 49, .store 53 54,
  .binary .add 50 50 55]

/-- Initialize the two private loop registers and tally every selected slot. -/
def packetLoop : RoutingISA.Code := .seq (.block [.constant 50 0,.constant 55 1])
  (.whileLt 50 48 packetStep)

private def packetReady (base dim src count width : ℕ) (z : NatState) : Prop :=
  z.reg 45 = base ∧ z.reg 46 = dim ∧ z.reg 47 = src ∧ z.reg 48 = count ∧ z.reg 49 = width

private theorem packetReady_keep {base dim src count width : ℕ} {z : NatState} {c : RoutingISA.Code}
    (hz : packetReady base dim src count width z) (hc : c.protects 50 = true) (env : Arg → ℕ) :
    packetReady base dim src count width (c.fixedEval env z) := by
  obtain ⟨a,b,d,e,f⟩ := hz
  exact ⟨(c.fixedEval_protected env z hc 45 (by decide)).trans a,
    (c.fixedEval_protected env z hc 46 (by decide)).trans b,
    (c.fixedEval_protected env z hc 47 (by decide)).trans d,
    (c.fixedEval_protected env z hc 48 (by decide)).trans e,
    (c.fixedEval_protected env z hc 49 (by decide)).trans f⟩

/-- The actual packet fragment reads every compact edge ordinal and writes its width to
the corresponding candidate total. It leaves every other address intact. -/
theorem packetLoop_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (base dim src count width : ℕ)
    (rb : (r 45).val = base) (rd : (r 46).val = dim) (rs : (r 47).val = src)
    (rc : (r 48).val = count) (rwth : (r 49).val = width)
    (hd : 0 < dim) (room : base+dim ≤ 2^w) (inputs : src+count ≤ 2^w)
    (disjoint : src+count ≤ base ∨ base+dim ≤ src)
    (fit : ∀ j < dim, readings m (base+j) + count*width < 2^w) :
    BoundedRun pub macros packetLoop r m (9*count+3) (fun z =>
      z.mem = packetImage (readings m) base width (fun k => (m (src+k)).val % dim) count) := by
  let old := readings m
  let dir k := (m (src+k)).val % dim
  let image := packetImage old base width dir
  let P i z := packetReady base dim src count width z ∧ z.reg 50 = i ∧ z.reg 55 = 1 ∧ z.mem = image i
  have dlt (i) : dir i < dim := Nat.mod_lt _ hd
  have oneFit : 1 < 2^w := (Nat.succ_le_of_lt hd).trans_lt (rd ▸ (r 46).isLt)
  have regs i z (hz : P i z) : z.reg 50 = i ∧ z.reg 48 = count := ⟨hz.2.1,hz.1.2.2.2.1⟩
  have step (i : ℕ) (hi : i < count) (t : Bank w) (mt : Memory w) (hp : P i (.ofWords t mt)) :
      BoundedRun pub macros packetStep t mt 8 (P (i+1)) := by
    let z := NatState.ofWords t mt
    have hz : packetReady base dim src count width z := hp.1
    obtain ⟨b,d,s,_,v⟩ := hz
    have idx : z.reg 50 = i := hp.2.1
    have one : z.reg 55 = 1 := hp.2.2.1
    have mem : z.mem = image i := hp.2.2.2
    have no (k : ℕ) : src+i ≠ base+dir k := by have := dlt k; omega
    have input : z.mem (src+i) = (m (src+i)).val := by simp [mem,image,packetImage,no,old,readings]
    have da : z.mem (src+i) % dim = dir i := congrArg (· % dim) input
    have acc : z.mem (base+dir i) + width < 2^w := by
      have le : ∑ k ∈ Finset.range i, (if base+dir i = base+dir k then width else 0) ≤ i*width := by
        simpa using Finset.sum_le_sum (s := Finset.range i)
          (g := fun _ => width) (f := fun k => if base+dir i = base+dir k then width else 0)
          (fun _ _ => by split <;> omega)
      have mul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at mul
      have cap := fit _ (dlt i)
      change readings m _ + _ < _ at cap
      rw [mem]
      change readings m _ + _ + width < _
      omega
    have aFit : src+i < 2^w := by omega
    have bFit : base+dir i < 2^w := by have := dlt i; omega
    have iFit : i+1 < 2^w := (Nat.succ_le_of_lt hi).trans_lt (rc ▸ (r 48).isLt)
    have safe : packetStep.fixedSafe w (readings pub) z := by
      simp (config := {decide := true}) [packetStep, RoutingISA.Code.block,RoutingISA.Code.fixedSafe,
        RoutingISA.Code.fixedEval,RoutingISA.Code.safeReadOnly,RoutingISA.Code.evalNat,
        addressOpFits,addressOp,b,d,s,v,idx,one,da,hd,aFit,bFit,acc,iFit]
    apply (packetStep.runFixed pub macros t mt safe).mono (by decide)
    rintro y rfl
    change P (i+1) (packetStep.fixedEval (readings pub) z)
    refine ⟨packetReady_keep hp.1 (by decide) _,?_,?_,?_⟩
    · simp (config := {decide := true}) [packetStep, RoutingISA.Code.block, RoutingISA.Code.fixedEval,
        RoutingISA.Code.evalNat,addressOp,idx,one]
    · simp (config := {decide := true}) [packetStep, RoutingISA.Code.block, RoutingISA.Code.fixedEval,
        RoutingISA.Code.evalNat,one]
    · simp (config := {decide := true}) [packetStep, RoutingISA.Code.block, RoutingISA.Code.fixedEval,
        RoutingISA.Code.evalNat,addressOp,b,d,s,v,idx,da]
      rw [mem]
      exact packetImage_succ ..
  let init := RoutingISA.Code.block [.constant 50 0,.constant 55 1]
  have ready : packetReady base dim src count width (.ofWords r m) := ⟨rb,rd,rs,rc,rwth⟩
  have run := (init.runFixed pub macros r m (by
    simp [init, RoutingISA.Code.block, RoutingISA.Code.fixedSafe, RoutingISA.Code.safeReadOnly,oneFit])).seq
    (b := .whileLt 50 48 packetStep) (t := (count-0)*(8+1)+1) (Q := P count)
    (fun t mt eq => run_counted_loop pub macros 50 48 packetStep count 8 P regs step 0 (by omega) t mt (by
      rw [eq]
      refine ⟨packetReady_keep ready (by decide) _,?_,?_,?_⟩ <;>
        simp (config := {decide := true}) [init,RoutingISA.Code.block,RoutingISA.Code.fixedEval,
          RoutingISA.Code.evalNat,image,old,NatState.ofWords]
      funext a
      simp [packetImage]))
  exact run.mono (by change 2+(count-0)*(8+1)+1 ≤ _; omega) fun _ hz => hz.2.2.2

end Cube.RowAccum

end BorderVNP
end Computability
end OAI
