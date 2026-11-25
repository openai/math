import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.Hierarchy.GridPinNativeLoops
import OAI.Hierarchy.GridPinAddressImage

namespace OAI
/-! The receiver extracts the in-tick address of each active original bit interval.
    A four-word row retains its first three words and stores the address in its last word. -/

namespace Hierarchy.GridPinReceiverIntervals
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open FactorBucketRAM GridThrough
open scoped Fin.CommRing

variable {W : ℕ}

def words (W lanes blocks pins intervals : ℕ) : Parameters W :=
  ![lanes,blocks,pins,intervals,0,0,0,0,0,0,0,0]

def step (v : Parameters W) (i : Word W) (m : Memory W) : Memory W :=
  writeMemory m (v 3 + 4*i + 3) (BinaryOp.mod.eval (m (v 1+i).val) (v 2))

def ops : List (Op 14 12) :=
  [.publicWord 2 1,.binary .add 2 2 0,.read 3 2,.publicWord 4 2,.binary .mod 3 3 4,
   .binary .add 5 0 0,.binary .add 5 5 5,.publicWord 6 3,.binary .add 6 6 5,.constant 7 3,
   .binary .add 6 6 7,.write 6 3,.constant 13 1,.binary .add 0 0 13]

private theorem effect {R K : ℕ} (reg : Fin 14 ↪ Fin R) (pub : Fin 12 → Fin K)
    (v : Fin K → Word W) (s : Word W) (rs : Regs W R) (m : Memory W) :
    Executes ops step reg pub v s rs m := by
  simp [Executes,ops,step,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]
  congr 2; ring

def program (W lanes blocks pins intervals : ℕ) :=
  FactorBucketRAM.procedure ops (words W lanes blocks pins intervals)

theorem execute (lanes blocks pins intervals : ℕ) (m : Memory W) (fit : lanes<2^W) :
    (program W lanes blocks pins intervals).Exec m
      (iterRows step (words W lanes blocks pins intervals) m lanes) (3+15*lanes) := by
  let v:= words W lanes blocks pins intervals
  have spec : (FactorBucketRAM.procedure ops v).Spec (fun _=>True)
      (fun mem out=>out=iterRows step v mem lanes) (3+lanes*(1+ops.length)) :=
    GridPinNativeLoops.loop_spec ops step (fun _ _ _ _ _ _=>effect ..) v lanes fit rfl
  have h : (FactorBucketRAM.procedure ops v).Exec m (iterRows step v m lanes) (3+lanes*(1+ops.length)) :=
    Procedure.Spec.exec (A:=FactorBucketRAM.procedure ops v) (f:=fun mem=>iterRows step v mem lanes) spec m trivial
  change (FactorBucketRAM.procedure ops v).Exec m (iterRows step v m lanes) (3+15*lanes)
  rw [←show 3+lanes*(1+ops.length)=3+15*lanes by change 3+lanes*15=3+15*lanes;rw [Nat.mul_comm lanes]]
  exact @h

def RowFrame (lanes intervals : ℕ) (m o : Memory W) :=
  ∀ a, (∀ b<lanes, a≠intervals+4*b+3) → o a=m a

def Readback (lanes blocks pins intervals : ℕ) (m o : Memory W) :=
  RowFrame lanes intervals m o ∧ ∀ b<lanes,
    o (intervals+4*b+3)=(((m (blocks+b)).val%pins:ℕ):Word W)

private theorem natural (lanes blocks pins intervals i : ℕ) (m : Memory W)
    (readFit : blocks+i<2^W) (writeFit : intervals+4*i+3<2^W) (pinFit : pins<2^W) :
    step (words W lanes blocks pins intervals) (i:Word W) m =
      Function.update m (intervals+4*i+3) (((m (blocks+i)).val%pins:ℕ):Word W) := by
  change writeMemory m ((intervals:Word W)+4*(i:Word W)+3)
    (BinaryOp.mod.eval (m ((blocks:Word W)+(i:Word W)).val) (pins:Word W))=_
  have dest : (intervals:Word W)+4*(i:Word W)+3=((intervals+4*i+3:ℕ):Word W) := by push_cast; rfl
  have src : (blocks:Word W)+(i:Word W)=((blocks+i:ℕ):Word W) := by push_cast; rfl
  rw [dest,src,Fin.val_cast_of_lt readFit,GridPassageRAMRow.writeMemory_nat _ _ writeFit]
  simp [BinaryOp.eval,Fin.val_cast_of_lt pinFit]

theorem readback (lanes blocks pins intervals : ℕ) (_laneFit : lanes<2^W)
    (readFit : blocks+lanes≤2^W) (writeFit : intervals+4*lanes≤2^W) (pinFit : pins<2^W)
    (sep : ∀ b<lanes, ∀ j<lanes, blocks+b≠intervals+4*j+3) :
    ∀ (input : Memory W), Readback lanes blocks pins intervals input
      (iterRows step (words W lanes blocks pins intervals) input lanes) := by
  intro input
  let v := words W lanes blocks pins intervals
  have inv (i : ℕ) (hi : i≤lanes) : Readback i blocks pins intervals input
      (iterRows step v input i) := by
    induction i with
    | zero =>
      exact ⟨fun _ _=>rfl,by simp⟩
    | succ i ih =>
      have ⟨outside, earlier⟩ := ih (by omega)
      have update := natural lanes blocks pins intervals i (iterRows step v input i)
        (by omega) (by omega) pinFit
      rw [iterRows]
      change Readback (i+1) blocks pins intervals input (step (words W lanes blocks pins intervals)
        (i:Word W) (iterRows step v input i))
      rw [update]
      constructor
      · intro a ha
        rw [Function.update_of_ne (ha i (by omega))]
        exact outside a (fun j hj=>ha j (by omega))
      · intro b hb
        by_cases eq : b=i
        · subst b
          rw [Function.update_self, outside (blocks+i) (fun j hj=> sep i (by omega) j (by omega))]
        · rw [Function.update_of_ne (show intervals+4*b+3≠intervals+4*i+3 by omega)]
          exact earlier b (by omega)
  exact inv lanes le_rfl

/-- The loop uses the receiver's own class/bucket scan and writes one word per
active original bit interval. -/
theorem program_spec (lanes blocks pins intervals : ℕ) (laneFit : lanes<2^W)
    (readFit : blocks+lanes≤2^W) (writeFit : intervals+4*lanes≤2^W) (pinFit : pins<2^W)
    (sep : ∀ b<lanes, ∀ j<lanes, blocks+b≠intervals+4*j+3) :
    (program W lanes blocks pins intervals).Spec (fun _=>True) (Readback lanes blocks pins intervals)
      (3+15*lanes) := by
  let v := words W lanes blocks pins intervals
  have spec : (FactorBucketRAM.procedure ops v).Spec (fun _=>True)
      (fun mem out=>out=iterRows step v mem lanes) (3+lanes*(1+ops.length)) :=
    GridPinNativeLoops.loop_spec ops step (fun _ _ _ _ _ _=>effect ..) v lanes laneFit rfl
  intro P R K M pc reg pub exit installed values config input start h
  obtain ⟨t,ht,c,o,run,atExit,endEq⟩ := spec M pc reg pub exit installed values config input start h
  refine ⟨t,?_,c,o,run,atExit,?_⟩
  · calc
      t ≤ 3+lanes*(1+ops.length) := ht
      _ = _ := by change 3+lanes*15=3+15*lanes; rw [Nat.mul_comm lanes]
  · rw [endEq]
    exact readback lanes blocks pins intervals laneFit readFit writeFit pinFit sep input

/-- At an original bucket's first bit, its absolute address modulo pins-per-tick
is precisely the local pin after the tick header and earlier factors. -/
theorem slot_at_bucket {k n q d S N lanes blocks intervals span : ℕ}
    (layout : FactorPinIntervals.Layout (Cell k n×Fin q) S N d)
    (input out : Memory W) (installed : Readback lanes blocks d intervals input out)
    (fit : (n+1)^k*(q*d)≤2^W)
    (read : ∀ j : Fin S, input (blocks+j.val/span)+((j.val%span:ℕ):Word W)=
      ((GridPinAddressImage.code (layout.address j)).val:Word W))
    (b : Fin lanes) (j : Fin S) (atLane : j.val/span=b.val) (first : j.val%span=0) :
    out (intervals+4*b.val+3)=((layout.slot j).val:Word W) := by
  have raw := read j
  rw [atLane,first,Nat.cast_zero,add_zero] at raw
  rw [installed.2 b.val b.isLt,raw,Fin.val_cast_of_lt ((GridPinAddressImage.code (layout.address j)).isLt.trans_le fit)]
  change (((GridPinAddressImage.code (layout.tick j,layout.slot j)).val%d:ℕ):Word W)=_
  rw [GridPinAddressImage.code_val,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (layout.slot j).isLt]

end Hierarchy.GridPinReceiverIntervals

end OAI
