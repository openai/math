import OAI.Hierarchy.DescentPackedWalshResident
import OAI.Hierarchy.DescentDyadicReductionAny

namespace OAI
/-! # All estimator depth rows execute on every input word -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

namespace Column
variable (P : Plan) {w : ℕ}
local notation "k" => P.axis
local notation "l" => P.laneBits P.depth
local notation "s" => P.bits+P.depth
local notation "K" => P.chunks P.depth

theorem any_publish (root first extract out : ℕ) (m : Memory w)
    (static : P.headerAt root P.depth≤first) (early : extract+size k s l≤first)
    (later : P.dataAt first (P.depth+1)≤out) (room : out+2^k<2^w) :
    (publishCode P w root first extract out).Exec m (publishMem P root first extract out m)
      (publishTime P root first extract) := by
  have outFit : out<2^w:=(Nat.le_add_right ..).trans_lt room
  have dataRoom:=later.trans_lt outFit
  have rows : P.dataAt first P.depth+K≤out := by
    have h : P.hosts P.depth=1:=by simp [Plan.hosts]
    change P.dataAt first P.depth+P.hosts P.depth*K≤out at later
    simpa [h] using later
  have start : first≤out:=(P.data_mono first (Nat.zero_le _)).trans later
  have fixed:=early.trans start
  have banksFit (B : Bank) (ends_ : B.base+B.size≤out) : B.Fits w out :=
    ⟨Nat.two_pow_pos _,((Nat.le_add_left B.size B.base).trans ends_).trans_lt outFit,ends_⟩
  let B:=banks extract k K s l (input P first)
  have old : B.data.Fits w out:=banksFit _ rows
  have extent : 2*2^k≤ size k s l:=Nat.le_add_right ..
  have idx : B.chunks.Fits w out:=banksFit _ (by change extract+2^k≤_;omega)
  have offset : B.offsets.Fits w out:=banksFit _ (by change extract+2^k+2^k≤_;omega)
  have matchTerm : (scanRow B l).Fits w out:=by
    by_cases scalar : l=0
    · rw [scanRow,ite_eq_left scalar]
      exact ⟨old,idx,trivial⟩
    · have table : B.lut.Fits w out:=banksFit _ (by
        change extract+2*2^k+2^(l+s*2^l)≤_
        simpa only [size,ite_eq_right scalar,Nat.add_assoc] using fixed)
      rw [scanRow,ite_eq_right scalar]
      exact ⟨table,⟨old,idx,trivial⟩,offset,trivial⟩
  let pm:=P.pad first m
  let final:=P.state root first pm P.depth
  intro labels regs slots machine
  exact Procedure.Exec.then (Procedure.Exec.then
    (P.any_pad first m ((P.data_mono first (by omega : 1≤P.depth+1)).trans_lt dataRoom))
    (P.any_reduce root first pm P.depth le_rfl static dataRoom))
    (@scan_exec w out (2^k) (scanRow B l) final matchTerm room) machine
end Column

namespace EstimatorArena
variable (E : EstimatorArena) {w : ℕ}

theorem calendar_any (fits : E.Fits w) (_payload : E.payload≤w) (_stageWidth : E.dim+1≤2^w) (m : Memory w) :
    (E.calendar.code E.plan w E.hosts (E.dim+1)).Exec m
      (E.calendar.state E.plan E.hosts m (E.dim+1)) (E.calendar.ticks E.plan E.hosts (E.dim+1)) := by
  have ⟨_,_,ord,transform,square,start,numerator⟩:=E.areas
  have small : E.transformAt≤E.inputEnd:=transform.trans (square.trans (start.trans numerator))
  have whole (j : ℕ) (live : j≤E.dim+1) :
      (E.calendar.code E.plan w E.hosts j).Exec m (E.calendar.state E.plan E.hosts m j)
        (E.calendar.ticks E.plan E.hosts j) := by
    induction j with
    | zero=>
      have cap : E.inputEnd<2^w:=by
        have first : E.inputEnd≤E.solveAt:=Nat.le_add_right ..
        exact first.trans_lt fits.bounded
      have same : image E.inputEnd 0 .row m=m:=by
        funext a
        exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)
      have run : (scan w E.inputEnd 0 .row).Exec m (image E.inputEnd 0 .row m)
          (4+0*(2*Expr.row.work+4)) :=
        @scan_exec w E.inputEnd 0 .row m trivial (by simpa only [Nat.add_zero] using cap)
      rw [same,Nat.zero_mul,Nat.add_zero] at run
      exact @run
    | succ j ih=>
      let current:=E.calendar.state E.plan E.hosts m j
      let first:=E.scratch j
      let weighted:=image first (E.hosts*2^E.high) (Weight.expr E.weights j) current
      have room:=(E.shared_room fits j live).1
      have legal : (Weight.expr E.weights j).Fits w first :=
        ⟨⟨room.depth,room.owner,trivial⟩,trivial,⟨room.results,⟨room.numer,trivial⟩,room.shift,
          room.gain,room.owner,trivial⟩,trivial⟩
      have weight : (scan w first (E.hosts*2^E.high) (Weight.expr E.weights j)).Exec current weighted
          (4+94*(E.hosts*2^E.high)) := by
        rw [Nat.mul_comm 94,←Weight.tariff E.weights j]
        exact @scan_exec w _ _ _ _ legal room.endBound
      have input : E.inputEnd≤first:=Nat.le_add_right ..
      have tail : E.bank j+2^E.dim<2^w:=(E.includes_bank j live).trans_lt fits.bounded
      intro labels regs slots machine
      exact Procedure.Exec.then (ih (Nat.le_of_succ_le live))
        (Procedure.Exec.then weight (Column.any_publish E.plan E.reduceAt first E.orderAt (E.bank j) weighted
          (ord.trans (small.trans input)) (small.trans input) (E.packed_before j).le tail)) machine
  exact @whole (E.dim+1) le_rfl

end EstimatorArena
end
end Hierarchy.DescentPackedWalsh

end OAI
