import OAI.Hierarchy.DescentSeedTokenLayout

namespace OAI
/-! # Native seed-token publication from zero-based census words in the original RAM -/
namespace Hierarchy.DescentSeedTokenTransposition
open DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM DescentSixParty.Chronology
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical
noncomputable section
variable {w b : ℕ} (base O H G X a A M : ℕ) (old : Bank)
local notation "splitAt" => cut base O G X a A M
local notation "length_" => H*chunks G M

variable (select : Fin H→Option (Option (Fin O))) (hub : Cell b)
local notation "columns" => Narrow.page base O G X a A M
local notation "publish" => DescentSeedTokenColumns.phase w G M a splitAt select hub columns
local notation "first" => Narrow.program base O G X a A M old w
local notation "firstTime" => Narrow.ticks base O G X a A M old
local notation "firstImage" => Narrow.image base O G X a A M old
local notation "output" => endAddress base O H G X a A M

def program (w : ℕ) := (Narrow.program base O G X a A M old w).seq
  (DescentSeedTokenColumns.phase w G M a splitAt select hub columns).program
def ticks (w : ℕ) := firstTime+(DescentSeedTokenColumns.phase w G M a splitAt select hub columns).ticks
def image (m : Memory w) := (publish).image (firstImage m)

theorem addresses :
    base ≤ splitAt ∧ splitAt≤ out base O H G X a A M ∧ out base O H G X a A M+X*length_≤ output :=
  ⟨by change base ≤ Narrow.cut base O G X a A M; rw [Narrow.cut_eq]; exact Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩

theorem page_ready (x : Fin X) (room : output < 2^w) :
    (page base O H G X a A M x).Fits w output ∧ length_≤(page base O H G X a A M x).size :=by
  let top:=out base O H G X a A M
  have le_end:=Nat.mul_le_mul_right length_ x.isLt.le
  change top+X*length_+2^Nat.clog 2 length_<2^w at room
  change (0<2^Nat.clog 2 length_ ∧ 2^Nat.clog 2 length_<2^w ∧
    top+x.val*length_+2^Nat.clog 2 length_≤ top+X*length_+2^Nat.clog 2 length_) ∧
    length_≤2^Nat.clog 2 length_
  exact ⟨⟨Nat.two_pow_pos _,by omega,by omega⟩,Nat.le_pow_clog (by decide) _⟩

local notation "cpu" => program base O H G X a A M old select hub w
local notation "elapsed" => ticks base O H G X a A M old select hub w
local notation "after" => image base O H G X a A M old select hub

theorem any (m : Memory w) (lanes : 0<M) (blocks : 0<X) (fit : old.Fits w base) (room : output<2^w) :
    (cpu).Exec m (after m) elapsed ∧ (∀i,i< base ∨ output≤ i→after m i=m i) ∧ CheapCode cpu :=by
  obtain ⟨pre,middle,last⟩:=addresses base O H G X a A M
  have dt:=last.trans_lt room
  have cutRoom:=middle.trans_lt ((Nat.le_add_right ..).trans_lt dt)
  obtain ⟨one,oldFrame,cheap⟩:=Narrow.any base O G X a A M old m lanes blocks fit cutRoom
  obtain ⟨two,newFrame⟩:=DescentSeedTokenColumns.any w G M a splitAt select hub columns (firstImage m)
    (fun x=>(Narrow.page_fits base O G X a A M x cutRoom).1) dt
  refine ⟨?_,?_,@cheap_seq w _ _ (@cheap) (@NativePhase.cheap _ publish)⟩
  · intro np nr nk machine pcs regs pubs exit rom advice cfg physical enter same
    exact Procedure.Exec.then one two machine pcs regs pubs exit rom advice cfg physical enter same
  · rintro i (lo|hi)
    · exact (newFrame _ (.inl (lo.trans_le pre))).trans (oldFrame _ (.inl lo))
    · exact (newFrame _ (.inr (last.trans hi))).trans
        (oldFrame _ (.inr (middle.trans ((Nat.le_add_right ..).trans (last.trans hi)))))

theorem issued (m : Memory w) (ys : Fin O→Fin (G*X)→Cell a) (oldLanes : 0<A) (lanes : 0<M)
    (blocks : 0<X) (fit : old.Fits w base) (capacity : O*chunks (G*X) A≤ old.size)
    (read : Reads old ys A m) (bits : b*M≤ w) (room : output<2^w) :
    (cpu).Exec m (after m) elapsed ∧
    (∀x,Reads (page base O H G X a A M x)
      (DescentSeedTokenColumns.values select hub (fun x v g=>ys v (finProdFinEquiv (g,x))) x) M (after m)) ∧
    (∀i,i< base ∨ output≤ i→after m i=m i) ∧ CheapCode cpu :=by
  obtain ⟨_,middle,last⟩:=addresses base O H G X a A M
  have dt:=last.trans_lt room
  have cutRoom:=middle.trans_lt ((Nat.le_add_right ..).trans_lt dt)
  have narrow:=Narrow.issued base O G X a A M old m ys oldLanes lanes blocks fit capacity read cutRoom
  obtain ⟨_,rows,_⟩:=DescentSeedTokenColumns.run w G M a splitAt select hub columns
    (fun x v g=>ys v (finProdFinEquiv (g,x))) (firstImage m)
    (fun x=>(Narrow.page_fits base O G X a A M x cutRoom).1) dt bits
    (fun x=>(Narrow.page_fits base O G X a A M x cutRoom).2) narrow.2.1
  obtain ⟨runtime,frame,cheap⟩:=any base O H G X a A M old select hub m lanes blocks fit room
  exact ⟨runtime,rows,frame,@cheap⟩

end
end Hierarchy.DescentSeedTokenTransposition

end OAI
