import OAI.ThreeFlat.Diagonal.TickWorkspace
import OAI.ThreeFlat.Diagonal.InitialMetadataActual
import OAI.ThreeFlat.Diagonal.NavigationNodeArchive

namespace OAI
/-! # The initial node bank fits in S49 and preserves the complete mounted navigation prefix -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM HeaderScan TickWorkspace PhysicalStage
open scoped Classical
noncomputable section

private theorem twice_le_two_pow (n : ℕ) : 2*n≤2^n := by
  induction n with
  | zero=>decide
  | succ n ih=>
    cases n with
    | zero=>decide
    | succ k=>rw [pow_succ];have hh:=Nat.one_lt_two_pow (Nat.succ_ne_zero k);omega


variable (p : Parameters) (d : ℕ)
local notation "u" => p.age
local notation "W" => (16*u^10)
local notation "A" => p.archive d W

structure InitialSpace : Prop where
  records : (A).MetadataSpace W
  graphAfterHeader : (A).seed+64≤(A).cursor.graph
  graphBeforeWidths : (A).cursor.graph+6*((A).axes*d)≤(A).cursor.width
  widthsBeforeControl : (A).cursor.width+(A).axes*d*(A).remainingLanes≤(A).control
  controlBeforeRecords : (A).control<(A).initialRecords
  graphBeforeRecords : (A).cursor.graph+6*((A).axes*d)≤(A).initialRecords
  widthsBeforeRecords : (A).cursor.width+(A).axes*d*2^(A).axes≤(A).initialRecords
  degreeWord : 2*d<2^W
  laneWord : 2^(A).axes<2^W
  eight : 8<2^W
  graphBeforeHeap : (A).cursor.graph+6*((A).axes*d)≤(A).cursor.heap
  widthsBeforeHeap : (A).cursor.width+(A).axes*d*(A).remainingLanes≤(A).cursor.heap
  recordSpan : (A).metadataEnd≤TickWorkspace.base u 49+TickWorkspace.stride u

theorem Parameters.initial_space (hu : 40≤u) (fixed : d≤u) (depth : p.axes≤u^10+2*u^6) : InitialSpace p d := by
  let v:=2^(u^10)
  have pos : 0<u:=by omega
  have q:=Nat.pow_le_pow_right pos (by decide : 6≤8)
  have usq : u≤u^2:=Nat.le_self_pow (by decide) _
  have q':=Nat.mul_le_mul_left (u^8) (by omega : 2≤u^2)
  have ex : p.axes≤2*u^10 := by
    rw [←pow_add] at q'
    change u^8*2 ≤ u^10 at q'
    omega
  have bv : p.axes≤v := ex.trans (twice_le_two_pow _)
  have lane : 2^p.axes≤v^2 := by
    change _≤(2^(u^10))^2;rw [←pow_mul];apply Nat.pow_le_pow_right (by decide);omega
  have mul := Nat.mul_le_mul_left u hu
  have square := Nat.pow_le_pow_right pos (by decide : 2≤10)
  have st : 7+8*d≤v := by
    have le : 7+8*d≤u^10 := by rw [pow_two] at square;omega
    exact le.trans (Nat.lt_two_pow_self (n:=u^10)).le
  have stride : TickWorkspace.stride u=v^4 := rfl
  have big : 65≤v := by
    have h:=twice_le_two_pow (u^10);have : u≤u^10 := Nat.le_self_pow (by decide) _
    omega
  have sc : 65≤TickWorkspace.stride u :=
    big.trans (by rw [stride];exact Nat.le_self_pow (by decide) _)
  have allSite : (7+8*d)*(p.axes*2^p.axes)≤TickWorkspace.stride u := by
    rw [stride]
    calc
      _ ≤ v*(v*v^2) := Nat.mul_le_mul st (Nat.mul_le_mul bv lane)
      _ = _ := by ring
  have smallGraph : 4*(6*(p.axes*d))≤TickWorkspace.stride u := by
    have size : 6*(p.axes*d)≤v*v := by
      calc
        6*(p.axes*d)=p.axes*(6*d) := by ring
        _ ≤ p.axes*(7+8*d) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ v*v := Nat.mul_le_mul bv st
    calc
      _ ≤ (v*v)*(v*v) := Nat.mul_le_mul (Nat.mul_le_mul (by omega : 2≤v) (by omega : 2≤v)) size
      _ = _ := by rw [stride];ring
  have raw : p.axes*d*2^p.axes≤TickWorkspace.stride u :=
    (by calc
      _ = d*(p.axes*2^p.axes) := by ring
      _ ≤ (7+8*d)*(p.axes*2^p.axes) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := allSite)
  have sep := TickWorkspace.apart («u»:=u) (by decide : 20<21)
  have widthToControl := TickWorkspace.apart («u»:=u) (by decide : 21<40)
  have fromNext:= TickWorkspace.apart («u»:=u) (by decide : 22<40)
  have inNext:= TickWorkspace.apart («u»:=u) (by decide : 21<22)
  have recs:= TickWorkspace.apart («u»:=u) (by decide : 40<49)
  have fit := TickWorkspace.word_space («u»:=u) (i:=49) (by omega) (by omega)
  have ctrl : TickWorkspace.base u 40<TickWorkspace.base u 49:=by omega
  have a2 : 2^p.axes≤TickWorkspace.stride u := by
    rw [stride];exact lane.trans (Nat.pow_le_pow_right (by omega) (by decide : 2≤4))
  refine ⟨⟨?_,.inl ctrl,?_,?_⟩,?_,?_,?_,ctrl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ctrl.trans (by omega)
  · change TickWorkspace.base u 20+64≤TickWorkspace.base u 49;omega
  · change TickWorkspace.base u 49+(7+8*d)*(p.axes*2^p.axes)<_;omega
  · change TickWorkspace.base u 20+64≤TickWorkspace.base u 21+TickWorkspace.stride u / 4;omega
  · change TickWorkspace.base u 21+TickWorkspace.stride u / 4+6*(p.axes*d)≤TickWorkspace.base u 21+TickWorkspace.stride u / 2;omega
  · change TickWorkspace.base u 21+TickWorkspace.stride u / 2+p.axes*d*2^p.axes≤TickWorkspace.base u 40;omega
  · change TickWorkspace.base u 21+TickWorkspace.stride u / 4+6*(p.axes*d)≤TickWorkspace.base u 49;omega
  · change TickWorkspace.base u 21+TickWorkspace.stride u / 2+p.axes*d*2^p.axes≤TickWorkspace.base u 49;omega
  · have h : v≤TickWorkspace.stride u := by rw [stride];exact Nat.le_self_pow (by decide) _
    omega
  · change 2^p.axes<2^W;omega
  · omega
  · change TickWorkspace.base u 21+TickWorkspace.stride u / 4+6*(p.axes*d)≤TickWorkspace.base u 22;omega
  · have twice : 2*(p.axes*d*2^p.axes)≤TickWorkspace.stride u :=
      (calc _ = (2*d)*(p.axes*2^p.axes) := by ring
            _ ≤ (7+8*d)*(p.axes*2^p.axes) := Nat.mul_le_mul_right _ (by omega)
            _ ≤ _ := allSite)
    change TickWorkspace.base u 21+TickWorkspace.stride u / 2+p.axes*d*2^p.axes≤TickWorkspace.base u 22;omega
  · exact Nat.add_le_add_left allSite _


end
end ThreeFlat.Diagonal.NavigationPass

end OAI
