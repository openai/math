import OAI.Hierarchy.DescentPackedMatchInstalled

namespace OAI
/-! # Later original selector words survive every native matching pass -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

theorem future (s : Shape) (d r D p B K H G M unit base seats : ℕ) (field : Fin (fields r D p)→Expr)
    (m : Memory w) (a : ℕ) (high : (place s d r D p K H G M unit base seats).endAddr≤a) :
    after s d r D p B K H G M unit base seats field m a=m a := by
  let n:=(K*H)*chunks G M
  let R:=M*s.pairs
  let P:=place s d r D p K H G M unit base seats
  let l:=P.layout
  let c:=chart s d r D p K H G M R unit base P.source
  let warm:=mounted s d r D p B K H G M R unit base m
  let rows:=ProtocolRAM.result (passes c.joins field c.desc c.mask P.source.base H G M) warm
  let top:=PackedMatch.result c.lookup l.topology.base (K*H) G M rows
  let starts:=ProfileTable.boot l n top
  let mid:=ProfileTable.middle l R n top
  have past : l.out+n≤a:=high
  have cp : l.cursor.base+l.cursor.size=l.out:=rfl
  have cap : 2*(n+1)≤l.cursor.size:=column_size ..
  have ptr : PackedProfileCursor.addr l.cursor.base n+2≤a := by dsimp only [PackedProfileCursor.addr];omega
  have countEnd : l.counts+n=l.cursor.base:=rfl
  have tc : l.topology.base+l.topology.size=l.counts:=rfl
  have ts : n≤l.topology.size:=column_size ..
  have sc : P.source.base+P.source.size=l.topology.base:=rfl
  have ss : n≤P.source.size:=column_size ..
  have rawEnd : P.raw.base+P.raw.size=P.source.base:=rfl
  have dict : base+size (fields r D p) K H G M unit≤P.raw.base :=
    (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have finalRead : ProfileTable.issued l R n top a=mid a :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr past)
  have cursorRead : mid a=starts a:=PackedProfileCursor.above R l.counts l.cursor.base n starts a ptr
  have countsRead : starts a=top a:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr (by omega))
  have topRead : top a=rows a:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr (by omega))
  have gatherRead : rows a=warm a := by
    apply ProbeStage.Native.columns_frame _ _ (.inr ?_)
    rw [allExprs,List.length_ofFn,←Nat.mul_assoc]
    change P.source.base+n≤a
    omega
  exact finalRead.trans (cursorRead.trans (countsRead.trans (topRead.trans (gatherRead.trans
    (frame s d r D p B K H G M R unit base m a (.inr (by omega)))))))

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM

end OAI
