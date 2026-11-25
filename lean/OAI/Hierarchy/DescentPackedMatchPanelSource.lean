import OAI.Hierarchy.DescentPackedMatchInstalled

namespace OAI
/-! # The actual assembled donor register survives the matcher -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

def donorExpr (s : Shape) (d r D p K H G M unit base seats : ℕ)
    (field : Fin (fields r D p)→Expr) :=
  let P:=place s d r D p K H G M unit base seats
  assembly (chart s d r D p K H G M (M*s.pairs) unit base P.source).joins field

structure DonorWord {d r D p H G M w : ℕ} (op : Expr) (stop : ℕ)
    (panel : Fin H→Fin G→Panel r D p d) (m : Memory w) : Prop where
  fits : op.Fits w stop
  read : Source op (fun h g=>encodePanel (panel h g)) M m

theorem DonorWord.moved {d r D p H G M w stop : ℕ} {op : Expr} {panel : Fin H→Fin G→Panel r D p d}
    {m o : Memory w} (old : DonorWord (M:=M) op stop panel m) (frame : ∀i<stop,o i=m i) :
    DonorWord (M:=M) op stop panel o :=
  ⟨old.fits,fun j=>(eval_below op _ m o old.fits frame).trans (old.read j)⟩

theorem panel_source (s : Shape) (d r D p B K H G M unit base seats w : ℕ)
    (field : Fin (fields r D p)→Expr) (panel : Fin H→Fin G→Panel r D p d) (m : Memory w)
    (large : matchUnit s d r D p≤unit) (shifts : unit*M≤w/2)
    (room : (place s d r D p K H G M unit base seats).endAddr<2^w)
    (low : ∀i,(field i).Fits w base) (input : ∀i,Source (field i) (fun h g=>terrain panel h g i) M m) :
    DonorWord (M:=M) (donorExpr s d r D p K H G M unit base seats field)
      (place s d r D p K H G M unit base seats).source.base panel (after s d r D p B K H G M unit base seats field m) := by
  let R:=M*s.pairs
  let P:=place s d r D p K H G M unit base seats
  let c:=chart s d r D p K H G M R unit base P.source
  let n:=(K*H)*chunks G M
  let l:=P.layout
  let warm:=mounted s d r D p B K H G M R unit base m
  let rows:=ProtocolRAM.result (passes c.joins field c.desc c.mask P.source.base H G M) warm
  let top:=PackedMatch.result c.lookup l.topology.base (K*H) G M rows
  let boot:=ProfileTable.boot l n top
  let mid:=ProfileTable.middle l R n top
  have bds:=(arranged s d r D p K H G M unit base seats w large shifts room).gather field low
  have chips:=(loaded s d r D p B K H G M unit base P.source m large).joins
  have source (i) : Source (field i) (fun h g=>terrain panel h g i) M warm :=
    fun j=>(eval_below _ _ m warm (low i)
      (fun a ha=>frame s d r D p B K H G M R unit base m a (.inl ha))).trans (input i j)
  have built : DonorWord (M:=M) (assembly c.joins field) P.source.base panel warm :=
    ⟨Gather.fits c.joins field _ bds _,assembled c.joins field _ bds panel warm chips source⟩
  apply built.moved
  intro i hi
  have sourceEnd : P.source.base+P.source.size=l.topology.base:=rfl
  have topEnd : l.topology.base+l.topology.size=l.counts:=rfl
  have cntEnd : l.counts+n=l.cursor.base:=rfl
  have cursorEnd : l.cursor.base+l.cursor.size=l.out:=rfl
  have s1 : ProfileTable.issued l R n top i=mid i:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))
  have s2 : mid i=boot i:=PackedProfileCursor.below R l.counts l.cursor.base n boot i (by omega)
  have s3 : boot i=top i:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))
  have s4 : top i=rows i:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))
  exact s1.trans (s2.trans (s3.trans (s4.trans (ProbeStage.Native.columns_frame _ _ (.inl hi)))))

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM

end OAI
