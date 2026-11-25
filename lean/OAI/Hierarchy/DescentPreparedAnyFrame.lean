import OAI.Hierarchy.DescentPackedMatchAny
import OAI.Hierarchy.DescentPackedMatchFuture

namespace OAI
/-! # A two-sided frame for the original prepared matcher on arbitrary words -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w : ℕ}

theorem base_le_end (s : Shape) (d r D p K H G M unit base seats : ℕ) :
    base≤(place s d r D p K H G M unit base seats).endAddr := by
  let P:=place s d r D p K H G M unit base seats
  have reach : base≤P.raw.base := ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have source : P.raw.base≤P.source.base := Nat.le_add_right ..
  have top : P.source.base≤P.layout.topology.base := Nat.le_add_right ..
  have counts : P.layout.topology.base≤P.layout.counts := Nat.le_add_right ..
  have cursor : P.layout.counts≤P.layout.cursor.base := Nat.le_add_right ..
  have out : P.layout.cursor.base≤P.layout.out := Nat.le_add_right ..
  exact reach.trans (source.trans (top.trans (counts.trans (cursor.trans (out.trans (Nat.le_add_right ..))))))

theorem below (s : Shape) (d r D p B K H G M unit base seats : ℕ) (field : Fin («fields» r D p)→Expr)
    (m : Memory w) (a : ℕ) (low : a<base) :
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
  have rawLow : a<P.raw.base :=
    low.trans_le (((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..))
  have sourceLow : a<P.source.base := rawLow.trans_le (Nat.le_add_right ..)
  have topLow : a<l.topology.base := sourceLow.trans_le (Nat.le_add_right ..)
  have countLow : a<l.counts := topLow.trans_le (Nat.le_add_right ..)
  have cursorLow : a<l.cursor.base := countLow.trans_le (Nat.le_add_right ..)
  have outLow : a<l.out := cursorLow.trans_le (Nat.le_add_right ..)
  have finalRead : ProfileTable.issued l R n top a=mid a :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl outLow)
  have cursorRead : mid a=starts a := PackedProfileCursor.below R l.counts l.cursor.base n starts a cursorLow
  have countsRead : starts a=top a := ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl countLow)
  have topRead : top a=rows a := ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl topLow)
  have gatherRead : rows a=warm a := ProbeStage.Native.columns_frame _ _ (.inl sourceLow)
  exact finalRead.trans (cursorRead.trans (countsRead.trans (topRead.trans (gatherRead.trans
    (frame s d r D p B K H G M R unit base m a (.inl low))))))

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

theorem passes_outside {w k cap : ℕ} (C : Chart k cap) (R : DescentSortedRoster.Chart)
    (base H G M D : ℕ) (m : Memory w) (a : ℕ) (away : a<base ∨ stop k H G M D cap base≤a) :
    ProtocolRAM.result (passes C R base H G M D) m a=m a := by
  let terms:=List.ofFn (expr C)
  let mid:=ProtocolRAM.image base (H*D) (DescentSortedRoster.code R D H) m
  have groupEnd : base+H*D ≤ stop k H G M D cap base := Nat.le_add_right ..
  have head : mid a=m a := ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a
    (away.imp_right (fun tail=> groupEnd.trans tail))
  have tail : a<fieldBase base H D ∨ fieldBase base H D+terms.length*(H*chunks G M)≤a := by
    rcases away with lower|upper
    · exact Or.inl (lower.trans_le (Nat.le_add_right ..))
    · exact Or.inr (by simpa only [terms,List.length_ofFn,stop] using upper)
  exact (ProbeStage.Native.columns_frame terms mid tail).trans head

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup DescentPackedColony ProtocolRAM
noncomputable section
variable {k D cap a short H G M w : ℕ}
variable (s : Shape) (K B unit romBase seats : ℕ) (P : Ports D)
    (act : Bank) (vals : Fin (2^k)→Bank) (wire : Fin (2^k)→Fin (2*cap)→Bank)
local notation "base" => Prepare.ROM.sortBase romBase k D cap a M H G
local notation "rbits" => Prepare.bits H G M
local notation "C" => Prepare.ROM.chart romBase D a M rbits act vals wire
local notation "Z" => Prepare.ROM.roster romBase k D cap a M H G (Prepare.ROM.headBits H D) P.roster
local notation "ps" => Prepare.passes C Z base H G M D
local notation "afterPrep" => Prepare.next k H G M D cap base
set_option quotPrecheck false in
local notation "field" => Gather.expr (Prepare.gatedBank (k:=k) base H G M D rbits)
  (Prepare.markedBank (k:=k) (cap:=cap) base H G M D rbits) {P with roster:=Prepare.rosterBank base H D} H
local notation "placed" => Gather.ROM.place s short (2^k) D (2*cap) K H G M unit afterPrep seats
local notation "warm" => Prepare.ROM.program w romBase k D cap a short M H G
local notation "matchCPU" => Gather.ROM.machine s short (2^k) D (2*cap) B K H G M unit afterPrep seats w field

theorem output_frame (m : Memory w) (x : ℕ) (away : x<romBase ∨ (placed).endAddr≤x) :
    let setup:=Prepare.ROM.after romBase k D cap a short M H G m
    let reached:=ProtocolRAM.result ps setup
    Gather.ROM.after s short (2^k) D (2*cap) B K H G M unit afterPrep seats field reached x=m x := by
  intro setup reached
  have installed : romBase+Prepare.staticWords k D cap a M H G≤base :=
    (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have begin_ : romBase≤base := (Nat.le_add_right ..).trans installed
  have inner : base≤Prepare.stop k H G M D cap base :=
    (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have outer : Prepare.stop k H G M D cap base≤afterPrep :=
    (Nat.le_add_right ..).trans (le_max_left ..)
  have finish := Gather.ROM.base_le_end s short (2^k) D (2*cap) K H G M unit afterPrep seats
  rcases away with lower|upper
  · have old := lower.trans_le begin_
    exact (Gather.ROM.below s short (2^k) D (2*cap) B K H G M unit afterPrep seats field reached x
        (old.trans_le (inner.trans outer))).trans
      ((Prepare.passes_outside C Z base H G M D setup x (.inl old)).trans
        (Prepare.ROM.frame romBase k D cap a short M H G m x (.inl lower)))
  · have high := outer.trans (finish.trans upper)
    exact (Gather.ROM.future s short (2^k) D (2*cap) B K H G M unit afterPrep seats field reached x upper).trans
      ((Prepare.passes_outside C Z base H G M D setup x (.inr high)).trans
        (Prepare.ROM.frame romBase k D cap a short M H G m x (.inr (installed.trans (inner.trans high)))))

theorem any_frame (input : Prepare.ROM.OldRoom act vals wire P.roster H G D M w romBase)
    (ports : Accessible P act H G M w romBase) (key : M*max (DescentSignedCableCodec.width D cap) short≤w/2)
    (large : Gather.matchUnit s short (2^k) D (2*cap)≤unit) (bits : unit*M≤w/2)
    (range : max H D<2^w) (space : (placed).endAddr<2^w) (m : Memory w) :
    let setup:=Prepare.ROM.after romBase k D cap a short M H G m
    let reached:=ProtocolRAM.result ps setup
    let final:=Gather.ROM.after s short (2^k) D (2*cap) B K H G M unit afterPrep seats field reached
    (((warm).seq (ProtocolRAM.program w ps)).seq matchCPU).Exec m
      final
      (((4+10*Prepare.staticWords k D cap a M H G)+clock ps)+Gather.ROM.ticks s short (2^k) D (2*cap) K H G M unit afterPrep seats field) ∧
      ∀x,x<romBase ∨ (placed).endAddr≤x → final x=m x := by
  intro setup reached final
  exact ⟨any s K B unit romBase seats P act vals wire input ports key large bits range space m,
    output_frame s K B unit romBase seats P act vals wire m⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared

end OAI
