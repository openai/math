import OAI.ThreeFlat.Diagonal.CompressorDemandImage

namespace OAI
/-! # The exact six-pass image of an old shrinking-stage graph -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan Placement
open scoped Fin.NatCast
variable {B H : Type} [DecidableEq B] [AddCommGroup H] [Fintype B] [Fintype H] {w N t l : ℕ}
variable {S : Graph.Stage} {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B ≃ Fin N} {p : Pointers} {cell : Word w} {m : Memory w}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
local notation "x" => dims S N t l
local notation "C" => incoming S N p

theorem Old.pre_image (old : Old S P b p cell prior m) (space : Fresh (dims S N t l) p cell.val) (pub : Fin 1→Word w)
    (hc : 2≤S.colors) (palette : 2*S.degree+1≤2^w) (tw : t≤w) (eight : 8<2^w) (oneWord : (1:Word w)≠0)
    (colorCode : ∀v,(P.color v).val=(Ordered.colors P.slots b.symm v).val)
    (tagCode : ∀v,P.offset v=Ordered.offsets P.slots (shift P) b.symm (tagOrdinal t).symm v)
    (bits : 2^S.colors<2^w) (dimensions : S.degree<2^w ∧ 2^t<2^w ∧ 2^l<2^w)
    (E : Codec B w S.colors t l) (code : ∀v,E.base v=((b v).val:Word w))
    (add : ∀u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
    (sub : ∀u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
    (qFits : 3*(2^S.colors*S.degree)/4<2^w)
    (sums : ∀a:P.Motif,thickWidth P prior (P.bundle a)<2^w) :
    let run:=pre cell S t
    let out:=(run.execute cell pub m).2
    run.fits cell pub m ∧ agreesOutside p.demands p.newGraph out m ∧
      Chart S P b p cell prior out ∧
      ∀a j,out (p.demands+2*(denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc a).val+j.val)=
        (demandWidth P prior (motifNumbers P (Demand.key P (baseNat b)) hc) a j:Word w) := by
  let first:=((splitSpan S).install cell).execute cell pub m |>.2
  let middle:=coloringRest cell S t pub first
  have sliced:=old.slice space pub ⟨dimensions.1,bits,dimensions.2.1⟩ eight
  have Hs : Sliced S P b p cell prior first := sliced.2.2
  have chart:=Hs.greedy space pub palette tw oneWord colorCode tagCode
  have tail:=space.high
  have a:=space.demandEnd
  have d:=space.splitEnd
  have e:=space.colorEnd
  have f:=space.offsetEnd
  have cap:=cell.isLt
  have bases : (dims S N t l).oldBase = N := rfl
  have edges : (dims S N t l).oldEdges = (C).rows := rfl
  have midChart : Chart S P b p cell prior middle :=
    ⟨chart.2.2.1.toOld,chart.2.2.2,by have :=space.oldWidths;omega⟩
  have demands:=midChart.demands hc space pub E code add sub bits dimensions qFits sums
  refine ⟨?_,?_,demands.2.2.1,demands.2.2.2⟩
  · obtain ⟨ca,cb,cc,cd⟩ := chart.1
    exact ⟨sliced.1,ca,cb,cc,cd,demands.1⟩
  · intro i outside
    have r : i<p.demands ∨ p.demands+2*(x).motifs≤ i := by rcases outside with o|o <;> omega
    have g : i<p.colors ∨ p.offsets+N≤ i := by rcases outside with o|o <;> omega
    have sp : i<p.split ∨ p.split+8*(C).rows≤ i := by rcases outside with o|o <;> omega
    exact (demands.2.1 i r).trans ((chart.2.1 i g).trans (sliced.2.1 i sp))


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
