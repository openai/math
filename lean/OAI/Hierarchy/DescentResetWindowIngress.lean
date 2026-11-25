import OAI.Hierarchy.DescentStageSignedGL
import OAI.Hierarchy.DescentSignedGLTotal
import OAI.Hierarchy.DescentResetWindowColumns
import OAI.Hierarchy.DescentResetMeasuredStencil

namespace OAI
/-! # One reached image for the selected stencil and old signed cable receiver windows -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.SignedFields
open DescentSIMDLookup DescentPackedZip DescentGL DescentGLNielsen DescentColonies DescentIssuedFallbackPanel
open DescentPackedColony DescentPacking.PackedMatch.Local DescentSixParty DescentSharedCableNames.Stage
open DescentSixParty.Chronology DescentSixParty.Chronology.Shelf
open DescentGroupPeerOrder DescentStageEdgeReceipt ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i g h l H G c M batch field t w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {gate : PoweredGadget F} {q ε : ℝ} (A : GroupStage W gate q ε J V k)
  (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (groups : J≃Fin G) (host : V↪Fin H)
local notation "degree" => A.degree
local notation "D" => 2*A.cap
local notation "N" => 2^k
local notation "b" => DescentSignedCableCodec.width A.degree A.cap
local notation "L" => 2^(h+l-c)

def remixedBank (C : Chart) (h l H : ℕ) (j : Fin D) : Bank :=
  ⟨slice (((C.chosen (h+l)).bank (schedule (h+l)).length).base) H (2^h) j,Nat.clog 2 (H*2^h)⟩

/-- `shape` is the actual output of the selected reset's paid stencil, including padded
hosts. Its true rows and every original signed occurrence remain available together. -/
theorem after_stencil_rows (base : ℕ) (saved shape : Bank) (old : Fin D→Fin N→Bank)
    (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N) (pos : 0<M)
    (small : c≤h+l) (repack : batch*L=2^l) (many : 0<batch)
    (mem : Memory w) (safe : ∀j x,(old j x).Fits w base)
    (dataSize : ∀j x,H*chunks G M≤(old j x).size)
    (signed : ∀j x,Reads (old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) M mem)
    (keyFits : saved.Fits w base) (savedWord : mem saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (room : SignedFields.stop (joinStop base b N M) D H h l b<2^w)
    (shapeRoom : shape.base+H*chunks (2^c) batch≤base) (_shapeSize : H*chunks (2^c) batch≤ shape.size)
    (code : V→Block c→Fin L→Cell t)
    (published : PackedFlow.Padded.Published (h:=h) (l:=l) batch t shape.base host code mem)
    (bounds :
      let first:=joinStop base b N M
      let C:=SignedFields.chart first D H h l b
      let upper:=SignedFields.stop first D H h l b
      let rs:=remixedBank A C h l H
      ∀a : Column L A.cap,(spec shape rs t degree a).Room
        (start upper (maxBits t degree A.cap L) H (2^c) batch ((column L A.cap) a).val) H (2^c) batch field w) :
    let first:=joinStop base b N M
    let C:=SignedFields.chart first D H h l b
    let upper:=SignedFields.stop first D H h l b
    let rs:=remixedBank A C h l H
    let op:=joinOp base b N M D (fun j x=>.lookup (old j x) .row)
    let prep:=(Book.install (joinGate b N) (joinWidth b N) M w base).seq (SignedFields.program first C saved op D H h l b w)
    let ids:=column L A.cap
    let startAt:=start upper (maxBits t degree A.cap L) H (2^c) batch
    let jobs:=fun j=>let a:=ids.symm j
             (spec shape rs t degree a).job (startAt j.val) (by simpa only [a,ids,Equiv.apply_symm_apply] using bounds a)
    let phase:=series (catalog jobs)
    let bank:=bankAt shape rs t degree upper H (2^c) batch
    ∃(last : Memory w) (values : Fin H→Block c→Fin L→Cell t)
      (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      (prep.seq phase.program).Exec mem last (((4+10*(N*(2*2^(joinWidth b N*M))))+
        SignedFields.duration first C saved op D H h l b w)+phase.ticks) ∧
      CheapCode (prep.seq phase.program) ∧
      (∀x,Reads (bank (.inl (0,x))) (fun v hi=>((values v hi x).val:Cell field)) batch last) ∧
      (∀x,Reads (bank (.inl (1,x))) (fun v hi=>((values v hi x).val+1:Cell field)) batch last) ∧
      (∀j x,Reads (bank (.inr (j,x))) (fun v hi=>((DescentSignedCableCodec.encode (ports v hi x j)).val:Cell field)) batch last) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      (∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j) ∧
      ∀a,a<base ∨ upper+stride (maxBits t degree A.cap L) H (2^c) batch*count L A.cap≤a→last a=mem a := by
  let first:=joinStop base b N M
  let C:=SignedFields.chart first D H h l b
  let upper:=SignedFields.stop first D H h l b
  let rs:=remixedBank A C h l H
  obtain ⟨mid,ran,cheap,read,keep⟩:=stage_ports A native S ready groups host base saved old μ size width pos
    small repack many mem safe dataSize signed keyFits savedWord room
  obtain ⟨values,stencil,atHost⟩:=published
  have shapeRead : Reads shape (fun v hi=>encode t L (values v hi)) batch mid := by
    intro p
    exact (keep _ (.inl ((Nat.add_lt_add_left (row H (2^c) batch p).isLt _).trans_le shapeRoom))).trans (stencil p)
  let ports (v : Fin H) (hi : Block c) (x : Fin L) (j : Fin D) :=
    let oldPoint:=finProdFinEquiv.symm (Fin.cast size ((rearrange μ).symm (join small hi x)))
    Stage.Prepare.signed A native S ready groups.toEmbedding host oldPoint.2 j v oldPoint.1
  have chipRead (j : Fin D) : Reads (rs j)
      (fun v hi=>encode b L (fun x=>DescentSignedCableCodec.encode (ports v hi x j))) batch mid:=(read j).1
  obtain ⟨exec,_,own,tag,sign,frame⟩:=window_columns shape rs upper mid values ports shapeRead chipRead bounds
  refine ⟨_,values,ports,ran.then exec,cheap_seq cheap (NativePhase.cheap _),own,tag,sign,atHost,?_,?_⟩
  · intro v hi x j
    have hit := congrArg (DescentSignedCableCodec.decode degree A.cap) ((read j).2 v hi x)
    simpa only [oldWord,DescentSignedCableCodec.decode_encode] using hit
  · intro a ha
    have top : base≤upper := (Nat.le_add_right ..).trans (Dated.origin_le_endAddress first (D*H) h l b)
    rcases ha with lo|hi
    · exact (frame a (.inl (lo.trans_le top))).trans (keep a (.inl lo))
    · exact (frame a (.inr hi)).trans (keep a (.inr ((Nat.le_add_right ..).trans hi)))

theorem after_stencil (base : ℕ) (saved shape : Bank) (old : Fin D→Fin N→Bank)
    (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N) (pos : 0<M)
    (small : c≤h+l) (repack : batch*L=2^l) (many : 0<batch)
    (mem : Memory w) (safe : ∀j x,(old j x).Fits w base)
    (dataSize : ∀j x,H*chunks G M≤(old j x).size)
    (signed : ∀j x,Reads (old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) M mem)
    (keyFits : saved.Fits w base) (savedWord : mem saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (room : SignedFields.stop (joinStop base b N M) D H h l b<2^w)
    (shapeRoom : shape.Fits w base) (shapeSize : H*chunks (2^c) batch≤ shape.size)
    (code : V→Block c→Fin L→Cell t)
    (published : PackedFlow.Padded.Published (h:=h) (l:=l) batch t shape.base host code mem)
    (bounds :
      let first:=joinStop base b N M
      let C:=SignedFields.chart first D H h l b
      let upper:=SignedFields.stop first D H h l b
      let rs:=remixedBank A C h l H
      ∀a : Column L A.cap,(spec shape rs t degree a).Room
        (start upper (maxBits t degree A.cap L) H (2^c) batch ((column L A.cap) a).val) H (2^c) batch field w) :
    let first:=joinStop base b N M
    let C:=SignedFields.chart first D H h l b
    let upper:=SignedFields.stop first D H h l b
    let rs:=remixedBank A C h l H
    let op:=joinOp base b N M D (fun j x=>.lookup (old j x) .row)
    let prep:=(Book.install (joinGate b N) (joinWidth b N) M w base).seq (SignedFields.program first C saved op D H h l b w)
    let ids:=column L A.cap
    let startAt:=start upper (maxBits t degree A.cap L) H (2^c) batch
    let jobs:=fun j=>let a:=ids.symm j
             (spec shape rs t degree a).job (startAt j.val) (by simpa only [a,ids,Equiv.apply_symm_apply] using bounds a)
    let phase:=series (catalog jobs)
    let bank:=bankAt shape rs t degree upper H (2^c) batch
    ∃(last : Memory w) (values : Fin H→Block c→Fin L→Cell t)
      (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      (prep.seq phase.program).Exec mem last (((4+10*(N*(2*2^(joinWidth b N*M))))+
        SignedFields.duration first C saved op D H h l b w)+phase.ticks) ∧
      CheapCode (prep.seq phase.program) ∧
      (∀x,Reads (bank (.inl (0,x))) (fun v hi=>((values v hi x).val:Cell field)) batch last) ∧
      (∀x,Reads (bank (.inl (1,x))) (fun v hi=>((values v hi x).val+1:Cell field)) batch last) ∧
      (∀j x,Reads (bank (.inr (j,x))) (fun v hi=>((DescentSignedCableCodec.encode (ports v hi x j)).val:Cell field)) batch last) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      (∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j) ∧
      ∀a,a<base ∨ upper+stride (maxBits t degree A.cap L) H (2^c) batch*count L A.cap≤a→last a=mem a := by
  exact after_stencil_rows A native S ready groups host base saved shape old μ size width pos small repack many mem safe dataSize signed keyFits savedWord room
    ((Nat.add_le_add_left shapeSize _).trans shapeRoom.2.2) shapeSize code published bounds

end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
