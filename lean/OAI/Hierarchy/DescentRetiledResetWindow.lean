import OAI.Hierarchy.DescentStageSignedGL
import OAI.Hierarchy.DescentSignedRetile
import OAI.Hierarchy.DescentResetWindowIngress
import OAI.Hierarchy.DescentResetWindowColumns
import OAI.Hierarchy.DescentResetMeasuredStencil

namespace OAI
/-! # The measured stencil and signed fields with independently chosen previous and next packet pitches -/
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
def incoming {D N : ℕ} (old : Fin D→Fin N→Bank) (j : Fin (D*N)) : Bank :=
  let pair:=finProdFinEquiv.symm j
  old pair.1 pair.2

local notation "degree" => A.degree
local notation "D" => 2*A.cap
local notation "N" => 2^k
local notation "b" => DescentSignedCableCodec.width A.degree A.cap
local notation "L" => 2^(h+l-c)

variable {R K : ℕ} (origin : ℕ)

local notation "base" => Retile.stop origin b H G R M (D*N)
local notation "newOld" => fun (j : Fin D) (x : Fin N) =>
  Retile.output origin b H G R M (finProdFinEquiv (j,x))

theorem after_retile_rows  (saved shape : Bank) (old : Fin D→Fin N→Bank)
    (slots : G=K*(R*M)) (ratio : 0<R) (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N) (pos : 0<M)
    (small : c≤h+l) (repack : batch*L=2^l) (many : 0<batch)
    (mem : Memory w) (safe : ∀j x,(old j x).Fits w origin)
    (dataSize : ∀j x,H*chunks G (R*M)≤(old j x).size)
    (signed : ∀j x,Reads (old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) (R*M) mem)
    (keyFits : saved.Fits w origin) (savedWord : mem saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (fits : base<2^w) (room : SignedFields.stop (joinStop base b N M) D H h l b<2^w)
    (shapeRoom : shape.base+H*chunks (2^c) batch≤origin) (shapeSize : H*chunks (2^c) batch≤ shape.size)
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
    let op:=joinOp base b N M D (fun j x=>.lookup (newOld j x) .row)
    let prep:=(Book.install (joinGate b N) (joinWidth b N) M w base).seq (SignedFields.program first C saved op D H h l b w)
    let ids:=column L A.cap
    let startAt:=start upper (maxBits t degree A.cap L) H (2^c) batch
    let jobs:=fun j=>let a:=ids.symm j
             (spec shape rs t degree a).job (startAt j.val) (by simpa only [a,ids,Equiv.apply_symm_apply] using bounds a)
    let phase:=series (catalog jobs)
    let bank:=bankAt shape rs t degree upper H (2^c) batch
    ∃(last : Memory w) (values : Fin H→Block c→Fin L→Cell t)
      (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      ((Retile.program origin H b slots ratio pos (incoming old) w).seq (prep.seq phase.program)).Exec mem last (Retile.ticks origin H b slots ratio pos (incoming old)+(((4+10*(N*(2*2^(joinWidth b N*M))))+
        SignedFields.duration first C saved op D H h l b w)+phase.ticks)) ∧
      CheapCode ((Retile.program origin H b slots ratio pos (incoming old) w).seq (prep.seq phase.program)) ∧
      (∀x,Reads (bank (.inl (0,x))) (fun v hi=>((values v hi x).val:Cell field)) batch last) ∧
      (∀x,Reads (bank (.inl (1,x))) (fun v hi=>((values v hi x).val+1:Cell field)) batch last) ∧
      (∀j x,Reads (bank (.inr (j,x))) (fun v hi=>((DescentSignedCableCodec.encode (ports v hi x j)).val:Cell field)) batch last) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      (∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j) ∧
      ∀a,a<origin ∨ upper+stride (maxBits t degree A.cap L) H (2^c) batch*count L A.cap≤a→last a=mem a := by
  let values (p : Fin (D*N)) (v : Fin H) (g : Fin G) :=
    let a:=finProdFinEquiv.symm p
    DescentSignedCableCodec.encode (Stage.Prepare.signed A native S ready groups.toEmbedding host a.2 a.1 v g)
  obtain ⟨mid,split,cheap,read,frame⟩:=Retile.issued origin slots ratio pos (incoming old) values mem
    (fun _=>safe _ _) (fun _=>dataSize _ _) (fun _=>signed _ _) fits
  have lower:origin≤base:=by
    unfold Retile.stop Subwords.destination
    omega
  have bound (j : Fin D) (x : Fin N):=(Retile.fits_output origin (finProdFinEquiv (j,x)) fits)
  have lifted (j : Fin D) (x : Fin N) : Reads (newOld j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) M mid := by
    simpa only [DescentPackedColony.Reads,values,Equiv.symm_apply_apply] using read (finProdFinEquiv (j,x))
  have kept : mid saved.base=mem saved.base:=frame _ (.inl (by have h₀:=keyFits.1;have h₁:=keyFits.2.2;omega))
  have visible : PackedFlow.Padded.Published (h:=h) (l:=l) batch t shape.base host code mid := by
    obtain ⟨u,posted,spec⟩:=published
    refine ⟨u,?_,spec⟩
    intro p
    exact (frame _ (.inl ((Nat.add_lt_add_left (row H (2^c) batch p).isLt _).trans_le shapeRoom))).trans (posted p)
  obtain ⟨dst,oldCode,chips,run,ok,own,tag,sign,truth,live,space⟩:=after_stencil_rows
    A native S ready groups host base saved shape newOld μ size width pos small repack many mid
    (fun j x=>(bound j x).1) (fun j x=>(bound j x).2) lifted
    ⟨keyFits.1,keyFits.2.1,keyFits.2.2.trans lower⟩ (kept.trans savedWord) room
    (shapeRoom.trans lower) shapeSize code visible bounds
  refine ⟨dst,oldCode,chips,split.then run,cheap_seq cheap ok,own,tag,sign,truth,live,?_⟩
  intro a ha
  have first:base≤joinStop base b N M:=Nat.le_add_right ..
  have second:joinStop base b N M≤SignedFields.stop (joinStop base b N M) D H h l b:=
    Dated.origin_le_endAddress _ _ _ _ _
  rcases ha with lo|hi
  · exact (space a (.inl (lo.trans_le lower))).trans (frame a (.inl lo))
  · exact (space a (.inr hi)).trans (frame a (.inr ((first.trans second).trans ((Nat.le_add_right ..).trans hi))))

theorem after_retile  (saved shape : Bank) (old : Fin D→Fin N→Bank)
    (slots : G=K*(R*M)) (ratio : 0<R) (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N) (pos : 0<M)
    (small : c≤h+l) (repack : batch*L=2^l) (many : 0<batch)
    (mem : Memory w) (safe : ∀j x,(old j x).Fits w origin)
    (dataSize : ∀j x,H*chunks G (R*M)≤(old j x).size)
    (signed : ∀j x,Reads (old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) (R*M) mem)
    (keyFits : saved.Fits w origin) (savedWord : mem saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (fits : base<2^w) (room : SignedFields.stop (joinStop base b N M) D H h l b<2^w)
    (shapeRoom : shape.Fits w origin) (shapeSize : H*chunks (2^c) batch≤ shape.size)
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
    let op:=joinOp base b N M D (fun j x=>.lookup (newOld j x) .row)
    let prep:=(Book.install (joinGate b N) (joinWidth b N) M w base).seq (SignedFields.program first C saved op D H h l b w)
    let ids:=column L A.cap
    let startAt:=start upper (maxBits t degree A.cap L) H (2^c) batch
    let jobs:=fun j=>let a:=ids.symm j
             (spec shape rs t degree a).job (startAt j.val) (by simpa only [a,ids,Equiv.apply_symm_apply] using bounds a)
    let phase:=series (catalog jobs)
    let bank:=bankAt shape rs t degree upper H (2^c) batch
    ∃(last : Memory w) (values : Fin H→Block c→Fin L→Cell t)
      (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      ((Retile.program origin H b slots ratio pos (incoming old) w).seq (prep.seq phase.program)).Exec mem last (Retile.ticks origin H b slots ratio pos (incoming old)+(((4+10*(N*(2*2^(joinWidth b N*M))))+
        SignedFields.duration first C saved op D H h l b w)+phase.ticks)) ∧
      CheapCode ((Retile.program origin H b slots ratio pos (incoming old) w).seq (prep.seq phase.program)) ∧
      (∀x,Reads (bank (.inl (0,x))) (fun v hi=>((values v hi x).val:Cell field)) batch last) ∧
      (∀x,Reads (bank (.inl (1,x))) (fun v hi=>((values v hi x).val+1:Cell field)) batch last) ∧
      (∀j x,Reads (bank (.inr (j,x))) (fun v hi=>((DescentSignedCableCodec.encode (ports v hi x j)).val:Cell field)) batch last) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      (∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j) ∧
      ∀a,a<origin ∨ upper+stride (maxBits t degree A.cap L) H (2^c) batch*count L A.cap≤a→last a=mem a := by
  exact after_retile_rows A native S ready groups host origin saved shape old slots ratio μ size width pos small repack many
    mem safe dataSize signed keyFits savedWord fits room ((Nat.add_le_add_left shapeSize _).trans shapeRoom.2.2)
    shapeSize code published bounds

end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
