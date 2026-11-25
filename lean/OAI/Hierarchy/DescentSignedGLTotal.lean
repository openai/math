import OAI.Hierarchy.DescentSignedGLRun

namespace OAI
/-! # The individual signed-field permutation always runs for its specified duration -/
namespace Hierarchy.DescentGLPacked.BankImage.SignedFields
open DescentGLPacked DescentGLNielsen DescentPackedColony.Phase.Arena
open DescentPacking.PackedMatch.Local DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D H h l b w N M : ℕ}

def image (origin : ℕ) (C : Chart) (saved : Bank) (field : ℕ→Expr) (D H h l b : ℕ) (m : Memory w) :=
  let d:=h+l
  let n:=(schedule d).length
  let I:=controlSheet origin d w
  let J:=Dated.routes C (D*H) h l b w
  let rows:=H*2^h
  let gs:=DescentPackedFlowBatch.passes C.input.base rows rows field 0 D
  let ps:=steps (C.chosen d) (D*H) (2^h) 0 n
  let ctrl:=(controlBanks origin d).expr (.lookup saved (.lit 0))
  result ps (ProtocolRAM.image C.flags n ctrl (result gs (J.output (I.output m))))

theorem always (origin : ℕ) (C : Chart) (saved : Bank) (field : ℕ→Expr) (mem : Memory w)
    (valid : Size C (D*H) h l b w) (keyFits : saved.Fits w origin)
    (fits : ∀j<D,(field j).Fits w origin)
    (space : controlEnd origin (h+l)≤C.input.base)
    (offsetFits : (controlBanks origin (h+l)).offsets.Fits w C.input.base)
    (switchFits : (controlBanks origin (h+l)).switches.Fits w C.input.base)
    (gap : C.input.base+C.input.size≤C.flags) :
    (program origin C saved field D H h l b w).Exec mem
      (image origin C saved field D H h l b mem) (duration origin C saved field D H h l b w) ∧
    CheapCode (program origin C saved field D H h l b w) ∧
    ∀a,a<origin ∨ endAddress C (h+l)≤a→image origin C saved field D H h l b mem a=mem a := by
  let d:=h+l
  let n:=(schedule d).length
  let I:=controlSheet origin d w
  let J:=Dated.routes C (D*H) h l b w
  let mid:=J.output (I.output mem)
  let rows:=H*2^h
  let gs:=DescentPackedFlowBatch.passes C.input.base rows rows field 0 D
  let flat:=result gs mid
  let key:=Expr.lookup saved (.lit 0)
  let op:=(controlBanks origin d).expr key
  have early : origin≤C.input.base:= (show origin≤controlEnd origin d by unfold controlEnd;omega).trans space
  have heap : C.start≤C.heap (h+l):=Nat.le_add_right ..
  have beginAt : C.input.base≤C.flags:=by omega
  have flags:=valid.controls
  have budget:=valid.top
  have lowI : I.low+I.length<2^w:=by
    change origin+(controlEnd origin (h+l)-origin)<2^w
    have initial : origin ≤ controlEnd origin (h+l) := by unfold controlEnd; omega
    omega
  have lowJ : J.low+J.length<2^w:=by change C.start+(C.heap (h+l)-C.start)<2^w;omega
  have afterFlags : C.flags ≤ C.start := (Nat.le_add_right ..).trans flags
  obtain ⟨printed,_,_,preserved,hware,_⟩:=I.pair J mem (.inl (space.trans (beginAt.trans afterFlags))) lowI lowJ
  have count : D*rows≤C.input.size:=by simpa only [rows,Nat.mul_assoc] using valid.inputSize
  have high : C.start<2^w:=heap.trans_lt ((Nat.le_add_right ..).trans_lt budget)
  obtain ⟨gather,_,low⟩:=DescentPackedFlowBatch.execute C.input.base rows rows D field mid
    (fun j hj=>ProtocolRAMGeneratedWrite.fits_mono _ early (fits j hj)) (by omega) le_rfl
  have widen (B : Bank) (fit : B.Fits w C.input.base) : B.Fits w C.flags :=
    ⟨fit.1,fit.2.1,fit.2.2.trans beginAt⟩
  have keyOK : key.Fits w C.flags :=
    ⟨⟨keyFits.1,keyFits.2.1,keyFits.2.2.trans (early.trans beginAt)⟩,trivial⟩
  have opOK : op.Fits w C.flags:=⟨widen _ switchFits,keyOK,widen _ offsetFits,trivial⟩
  have scanRoom : C.flags+n < 2^w := flags.trans_lt high
  have controls : (scan w C.flags n op).Exec flat (ProtocolRAM.image C.flags n op flat)
      (4+n*(2*op.work+4)) := @ProtocolRAM.scan_exec w C.flags n op flat opOK scanRoom
  obtain ⟨run,cheap⟩:=execution (C.chosen d) (hardware C valid) (ProtocolRAM.image C.flags n op flat) 0 n (by simpa only [n,d,Nat.zero_add] using (le_refl (schedule (h+l)).length))
  refine ⟨printed.then (gather.then (controls.then run)),cheap_seq hware (cheap_seq (@ProtocolRAM.program_cheap _ _)
    (cheap_seq (@scan_cheap _ _ _ _) cheap)),?_⟩
  intro a ha
  have before : C.input.base≤C.start:=beginAt.trans afterFlags
  rcases ha with lo|hi
  · exact (reset_frames C valid op flat a (.inl (lo.trans_le (early.trans beginAt)))).trans
      ((low a (lo.trans_le early)).trans (preserved a (.inl lo) (.inl (lo.trans_le (early.trans before)))))
  · have endHeap : C.heap d≤a:=(Nat.le_add_right ..).trans hi
    have keep : flat a=mid a:=DescentPackedFlowBatch.above _ _ _ _ _ 0 D a le_rfl (by
      have ca:C.input.base+D*rows≤C.flags:= (Nat.add_le_add_left count _).trans gap
      simpa only [Nat.zero_add] using ca.trans (afterFlags.trans (heap.trans endHeap)))
    exact (reset_frames C valid op flat a (.inr hi)).trans (keep.trans
      (preserved a (.inr (space.trans (before.trans (heap.trans endHeap)))) (.inr endHeap)))

theorem from_slots_any (base : ℕ) (saved : Bank) (old : Fin D→Fin N→Expr) (mem : Memory w)
    (safe : ∀j x,(old j x).Fits w base) (keyFits : saved.Fits w base)
    (room : stop (joinStop base b N M) D H h l b<2^w) :
    let first:=joinStop base b N M
    let C:=chart first D H h l b
    let pre:=Book.install (joinGate b N) (joinWidth b N) M w base
    let z:=Book.image (joinGate b N) (joinWidth b N) M base mem
    let field:=joinOp base b N M D old
    let run:=pre.seq (program first C saved field D H h l b w)
    run.Exec mem (image first C saved field D H h l b z)
      ((4+10*(N*(2*2^(joinWidth b N*M))))+duration first C saved field D H h l b w) ∧
    CheapCode run ∧
    ∀a,a<base ∨ stop first D H h l b≤a→image first C saved field D H h l b z a=mem a := by
  let first:=joinStop base b N M
  let C:=chart first D H h l b
  let T:=Book.tables (joinGate b N) (joinWidth b N) M base
  let z:=Book.image (joinGate b N) (joinWidth b N) M base mem
  have firstOrder : base≤first:=Nat.le_add_right ..
  have top : first≤ stop first D H h l b :=
    Dated.origin_le_endAddress first (D*H) h l b
  have caps (x : Fin N) : (joinGate b N x).left+(joinGate b N x).right≤joinWidth b N:=le_rfl
  obtain ⟨stamp,_,frame,cheap⟩:=Book.mount (joinGate b N) (joinWidth b N) M base mem caps (top.trans_lt room)
  have ok (j : ℕ) (hit : j<D) : (joinOp base b N M D old j).Fits w first := by
    rw [joinOp,dite_eq_left hit]
    apply Gather.fits
    intro x
    obtain ⟨shift,tbl⟩:=Book.geometry (joinGate b N) (joinWidth b N) M base x le_rfl (top.trans_lt room) (caps x)
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ firstOrder (safe ⟨j,hit⟩ x),shift,tbl,rfl,rfl⟩
  obtain ⟨valid,extent,off,sw,gap⟩:=allocation first D H h l b w room
  obtain ⟨run,hw,preserved⟩:=always first C saved (joinOp base b N M D old) z valid
    ⟨keyFits.1,keyFits.2.1,keyFits.2.2.trans firstOrder⟩ ok extent off sw gap
  refine ⟨stamp.then run,cheap_seq cheap hw,?_⟩
  intro a ha
  rcases ha with lo|hi
  · exact (preserved a (.inl (lo.trans_le firstOrder))).trans (frame a (.inl lo))
  · exact (preserved a (.inr ((after_data ..).trans hi))).trans (frame a (.inr (top.trans hi)))

end
end Hierarchy.DescentGLPacked.BankImage.SignedFields

end OAI
