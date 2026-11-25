import OAI.Hierarchy.DescentActorRechunk
import OAI.Hierarchy.DescentActorDenseRead
import OAI.Hierarchy.DescentScalarBookReshape

namespace OAI
/-! # Compacting the measured multi-bit sheets against the previously issued actor directory -/
open ThreeFlat.RAM.PhysicalProcedure
namespace Hierarchy.DescentVenueQuantityPlanes
open DescentSIMDLookup DescentPackedZip DescentActorRaster Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  earlier : Bank
  count : Bank
  inverse : Bank
  pitch : ℕ
  reshape : ℕ
  grouped : Bank
  collect : ℕ
  out : ℕ

structure Dims where
  shapes : ℕ
  oldHosts : ℕ
  hosts : ℕ
  groups : ℕ
  blocks : ℕ
  precision : ℕ
  oldLanes : ℕ
  lanes : ℕ

variable (p : Dims) (L : Layout)
local notation "N" => p.oldHosts*p.shapes
local notation "rad" => p.groups*p.blocks
local notation "s₀" => chunks rad p.oldLanes
local notation "s₁" => chunks p.groups p.lanes
local notation "wide" => p.lanes*p.blocks
local notation "converted" => Overlap.outputBank L.pitch (p.shapes*p.oldHosts) rad p.oldLanes wide p.precision
local notation "end₀" => Overlap.finish L.pitch (p.shapes*p.oldHosts) rad p.oldLanes wide p.precision
local notation "body" => DenseRead.expr p.blocks p.hosts s₁ L.collect N L.count L.inverse L.grouped

def program (w : ℕ) :=
  (((Overlap.program L.pitch (p.shapes*p.oldHosts) rad p.oldLanes wide p.precision w L.earlier).seq
      (DescentScalarBookReshape.program p.oldHosts p.shapes p.groups p.blocks p.precision p.lanes
        L.reshape L.grouped.base w converted)).seq
    (DenseRead.proc p.blocks p.hosts s₁ L.collect N L.out w L.count L.inverse L.grouped))

def ticks :=
  (Overlap.ticks L.pitch (p.shapes*p.oldHosts) rad p.oldLanes wide p.precision L.earlier+
    ((4+10*DescentScalarBookReshape.cells p.oldHosts p.shapes p.groups p.blocks p.precision p.lanes)+
      (4+(p.blocks*(N*s₁))*54)))+
    ((4+10*DenseRead.cells p.blocks p.hosts s₁ L.collect N)+(4+p.blocks*(p.hosts*s₁)*(2*(body).work+4)))

structure Room (used w:ℕ) : Prop where
  original : L.earlier.Fits w L.pitch
  originalSize : p.shapes*p.oldHosts*s₀≤L.earlier.size
  pitchRoom : end₀<2^w
  reshapeRoom : DescentScalarBookReshape.Room p.oldHosts p.shapes p.groups p.blocks p.precision p.lanes w
    L.reshape L.grouped.base converted
  later : L.pitch≤L.reshape
  expressions : (body).Fits w L.out
  groupedSize : p.blocks*(N*s₁)≤L.grouped.size
  countSize : 0<L.count.size
  inverseSize : used≤L.inverse.size
  countEarly : L.count.base+L.count.size≤L.pitch
  inverseEarly : L.inverse.base+L.inverse.size≤L.pitch
  last : L.reshape≤L.collect
  groupedEarly : L.grouped.base+L.grouped.size≤L.collect
  tables : L.collect+DenseRead.cells p.blocks p.hosts s₁ L.collect N≤L.out
  room : L.out+p.blocks*(p.hosts*s₁)<2^w
  hostsFit : p.hosts≤2^w
  usedFit : used<2^w

variable {used w : ℕ} (rank : Fin used → Fin (p.oldHosts * p.shapes))
    (raw : Fin p.shapes → Fin p.oldHosts → Fin (p.groups * p.blocks) → Cell p.precision)

def value (b : Fin p.blocks) (h : Fin p.hosts) (g : Fin p.groups) : Cell p.precision :=
  if ht:h.val<used then DescentScalarBookReshape.book raw b (rank ⟨h.val,ht⟩) g else 0

theorem run (m : Memory w) (fit : Room p L used w) (oldpos : 0<p.oldLanes) (newpos : 0<p.lanes)
    (rb : 0<p.blocks) (hosts : 0<p.hosts) (chunksPos : 0<s₁)
    (original : ∀q (u : Row p.oldHosts rad p.oldLanes),m (L.earlier.base+q.val*(p.oldHosts*s₀)+
      (row p.oldHosts rad p.oldLanes u).val)=((data (raw q) u).val:Word w))
    (count : m L.count.base=(used:Word w))
    (inverse : ∀h : Fin used,m (L.inverse.base+h.val)=((rank h).val:Word w)) :
    ∃done,(program p L w).Exec m done (ticks p L) ∧
      (∀b(u : Row p.hosts p.groups p.lanes),done (L.out+b.val*(p.hosts*s₁)+(row p.hosts p.groups p.lanes u).val)=
        ((data (value p rank raw b) u).val:Word w)) ∧
      ∀a,a<L.pitch ∨ L.out+p.blocks*(p.hosts*s₁)≤a→done a=m a := by
  let t₁:=Overlap.result L.pitch (p.shapes*p.oldHosts) rad p.oldLanes wide p.precision L.earlier m
  have rechunk:=change_pitch raw L.pitch L.earlier m oldpos fit.original fit.originalSize fit.pitchRoom original
  obtain ⟨first,transformed,frame₁,_⟩:=rechunk
  have ce : chunks rad wide=s₁:=chunks_group _ _ _ newpos rb
  let t₂:=DescentScalarBookReshape.result p.oldHosts p.shapes p.groups p.blocks p.precision p.lanes
    L.reshape L.grouped.base converted t₁
  obtain ⟨second,blocks,frame₂⟩:=DescentScalarBookReshape.run L.reshape L.grouped.base converted t₁ raw
    newpos rb fit.reshapeRoom (fun l u=>by simpa only [ce] using transformed l u)
  have before (a : ℕ) (lt:a<L.pitch) : t₂ a=m a:=
    (frame₂ a (.inl (lt.trans_le fit.later))).trans (frame₁ a (.inl lt))
  let rawWords (b : Fin p.blocks) (v : Fin N) (j : Fin s₁) : Word w :=
    (data (DescentScalarBookReshape.book raw b) (v,j)).val
  have stored (b : Fin p.blocks) (v : Fin N) (j : Fin s₁) :
      t₂ (L.grouped.base+(b.val*(N*s₁)+v.val*s₁+j.val))=rawWords b v j:=by
    have index : (row N p.groups p.lanes (v,j)).val = v.val*s₁+j.val := by
      simp [row,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
    simpa only [DescentScalarBookReshape.dest,index,rawWords,Nat.add_assoc] using blocks b (v,j)
  have seen : t₂ L.count.base=(used:Word w):=(before _ (by have:=fit.countEarly;have:=fit.countSize;omega)).trans count
  have ids (j:Fin used) : t₂ (L.inverse.base+j.val)=((rank j).val:Word w):=
    (before _ ((Nat.add_lt_add_left (j.isLt.trans_le fit.inverseSize) _).trans_le fit.inverseEarly)).trans (inverse j)
  obtain ⟨third,correct,frame₃⟩:=DenseRead.run rank L.collect L.out L.count L.inverse L.grouped t₂ rawWords stored
    fit.expressions fit.groupedSize fit.countSize fit.inverseSize
    ⟨fit.countEarly.trans (fit.later.trans fit.last),fit.inverseEarly.trans (fit.later.trans fit.last),fit.groupedEarly⟩
    seen ids fit.tables fit.room fit.hostsFit fit.usedFit hosts chunksPos
  refine ⟨_,by
    intro P R K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then (Procedure.Exec.then first second) third machine pc regs pubs exit rom advice cfg memory enter same,?_,?_⟩
  · rintro b ⟨h,j⟩
    have found:=correct b h j
    have addr : (DenseRead.seats p.blocks p.hosts s₁ (b,h,j)).val=
        b.val*(p.hosts*s₁)+(row p.hosts p.groups p.lanes (h,j)).val:=by
      simp [DenseRead.seats,row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    rw [addr,←Nat.add_assoc] at found
    rw [found]
    by_cases live : h.val<used
    · simp only [DenseRead.dense,dite_eq_left live,rawWords,data,value]
    · rw [DenseRead.dense,dite_eq_right live]
      change _=((finFunctionFinEquiv _).val:Word w)
      rw [finFunctionFinEquiv_apply];simp [value,live]
  · rintro a (low|late)
    · exact (frame₃ a (.inl (low.trans_le (fit.later.trans fit.last)))).trans (before a low)
    · have srcEnd : end₀≤L.reshape:=by
        simpa only [Overlap.finish,Overlap.outputBank,Overlap.rows,ce,Nat.mul_assoc] using fit.reshapeRoom.sourceEnd
      have past:=fit.tables
      have after₁ : end₀≤a:=by
        have nextBound:=fit.last
        omega
      have after₂ : L.grouped.base+p.blocks*(N*s₁)≤a:=by
        have:=fit.groupedEarly;have:=fit.groupedSize;omega
      exact (frame₃ a (.inr late)).trans ((frame₂ a (.inr after₂)).trans (frame₁ a (.inr after₁)))

end
end Hierarchy.DescentVenueQuantityPlanes

end OAI
