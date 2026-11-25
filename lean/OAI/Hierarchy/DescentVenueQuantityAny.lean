import OAI.Hierarchy.DescentVenueQuantityState
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Total execution of the reset funding bank conversion before the next stage -/
open ThreeFlat.RAM.PhysicalProcedure
namespace Hierarchy.DescentVenueQuantityPlanes
open DescentSIMDLookup DescentActorRaster DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (p:Dims) (L:Layout)
local notation "R" => p.groups*p.blocks
local notation "K" => chunks p.groups p.lanes
local notation "N" => p.oldHosts*p.shapes
local notation "new" => p.lanes*p.blocks
local notation "bank" => Overlap.outputBank L.pitch (p.shapes*p.oldHosts) R p.oldLanes new p.precision
local notation "reshapeWords" => DescentScalarBookReshape.words p.oldHosts p.shapes p.groups p.blocks p.precision p.lanes
local notation "reshapeLen" => DescentScalarBookReshape.cells p.oldHosts p.shapes p.groups p.blocks p.precision p.lanes
local notation "body" => DenseRead.expr p.blocks p.hosts K L.collect N L.count L.inverse L.grouped
local notation "denseWords" => DenseRead.literals p.blocks p.hosts K L.collect N
local notation "denseLen" => DenseRead.cells p.blocks p.hosts K L.collect N

def image {w:ℕ} (m:Memory w):Memory w:=
  let mid:=Overlap.result L.pitch (p.shapes*p.oldHosts) R p.oldLanes new p.precision L.earlier m
  let next:=DescentScalarBookReshape.result p.oldHosts p.shapes p.groups p.blocks p.precision p.lanes
    L.reshape L.grouped.base bank mid
  ProtocolRAM.image L.out (p.blocks*(p.hosts*K)) body
    (DescentStaticWordColumn.image L.collect denseWords next denseLen)

attribute [local irreducible] CheapCode Procedure.seq scan

theorem affordable (w:ℕ):CheapCode (program p L w):=by
  unfold program Overlap.program Overlap.tables DescentScalarBookReshape.program DenseRead.proc
  apply cheap_seq
  · apply cheap_seq
    · apply cheap_seq
      · apply cheap_seq <;> apply DescentOrdinaryAtomFieldRAM.ROM.cheap
      · apply scan_cheap
    · apply cheap_seq
      · apply DescentStaticWordColumn.cheap
      · apply scan_cheap
  · apply cheap_seq
    · apply DescentStaticWordColumn.cheap
    · apply scan_cheap

def phase (w:ℕ):NativePhase w:=⟨program p L w,ticks p L,image p L,affordable p L w⟩

theorem any {used w:ℕ} (m:Memory w)(fit:Room p L used w):
    (phase p L w).Runs m ∧
      ∀a,a<L.pitch ∨ L.out+p.blocks*(p.hosts*K)≤a→image p L m a=m a:=by
  let mid:=Overlap.result L.pitch (p.shapes*p.oldHosts) R p.oldLanes new p.precision L.earlier m
  let remapped:=DescentStaticWordColumn.image L.reshape reshapeWords mid reshapeLen
  let e:=DescentScalarBookReshape.expression (DescentScalarBookReshape.layout p.oldHosts p.shapes p.groups
    p.blocks p.precision p.lanes L.reshape bank)
  let shaped:=ProtocolRAM.image L.grouped.base (p.blocks*(N*K)) e remapped
  let dirs:=DescentStaticWordColumn.image L.collect denseWords shaped denseLen
  have sz:=fit.reshapeRoom
  obtain ⟨first,f₀,_⟩:=Overlap.any L.pitch (p.shapes*p.oldHosts) R p.oldLanes new p.precision L.earlier m fit.original fit.pitchRoom
  have printShape:(DescentStaticWordColumn.program w L.reshape reshapeWords reshapeLen).Exec mid remapped (4+10*reshapeLen):=DescentStaticWordColumn.mount L.reshape reshapeLen reshapeWords mid
    (sz.early.trans_lt ((Nat.le_add_right ..).trans_lt sz.end_))
  have project:(scan w L.grouped.base (p.blocks*(N*K)) e).Exec remapped shaped (4+(p.blocks*(N*K))*54):=
    scan_exec _ _ _ _ sz.banks sz.end_
  have printDir:(DescentStaticWordColumn.program w L.collect denseWords denseLen).Exec shaped dirs (4+10*denseLen):=DescentStaticWordColumn.mount L.collect denseLen denseWords shaped
    (fit.tables.trans_lt ((Nat.le_add_right ..).trans_lt fit.room))
  have collect:(scan w L.out (p.blocks*(p.hosts*K)) body).Exec dirs (ProtocolRAM.image L.out (p.blocks*(p.hosts*K)) body dirs)
      (4+(p.blocks*(p.hosts*K))*(2*(body).work+4)):=scan_exec L.out (p.blocks*(p.hosts*K)) body dirs fit.expressions fit.room
  refine ⟨by
    intro P Rw Kw machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then (Procedure.Exec.then first (Procedure.Exec.then printShape project))
      (Procedure.Exec.then printDir collect) machine pc regs pubs exit rom advice cfg memory enter same,?_⟩
  intro x away
  have before₁:=fit.later
  have before₂:=fit.last
  have bounds₁:=sz.early
  have bounds₂:=fit.groupedSize
  have bounds₃:=fit.groupedEarly
  have bounds₄:=fit.tables
  have reach:Overlap.finish L.pitch (p.shapes*p.oldHosts) R p.oldLanes new p.precision≤L.reshape:=by
    have source:=sz.sourceEnd
    have bounded:chunks R new≤K:=by
      by_cases h:p.lanes=0
      · simp [h,chunks,ThreeFlat.Routing.poolBatchCount]
      by_cases hr:p.blocks=0
      · simp [hr,chunks,ThreeFlat.Routing.poolBatchCount]
      rw [chunks_group _ _ _ (Nat.pos_of_ne_zero h) (Nat.pos_of_ne_zero hr)]
    calc
      _ ≤ (bank).base+(p.shapes*p.oldHosts)*K:=Nat.add_le_add_left (Nat.mul_le_mul_left _ bounded) _
      _ ≤ _:=by simpa only [Nat.mul_assoc] using source
  exact (ProtocolRAMGeneratedWrite.frame_image L.out (p.blocks*(p.hosts*K)) body dirs x
    (away.imp_left (by omega))).trans ((DescentStaticWordColumn.frame _ _ _ shaped x
    (away.imp (by omega) (by omega))).trans ((ProtocolRAMGeneratedWrite.frame_image _ _ e remapped x
    (away.imp (by omega) (by omega))).trans ((DescentStaticWordColumn.frame _ _ _ mid x
    (away.imp (by omega) (by omega))).trans (f₀ x (away.imp_right (by omega))))))

end
end Hierarchy.DescentVenueQuantityPlanes

end OAI
