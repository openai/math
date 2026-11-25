import OAI.Hierarchy.DescentRecordedControlSources
import OAI.Hierarchy.DescentDatedControlFrame
import OAI.Hierarchy.DescentRecordedVenueGeometry

namespace OAI
/-! # The reset's measured operand registers in the completed calendar date -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentSIMDLookup ProtocolRAM

theorem control_banks (v : ActorSetup) (base : ℕ) {w : ℕ} (room : v.directoryEnd base < 2^w) :
    (v.scene base).Fits w (v.endAddress base) ∧
    (v.depths base).Fits w (v.endAddress base) ∧ (v.levels base).Fits w (v.endAddress base) := by
  have last : v.endAddress base ≤ v.directoryEnd base := Nat.le_add_right ..
  have ds : (v.depths base).base+(v.depths base).size=(v.counts base).base:=rfl
  have cs : (v.counts base).base+(v.counts base).size=(v.starts base).base:=rfl
  have ss : (v.starts base).base+(v.starts base).size=(v.levels base).base:=rfl
  have ls : (v.levels base).base+(v.levels base).size=(v.heights base).base:=rfl
  have hs : (v.heights base).base+(v.heights base).size=(v.gate base).scalar:=rfl
  obtain ⟨b,g,o⟩:=v.gate_order base
  have rg : (v.gate base).repeatBase ≤ (v.gate base).gateBase:=by
    rw [←g]
    unfold DescentSharedLeafLookup.Public.stop
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have head : (v.gate base).output=(v.scene base).base:=rfl
  have end_ : (v.scene base).base+(v.scene base).size=v.endAddress base:=rfl
  have fits (bank : Bank) (endBank : bank.base+bank.size ≤ v.endAddress base) :
      bank.Fits w (v.endAddress base) :=
    ⟨Nat.two_pow_pos _,((Nat.le_add_left bank.size bank.base).trans endBank).trans_lt (last.trans_lt room),endBank⟩
  exact ⟨fits _ end_.le,fits _ (by omega),fits _ (by omega)⟩

end Hierarchy.DescentDatedAddressBook.ActorSetup

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentDenseHostOrder DescentActorRaster
open DescentPackedZip DescentSIMDLookup DescentPackedColony DescentDatedAddressBook DescentResetControlRegisters
open DescentVenueQuantityPlanes
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {old : Reached W G q ε S k i z D wire hist} {rates : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset old rates) {oldH H oldM M w : ℕ}
    (previous : Fintype.card old.V ≤ oldH) (next : Fintype.card B.next.V ≤ H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "Q" => (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g)).card
local notation "J" => S.groupCount (i+1)
local notation "cap" => old.placement.cap
local notation "oldId" => old.vertex.trans (Fin.castLEEmb previous)
local notation "rank" => (B.frame.host.symm.toEmbedding.trans old.vertex).trans (Fin.castLEEmb previous)
local notation "shapeId" v => ((Z).hostFields T rank v).2.val
local notation "depthAt" v => (Z).placement.b (position (Z).graph (v).val)
local notation "dims" => quantityDims B 1 oldH H oldM M
local notation "values" x => fun host group=>actualBit B next host group x
variable {A : PhysicalReset} {floor : ℕ} (u : A.DateInputs floor w) (ok : u.Ready)
local notation "V₀" => A.successor
local notation "base₀" => A.rebased floor
local notation "U₀" => (V₀).actor
local notation "cb" => (V₀).middle.stop base₀
local notation "first" => (U₀).endAddress cb
local notation "dir" => (⟨first,oldH,Q,chunks (2^cc) oldM⟩ : DescentResetNewActorDirectory.Layout)
local notation "scene" => (U₀).scene cb
local notation "depths" => (U₀).depths cb
local notation "levels" => (U₀).levels cb
local notation "a₀" => (V₀).setup.rotorBits
local notation "c₀" => (⟨dims,a₀⟩ : Chart)
local notation "start" => (V₀).controlFloor base₀
local notation "ceiling" => (V₀).operandFloor base₀
local notation "head₀" => A.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "time₀" => A.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "op₀" => (U₀).actorBody u.actor cb w
local notation "clock₀" => (U₀).actorTicks u.actor cb w

theorem control_chart_of_venue (shape : DescentFundedCensus.Shape) (paidM nextM precision : ℕ)
    (book : (V₀).venue=calibrated B shape oldH H paidM oldM M nextM precision) :
    (V₀).controlRegisters=c₀ := by
  unfold ResetOutput.controlRegisters
  rw [book]
  rfl

/-- The actor, depth and level rows are the three outputs of
`Recorded.directory_after_roots`. The five source expressions address the original
control bank after all seven operand fields and the node resolver have run. -/
theorem calendar_control_all_rows (grid : (U₀).directory cb=dir)
    (chart : (V₀).controlRegisters=c₀)
    (m before : Memory w)
    (ran : ((head₀).seq op₀).Exec m ((dir).result scene before) (time₀+clock₀))
    (cheap : CheapCode ((head₀).seq op₀))
    (oldPos : 0 < oldM) (newPos : 0 < M) (oldBits : oldM ≤ w)
    (actors : ∀(j : Fin Q) (p : Row oldH (2^cc) oldM),
      before ((scene).base+j.val*(oldH*chunks (2^cc) oldM)+(row _ _ _ p).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) j) p).val:Word w))
    (oldDepth : ∀v,before ((depths).base+(oldId v).val)=((Z).placement.b (B.frame.host v):Word w))
    (oldLevels : ∀j,j < (levels).size → before ((levels).base+j)=((j-cc+1:ℕ):Word w))
    (depthWidth : ∀v : B.next.V,(depthAt v) ≤ (U₀).oldWidth)
    (short : ∀v : B.next.V,∀t∈[1,cap,(depthAt v)-cc+1,shapeId v],t < 2^a₀) :
    let done_:=u.sheetsResult ok ((dir).result scene before)
    u.throughOperandDate.Runs m done_ ∧ u.throughOperandDate.cheap ∧
    ∀x : DescentColonies.Block k,(((V₀).controlRegisters.live start x.val).Fits w ceiling ∧
      Source ((V₀).controlRegisters.live start x.val) ((c₀).enabled (values x) (fun _=>1)) M done_) ∧
      ∀j : Fin 4,((V₀).controlRegisters.ports start cap x.val u.bank.inverse depths levels j).Fits w ceiling ∧
        Source ((V₀).controlRegisters.ports start cap x.val u.bank.inverse depths levels j)
          ((c₀).enabled (values x) (controlScalar B previous next j)) M done_ := by
  let actorMem:=(dir).result scene before
  let rendered:=u.beforeControl ok actorMem
  let finalC:=((c₀).phase start scene (dir).count (dir).inverse w).image rendered
  intro done_
  have front:=u.run_to_sheets_from_actors ok m actorMem ran cheap
  refine ⟨front.1,front.2.1,?_⟩
  have earlier:=u.control_frames ok m actorMem ran cheap
  have he : (V₀).actorEnd base₀=(dir).endAddress:=congrArg DescentResetNewActorDirectory.Layout.endAddress grid
  have ct : u.bank.count=(dir).count:=congrArg DescentResetNewActorDirectory.Layout.count grid
  have inv : u.bank.inverse=(dir).inverse:=congrArg DescentResetNewActorDirectory.Layout.inverse grid
  have eqRoof : ceiling=(c₀).endAddress start:=congrArg (fun c : Chart=>c.endAddress start) chart
  have ch : (U₀).chunksPerHost=chunks (2^cc) oldM:=congrArg DescentResetNewActorDirectory.Layout.preChunks grid
  have sh : (U₀).shapes=Q:=congrArg DescentResetNewActorDirectory.Layout.shapes grid
  have nh : (U₀).hosts=oldH:=congrArg DescentResetNewActorDirectory.Layout.oldHosts grid
  have stages:=(V₀).control_cuts ((V₀).linkedRankInputs u.sectors ((V₀).sheetsStart base₀)) base₀
  have prep : (V₀).sheetsStart base₀ ≤ (V₀).candidateEnd base₀:=by
    rw [←ok.matched]
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have low : (dir).endAddress ≤ start := by
    obtain ⟨_,_,a,b,c,d,e,f,_⟩:=ok.ordered
    have stop:=stages.1
    omega
  have physical : (dir).endAddress < 2^w := he ▸ ok.actor.room
  have roof : (c₀).endAddress start < 2^w := eqRoof ▸ ((stages.2.2.trans ((V₀).final_ge base₀)).trans_lt ok.full)
  have room : Room dims (State.layout dims start scene (dir).count (dir).inverse) 0 w := by
    have acquired:=ok.controls
    unfold ResetOutput.ControlRoom at acquired
    simpa only [chart,ct,inv] using acquired
  have hold : ∀addr,addr < (dir).endAddress → rendered addr=actorMem addr := by
    intro addr ha
    exact earlier.2 _ (ha.trans_le he.ge)
  have tailFrame : ∀addr,addr < (c₀).endAddress start → done_ addr=finalC addr := by
    intro addr ha
    have e:=earlier.1 addr (ha.trans_le eqRoof.ge)
    simpa only [ResetOutput.controlPhase,chart,ct,inv,finalC,rendered] using e
  obtain ⟨srcFit,depFit,levFit⟩:=(U₀).control_banks cb ok.actor.room
  have shapeRows : oldH*Q*chunks (2^cc) oldM ≤ (scene).size := by
    simpa only [sh,nh,ch,Nat.mul_left_comm,Nat.mul_assoc] using (U₀).extent_scene cb
  have dr : oldH ≤ (depths).size := nh ▸ ((U₀).extent_input cb).1
  have lr : ∀v : B.next.V,(depthAt v) < (levels).size:=fun v=>(depthWidth v).trans_lt ((U₀).extent_input cb).2.2.2.1
  have result:=recorded_control_all_rows B previous next start first scene depths levels before rendered
    oldPos newPos oldBits actors oldDepth oldLevels srcFit shapeRows depFit dr levFit lr
    (ch ▸ ok.actor.parts) physical low hold room roof short
  have within : (dir).endAddress ≤ (c₀).endAddress start:=low.trans (by rw [←eqRoof];exact stages.2.1)
  have up {a : Bank} (h : a.Fits w (dir).endAddress) : a.Fits w ((c₀).endAddress start):=
    ⟨h.1,h.2.1,h.2.2.trans within⟩
  have liftOld {a : Bank} (h : a.Fits w first) : a.Fits w ((c₀).endAddress start):=
    up ⟨h.1,h.2.1,h.2.2.trans (Nat.le_add_right ..)⟩
  have live:=recorded_control_sources B previous next start (dir).inverse depths levels finalC
    ((c₀).resident start scene (dir).count (dir).inverse rendered) roof (up ((dir).fits physical).2.2.2.2)
    (liftOld depFit) (liftOld levFit) result.1 result.2
  have carry {b} (x : Expr) (vals : Fin H→Fin J→Cell b)
      (saved : x.Fits w ((c₀).endAddress start) ∧ Source x vals M finalC) :
      x.Fits w ((c₀).endAddress start) ∧ Source x vals M done_ :=
    ⟨saved.1,fun p=>(eval_below x _ finalC done_ saved.1 tailFrame).trans (saved.2 p)⟩
  intro x
  rw [eqRoof,chart,inv]
  exact ⟨carry _ _ (live x).1,fun j=>carry _ _ ((live x).2 j)⟩

theorem calendar_control_sources (grid : (U₀).directory cb=dir)
    (chart : (V₀).controlRegisters=c₀)
    (m before : Memory w)
    (ran : ((head₀).seq op₀).Exec m ((dir).result scene before) (time₀+clock₀))
    (cheap : CheapCode ((head₀).seq op₀))
    (oldPos : 0 < oldM) (newPos : 0 < M) (oldBits : oldM ≤ w)
    (_hosts : 0 < H) (_sheets : 0 < chunks J M)
    (actors : ∀(j : Fin Q) (p : Row oldH (2^cc) oldM),
      before ((scene).base+j.val*(oldH*chunks (2^cc) oldM)+(row _ _ _ p).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) j) p).val:Word w))
    (oldDepth : ∀v,before ((depths).base+(oldId v).val)=((Z).placement.b (B.frame.host v):Word w))
    (oldLevels : ∀j,j < (levels).size → before ((levels).base+j)=((j-cc+1:ℕ):Word w))
    (depthWidth : ∀v : B.next.V,(depthAt v) ≤ (U₀).oldWidth)
    (short : ∀v : B.next.V,∀t∈[1,cap,(depthAt v)-cc+1,shapeId v],t < 2^a₀) :
    let done_:=u.sheetsResult ok ((dir).result scene before)
    u.throughOperandDate.Runs m done_ ∧ u.throughOperandDate.cheap ∧
    ∀x : DescentColonies.Block k,(((V₀).controlRegisters.live start x.val).Fits w ceiling ∧
      Source ((V₀).controlRegisters.live start x.val) ((c₀).enabled (values x) (fun _=>1)) M done_) ∧
      ∀j : Fin 4,((V₀).controlRegisters.ports start cap x.val u.bank.inverse depths levels j).Fits w ceiling ∧
        Source ((V₀).controlRegisters.ports start cap x.val u.bank.inverse depths levels j)
          ((c₀).enabled (values x) (controlScalar B previous next j)) M done_ :=
  calendar_control_all_rows B previous next u ok grid chart m before ran cheap oldPos newPos oldBits
    actors oldDepth oldLevels depthWidth short

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
