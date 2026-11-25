import OAI.Hierarchy.DescentCalendarControlSources
import OAI.Hierarchy.DescentDatedPublicValues

namespace OAI
/-! Native registers of the public range decoder and their zero/shape dispatch at every real host. -/
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

theorem public_control_operands (grid : (U₀).directory cb=dir)
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
    let actorMem:=(dir).result scene before
    let done_:=u.sheetsResult ok actorMem
    let prior:=u.beforeSetupImage ok actorMem
    (∀n,n<ceiling→done_ n=prior n) ∧
    ∀x : DescentColonies.Block k,
      ((((V₀).controlRegisters.live start x.val).Fits w ceiling ∧
        Source ((V₀).controlRegisters.live start x.val) ((c₀).enabled (values x) (fun _=>1)) M done_) ∧
        ∀j : Fin 4,((V₀).controlRegisters.ports start cap x.val u.bank.inverse depths levels j).Fits w ceiling ∧
          Source ((V₀).controlRegisters.ports start cap x.val u.bank.inverse depths levels j)
            ((c₀).enabled (values x) (controlScalar B previous next j)) M done_) ∧
      ∀h₀ : Fin H,∀group_ : Fin J,
        let active:=(c₀).enabled (values x) (fun _=>1) h₀ group_
        let reg:=fun j : Fin 4=>(c₀).enabled (values x) (controlScalar B previous next j) h₀ group_
        (active.val=0 → (reg 1).val=0) ∧
          ∀hv : h₀.val<Fintype.card B.next.V,active.val≠0 →
            (reg 3).val=(finProdFinEquiv.symm ((Z).rawAtIndex T rank ⟨h₀.val,hv⟩) :
              Fin oldH × Fin Q).2.val := by
  have rows:=calendar_control_all_rows B previous next u ok grid chart m before (@ran) (@cheap) oldPos newPos
    oldBits actors oldDepth oldLevels depthWidth short
  have earlier:=(u.control_frames ok m ((dir).result scene before) (@ran) (@cheap)).1
  refine ⟨earlier,fun x=>⟨rows.2.2 x,fun h₀ group_=>?_⟩⟩
  have large (v : B.next.V) : (shapeId v)<2^a₀:=short v _ (by simp)
  classical
  by_cases live : Nonempty B.next.V
  · obtain ⟨v⟩:=live
    have positive : 0<a₀:=by
      by_contra! zero
      have small:=short v 1 (by simp)
      rw [Nat.eq_zero_of_le_zero zero, pow_zero] at small
      omega
    exact recorded_dispatch (oldM:=oldM) (M:=M) B previous next h₀ group_ x positive large
  · have absent : ¬∃v : B.next.V,(B.next.vertex.trans (Fin.castLEEmb next)) v=h₀ :=
      fun hit=>live ⟨hit.choose⟩
    have off:=control_receiver_none B next h₀ (by unfold controlReceiver; exact dite_eq_right absent) group_ x
    simp [DescentResetControlRegisters.Chart.enabled,off]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
