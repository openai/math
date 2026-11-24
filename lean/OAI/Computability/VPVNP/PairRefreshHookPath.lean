import OAI.Computability.VPVNP.PairRefreshHookSite
import OAI.Computability.VPVNP.PairRefreshTraversalExact
import OAI.Computability.VPVNP.PairRefreshHookPacketFrame

/-!
# Exact native action of one selected refresh row

The successful action is fixed by the frozen level, the parsed old half and
the incoming upper scratch. The proof follows the physical role from its entry
to the common DFS continuation. A failed local action excludes a return for
every continuation and fuel.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords CompressorRecords.PortRefresh RefreshMapOperands NewSlots
open NodeArguments NodeArguments.ChildScan
open TraversalControllerInputs VertexImage DFS
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  {bits n hist t pcs regs : ℕ} (R : Site B n hist bits)
  (ties : Fin t ≃ Tie (2 ^ S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (loc : Fin (RefreshVertex.refreshSegment B ties stride order).count → Fin pcs)
  (dfs : Fin 9 ↪ Fin regs) (saved : Saved ↪ Fin regs)
  (reg : Fin (RefreshVertex.refreshSegment B ties stride order).privateRegs ↪ Fin regs)
  (done : Fin pcs)
  (M : Machine bits pcs regs 11) (m : Memory bits)

local notation "body" => TraversalPlan.body B ties stride order
local notation "locator" => TraversalPlan.locatorBank B ties stride order
local notation "bodyLoc" => RefreshVertexAssembly.bodyPC S.portExponent body locator loc
local notation "bodyBank" => RefreshVertexAssembly.bodyRegs S.portExponent body locator reg
local notation "segment" => RefreshVertex.refreshSegment B ties stride order
local notation "H₀" => LeafArena.Regions.histBase (regions R)
local notation "A" => arena R
local notation "P" => parent R
local notation "W" => BurstRAM.Word bits
local notation "O" => NewSlots.sites (State.baseIndex (state R)) (bitWordFinEquiv (lanes R))
local notation "oldSite" => olderSite R
local notation "newSite" => newerSite R
local notation "X" => state R
local notation "Y" => nextState R
local notation "child" => oldNode R

variable (installed : ∀ i, M.code (loc i) =
    ((RefreshVertex.refreshSegment B ties stride order).row loc dfs saved reg done i).resize bits)
  (apartD : ∀ i j, reg i ≠ dfs j) (apartS : ∀ i j, reg i ≠ saved j)
  (facts : R.Published ties stride M.publicData m)

include facts in
private theorem wordPos : 0 < bits := by
  have upper := facts.wide
  have pos := Nat.two_pow_pos S.portExponent
  by_contra! no
  have zero : bits=0 := Nat.eq_zero_of_le_zero no
  rw [zero,pow_zero] at upper
  omega

include installed facts in
/-- At this frozen row, a missing child half rejects before the map starts. -/
theorem short_path (c : Config bits pcs regs) (entry : c.pc = loc (segment).entry)
    (node : (c.reg (dfs 7)).val = P) (bs : List Bool)
    (short : bs.length < RefreshHalfDecoder.width X oldSite) :
    ¬ Returns M c m bs := by
  obtain ⟨h,f,pit,off,base,initial,ls,j,id,heads,hj,_,_,pos,last⟩ := facts.location
  let z : (X).network.Half oldSite := (fun _ _ _ => false,fun _ _ _ => false)
  have e := TraversalGeometry.argument_end R.degree n R.rowEnd hist X oldSite z child
    R.room.childBound R.room.oldDegree R.room.oldWidth
  have histFit : H₀ < 2^bits :=
    ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans_lt R.room.capacity.room
  exact RefreshVertexAssembly.reject_short S.portExponent body locator loc dfs saved reg done M
    installed X oldSite z R.prev m A R.older B.recordLimit R.listHead heads j R.level hj id c entry
    (node.trans pos) last facts.fields (node.symm ▸ facts.children) facts.oldCols facts.strideFit
    (facts.before.trans (node ▸ (c.reg (dfs 7)).isLt)) (e.trans_lt histFit) bs
    (by rwa [packed_length])

set_option maxHeartbeats 1400000 in
-- Joining the dependent child and map executions requires matching their register banks and frames.
include installed facts apartD apartS in
theorem action_path (node : W) (c : Config bits pcs regs) (entry : c.pc = loc (segment).entry)
    (popped : c.reg (dfs 7) = node) (endWord : c.reg (dfs 6) = word n)
    (ready : R.Prepared node (scratch n c.privateMem))
    (old : (X).network.Half oldSite) (new : (Y).network.Half newSite)
    (readParent : RefreshHalfDecoder.parent Y newSite A P (scratch n c.privateMem) = some new) :
    let packet := RefreshHook.packet X oldSite child old
    let front := R.front M.publicData m node old
    match R.action ties stride order M.publicData m old new
        (packet.write A (scratch n c.privateMem)) with
    | none => ∀ tail, ¬ Returns M c m (packed X oldSite old ++ tail)
    | some (es,next) =>
      ∃ out, out.pc = done ∧ ShrinkRole.Frame dfs n c out ∧ scratch n out.privateMem = next ∧
        ChildScan.Prefix M m c out (packed X oldSite old) (front++es) ∧
        ∀ i : Fin hist, out.privateMem (word (H₀+i.val)) = c.privateMem (word (H₀+i.val)) +
          (((TraversalPlan.emitted B order X R.choice R.port old new).getD []).count i : W) := by
  intro packet front
  obtain ⟨atNode,resident,typed,typedStored⟩ := ready
  have decoded := RefreshHalfDecoder.parent_eq Y newSite A P (scratch n c.privateMem)
    typed typedStored (wordPos R ties stride M m facts)
  obtain rfl := Option.some.inj (readParent.symm.trans decoded)
  have parentData : NodeFields A P Y newSite new c.privateMem := fun dir j i =>
    Packet.read_field Y newSite new A P c.privateMem (R.newFit new) typedStored dir j i
  obtain ⟨h,f,pit,off,base,initial,ls,j,id,heads,hj,siteEq,later,pos,last⟩ := facts.location
  have nodeVal := (congrArg Fin.val popped).trans atNode
  have histLimit : H₀+hist ≤ R.regions.cacheBase := Nat.le_add_right ..
  have histFits := histLimit.trans_lt R.room.capacity.room
  have oldEnd := TraversalGeometry.argument_end R.degree n R.rowEnd hist X oldSite old child
    R.room.childBound R.room.oldDegree R.room.oldWidth
  have oldFit := oldEnd.trans_lt ((Nat.le_add_right ..).trans_lt histFits)
  have early : n < (A).base child :=
    Nat.lt_add_of_pos_right (Nat.mul_pos facts.positive (Nat.succ_pos _))
  have row' : Row m (c.reg (dfs 7)).val R.listHead [word child] := nodeVal.symm ▸ facts.children
  obtain ⟨mid,first,atBody,located,mem,per,keep⟩ :=
    RefreshVertexAssembly.load_child S.portExponent body locator loc dfs saved reg done M installed
      X oldSite old R.prev m A R.older B.recordLimit R.listHead heads j R.level hj id c entry
      (nodeVal.trans pos) last facts.fields row' facts.oldCols facts.strideFit
      (facts.before.trans (atNode ▸ node.isLt)) oldFit
  have locRun : ChildScan.Prefix M m c mid (packed X oldSite old) front := by
    unfold front Site.front
    rw [later,← popped]; exact first
  have geom' := RefreshVertexPacket.geometry X oldSite old A R.older B.recordLimit c.privateMem
    R.geometry R.roleOffset (word H₀) resident early (oldEnd.trans facts.roleAfter)
    (oldEnd.trans facts.histAfter)
  have old' := RefreshVertexPacket.fields X oldSite old A R.older B.recordLimit c.privateMem
    oldFit.le
  have new' := RefreshVertexPacket.parent_fields X oldSite old A R.older B.recordLimit c.privateMem
    Y newSite new P facts.before (R.oldFit old).2.1 (R.newFit new).2.2 parentData
  have stack' := (keep (dfs 6) (fun ⟨i,e⟩ => apartD i 6 e)).trans endWord
  have fitId : id.val < 2^bits := by
    have small : id.val ≤ TraversalRows.address B.recordLimit
        (TraversalRoles.layerBase B.recordLimit base (initial::ls.map Prod.fst) j) id :=
      (Nat.le_mul_of_pos_left _ (by omega : 0<B.recordLimit+2)).trans (Nat.le_add_left ..)
    exact small.trans_lt (pos ▸ atNode ▸ node.isLt)
  have site' := (congrArg Fin.val located.owner).trans ((Nat.mod_eq_of_lt fitId).trans siteEq)
  have sc : scratch n mid.privateMem = packet.write A (scratch n c.privateMem) :=
    RefreshHook.child_scratch X oldSite old A R.older B.recordLimit mem
  have res := TraversalPlan.canonical_body B ties stride order X R.choice R.port R.degree n R.rowEnd
    child P R.room old new m (levelHead M.publicData m R.level).val
    (levelHead M.publicData m (R.level+1)).val R.geometry R.prev R.next R.start R.listHead
    bodyLoc dfs saved bodyBank done M
    (RefreshVertexAssembly.body_linked S.portExponent body locator loc dfs saved reg done M
      installed)
    (fun _ i => apartD _ i) (fun _ i => apartS _ i) mid atBody stack' (mem ▸ geom')
    (congrArg Fin.val located.oldHead) (congrArg Fin.val located.state.current) site'
    ((congrArg Fin.val located.state.node).trans nodeVal) facts.headers facts.children
    facts.lanesFit facts.terms facts.oldCols facts.newCols (mem ▸ old') (mem ▸ new') facts.wide _ sc
  unfold action
  cases eqn : TraversalPlan.canonicalAction B ties stride order X R.choice R.port R.degree n
      R.rowEnd child P R.room old new m (levelHead M.publicData m R.level).val
      (levelHead M.publicData m (R.level+1)).val R.geometry
      (packet.write A (scratch n c.privateMem)) with
  | none =>
    rw [eqn] at res
    exact fun tail => mt (locRun.returns tail).mp (res tail)
  | some value =>
    obtain ⟨es,next⟩ := value
    rw [eqn] at res
    obtain ⟨out,bodyRun,_,_,_,stop,persist,regs',external,hits,updated⟩ := res
    have cf := RefreshHook.child_frame X oldSite old A R.older B.recordLimit dfs reg apartD
      c mid mem per keep (R.oldFit old)
    have low : n ≤ H₀ := Nat.le_add_right ..
    have bf := RefreshHook.body_frame dfs bodyBank (fun _ j => apartD _ j) mid out persist regs'
      external low (by omega) histFits.le
    have frame := cf.trans bf
    refine ⟨out,stop,frame,updated,by simpa only [List.append_nil] using locRun.trans bodyRun,?_⟩
    intro i
    have histVal : (word (bits := bits) (H₀+i.val)).val = H₀+i.val :=
      Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans histFits)
    have histMem := RefreshVertexPacket.outside X oldSite old A R.older B.recordLimit c.privateMem
      oldFit.le (word (H₀+i.val))
      (Or.inr ((oldEnd.trans (Nat.le_add_right H₀ i.val)).trans histVal.symm.le))
    exact (hits i).trans (congrArg (fun x => x+_) ((congrFun mem _).trans histMem))

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
