import OAI.Hierarchy.DescentContactCurrentRank
import OAI.Hierarchy.DescentResetPeerJointPacked
import OAI.Hierarchy.DescentResetPeerCorrectionRoom

namespace OAI
/-! # A compact receiver reads all four packed menu entries on one reached memory -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentPackedColony DescentPackedZip DescentResetOriginHaloRAM DescentGroupPeerOrder DescentSortedRoster
open DescentResetPeerJointRAM DescentCommonHost DescentResetWindowResidentSources
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ} {input : Reached W G q ε S k i z D w hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "width" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "used" => Fintype.card B.next.V
variable {H O ww b M groups : ℕ} (old : Fintype.card input.V≤O) (live : used≤H)
local notation "host" => input.vertex.trans (Fin.castLEEmb old)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans host
local notation "raw" => (Z).rawHostRank T vertex
local notation "dense" => compactActorOrder B old
local notation "names" => compactActorName B old
local notation "adj" => DescentPacking.PackedMatch.Local.Stage.hostRotor host (hostRoster A ((host).trans Fin.valEmbedding))
local notation "P₀" => O*width
local notation:max "deck" address:arg src:arg => DescentResetPeerJointPacked.phase ww address H P₀ O width (A).degree groups M b src

theorem packed_current_rank (base : ℕ) (src : DescentResetPeerJointRAM.Sources) (m : Memory ww)
    (rows : Fin P₀→Fin 4→Option (Fin P₀)) (room : DescentResetPeerJointRAM.Room src base H P₀ O (A).degree ww)
    (stored : DescentResetPeerJointRAM.Reads src used names (indexed rows) adj m)
    (jointRoom : width*radix (A).degree≤2^b) (narrow : b≤ww) (small : 4≤2^b)
    (space : DescentResetPeerJointPacked.endAddress base H P₀ groups M b<2^ww)
    (word : Expr) (request : Fin H→Fin groups→Cell b)
    (fifth : Source word request M ((deck base src).image m))
    (peers : ∀v : B.next.V,present rows (raw v)=(insert v (B.next.placement.near v)).map raw) :
    let num := fun h j=>(DescentResetPeerJointRAM.value O width (A).degree adj used names (indexed rows) h j : Cell b)
    let «fields» := fun (n : Fin 5) (h : Fin H) (g : Fin groups)=>Fin.lastCases (request h g) (num h) n
    let args : Fin 5 → Expr := Fin.lastCases word (DescentResetPeerJointPacked.expr base H P₀ groups M b)
    (deck base src).Runs m ∧ (∀j,Source (args j) («fields» j) M ((deck base src).image m)) ∧
    ∀(u v : Host) (g : Fin groups),v∈sources B.next.placement u → (receiverRoot B v).1∈originDomain B u →
      (request ((dense u.1.2).castLE live) g).val=jointNumber B u (receiverRoot B v).1 (relativeShape B v) →
      (DescentResetJoinedRank.rank (fun j=>«fields» j ((dense u.1.2).castLE live) g)).val=localClass B u v:=by
  intro num «fields» args
  classical
  have positive : 0<width:=lt_of_lt_of_le (by decide : 0<2) (two_le_roster_card (Z).graph r Ht)
  have distinct:=hostRotor_distinct (A) host
  have all_:=DescentResetPeerJointPacked.run base width used src names (indexed rows) adj m live room stored distinct positive jointRoom space
  have fits (v : Fin H) (j : Fin 4) := DescentResetPeerJointRAM.value_lt adj names (indexed rows) v j distinct positive jointRoom
  refine ⟨all_.1,?_,?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun slot=>?_) j
    · have lastExpr : args (Fin.last 4) = word := Fin.lastCases_last ..
      have lastValues : «fields» (Fin.last 4) = request := by
        funext h groupIx
        exact Fin.lastCases_last ..
      exact Eq.mp (congrArg₂ (fun expression values => Source expression values M ((deck base src).image m))
        lastExpr.symm lastValues.symm) fifth
    · have printed:=all_.2.1 slot
      have same (h : Fin H) : (⟨_,fits h slot⟩ : Cell b)=num h slot:=Fin.ext (Fin.val_cast_of_lt (fits h slot)).symm
      simpa only [args,«fields»,Fin.lastCases_castSucc,same] using printed
  · intro u v groupIx actual prior same
    let receiver := (dense u.1.2).castLE live
    apply current_rank B old live u v _ small rows base src m room stored
      (jointRoom.trans (Nat.pow_le_pow_right (by decide) narrow)) (peers _) actual prior
    · have last : «fields» (Fin.last 4) receiver groupIx = request receiver groupIx := Fin.lastCases_last ..
      exact (congrArg Fin.val last).trans same
    · intro j
      have cellAt : «fields» j.castSucc receiver groupIx = num receiver j := Fin.lastCases_castSucc ..
      have readAt := DescentResetPeerJointRAM.read base width used src names (indexed rows) adj m live room stored receiver j
      have smallAt := fits receiver j
      have wordAt := smallAt.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) narrow)
      exact (congrArg Fin.val cellAt).trans ((Fin.val_cast_of_lt smallAt).trans
        ((Fin.val_cast_of_lt wordAt).symm.trans (congrArg Fin.val readAt.symm)))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
