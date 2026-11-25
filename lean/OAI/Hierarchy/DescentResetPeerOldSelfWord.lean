import OAI.Hierarchy.DescentResetPeerOldCorrection
import OAI.Hierarchy.DescentResetStemObservedInputs
import OAI.Hierarchy.DescentResetTrunkCompactSuffix
import OAI.Hierarchy.DescentResetCompactGeometryRead
import OAI.Hierarchy.DescentGenuineRosterDistinct
import OAI.Hierarchy.DescentOrdinaryRosterRead

namespace OAI
/-! The physically issued predecessor-loop correction is the original numbered
stem's common host field at each actual successor actor. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDenseHostOrder DescentResetStemCompactOrder DescentResetStemWord
open DescentGroupPeerOrder DescentSortedRoster DescentResetOriginHaloRAM DescentResetPeerOldCorrection
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentActorRaster DescentCommonHost
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) {O H : ℕ} (prev : Fintype.card input.V≤O)
local notation "A" => input.placement
local notation "named" => input.vertex.trans (Fin.castLEEmb prev)
local notation "old" => hostRotor named (hostRoster A ((named).trans Fin.valEmbedding))
local notation "pal" => DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) (GroupStage.depthBound D n f g)
local notation "N" => Fintype.card B.next.V

theorem original_self_code (u : input.V) :
    code (old (named u)) (named u)=
      hostCode (compress (hostDomain A input.vertex u) (input.vertex u).val) (decide (u∉(A).near u)) := by
  have pool : present old (named u)=((A).near u).map named:=by
    ext t
    simpa only [DescentSortedRoster.present,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map] using
      Chronology.original_hostRotor_rows A named u t
  have full : (present (closed old) (named u)).map Fin.valEmbedding=hostDomain A input.vertex u:=by
    rw [present_closed,pool,←Finset.map_insert,Finset.map_map,Finset.map_eq_image]
    rfl
  have ordinal : before (closed old) (named u) (named u)=compress (hostDomain A input.vertex u) (input.vertex u).val:=by
    rw [←full]
    simp only [before,compress,Finset.filter_map,Finset.card_map]
    rfl
  have same : named u∈present old (named u) ↔ u∈(A).near u:=by rw [pool];simp
  rw [code_eq old (named u) (hostRotor_distinct A named),ordinal]
  exact congrArg (fun z : Bool => 2*compress (hostDomain A input.vertex u) (input.vertex u).val+z.toNat)
    (decide_eq_decide.mpr (not_congr same))

theorem original_stem_self (next : N≤H) (v : Fin H) :
    DescentResetPeerOldCorrection.value (pal).card (compactActorName B prev) old v=
      stemSelfDigit B (originalTrunkRack B) v := by
  by_cases active : v.val<N
  · let i : Fin N:=⟨v.val,active⟩
    let actor:=(compactActorOrder B prev).symm i
    let orig:=stemOldHost B actor
    have position : (compactActorOrder B prev actor).castLE next=v :=by
      apply Fin.ext
      exact congrArg (fun x : Fin N=>x.val) ((compactActorOrder B prev).apply_symm_apply i)
    have has : originalTrunkRack B v=some actor:=position ▸ (original_rack_order B prev next).1 actor
    have addr : ((compactActorName B prev) i).val/(pal).card=(named orig).val :=
      (compact_host_fields B prev actor).2
    simp only [DescentResetPeerOldCorrection.value,dite_eq_left active,show (⟨v.val,active⟩:Fin N)=i from rfl,
      addr,dite_eq_left (named orig).isLt,stemSelfDigit,has,Option.elim_some]
    exact original_self_code prev orig
  · simp [DescentResetPeerOldCorrection.value,stemSelfDigit,originalTrunkRack,active]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
