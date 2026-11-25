import OAI.Hierarchy.DescentResetActorIssued
import OAI.Hierarchy.DescentResetActorRaster
import OAI.Hierarchy.DescentResetHeaderPlacement
import OAI.Hierarchy.DescentPackedMatchPrepareIssued

namespace OAI
/-! # Successor actor occupancy in the actual reset output coordinate system -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentResetAttachments
open DescentActorRaster DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage.Prepare
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "raw" => B.raw
local notation "A" => B.next.placement
local notation "groups" => S.groupCount (i+1)
local notation "dense" => ((Z).rawHostRank T vertex).trans Fin.valEmbedding
local notation "rawSite" => (raw).siteFrom (groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "board" => blocks B
local notation "installed" => (Z).actualRecord T vertex

/-- At the successor stage every remixed high window is decoded by the actual
public group/block bijection and the actual normalized host identifier. -/
theorem actor_coordinate (q : B.next.V) (g : Fin groups) (x : DescentColonies.Block k) :
    (∃u, (A).pos u=(g,q) ∧ (A).block u=x) ↔
      (Z).emits T q.val ((digits).symm (g,x)) := by
  rw [←ResetInput.reset_occupied]
  constructor
  · rintro ⟨w,addr,low⟩
    obtain ⟨v,rfl⟩:=(hop).surjective w
    have eqn:=named_home B v
    change ((A).pos ((hop) v),(A).block ((hop) v))=_ at eqn
    rw [addr,low] at eqn
    have host := congrArg (fun y=>y.1.2) eqn
    have old := congrArg (fun y=>(y.1.1,y.2)) eqn
    exact ⟨v,congrArg Subtype.val host.symm,((digits).symm_apply_eq.mpr old).symm⟩
  · rintro ⟨v,name,atBlock⟩
    have atHost : (Z).placed T v=q:=Subtype.ext name
    have eqn:=named_home B v
    rw [atHost,atBlock,Equiv.apply_symm_apply] at eqn
    exact ⟨(hop) v,congrArg Prod.fst eqn,congrArg Prod.snd eqn⟩

variable {H : ℕ} (rank : B.next.V↪Fin H)
theorem actor_bit_at (u : B.next.V) (g : Fin groups) (x : DescentColonies.Block k) :
    digit 1 x.val ((actors A (Function.Embedding.refl _) rank (rank u) g).val)=
      if (Z).emits T u.val ((digits).symm (g,x)) then 1 else 0 := by
  have yes : ∃z : Fin groups×B.next.V,z.1=g ∧ rank z.2=rank u:=⟨(g,u),rfl,rfl⟩
  have pair : yes.choose=(g,u):=Prod.ext yes.choose_spec.1 (rank.injective yes.choose_spec.2)
  simp only [actors,spreadField,Function.Embedding.refl_apply,dite_eq_left yes,pair,
    DescentActorRaster.actor_read,actor_coordinate]

theorem actor_missing (j : Fin H) (vacant : ∀v,rank v≠j) (g : Fin groups) :
    actors A (Function.Embedding.refl _) rank j g=0 := by
  simp [actors,spreadField,show ¬∃z : Fin groups×B.next.V,z.1=g ∧ rank z.2=j from
    fun ⟨z,_,hz⟩=>vacant _ hz]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
