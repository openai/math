import OAI.Hierarchy.DescentPhysicalStemOperand
import OAI.Hierarchy.DescentResetStemCalibratedIssue
import OAI.Hierarchy.DescentResetStemOriginalSlots

namespace OAI
/-! # Every signed stem operand reads the actual graph metadata after trunk publication -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentResetTrunkCompactPointer DescentResetFieldAssembler DescentCommonHost DescentResetTrunkIssue DescentActorRaster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals

open DescentDatedAddressBook DescentSIMDLookup DescentPackedZip DescentResetFieldAssembler
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "groups" => S.groupCount (i+1)
local notation "L" => 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)
local notation "cap" => input.placement.cap
local notation "Slot" => Fin L × Fin (2*cap)
local notation "ord" => DescentResetStemPackedIssue.ordinal L cap

theorem physical_stem_operand (v : CandidateFront) (floor : ℕ) (s : v.Scene) {bw : ℕ}
    (safe : v.SceneRoom floor s bw) (m : Memory bw) (room : v.trunkEnd floor<2^bw)
    (blocks : v.blocks=2^k) (queries : v.signedQueries=stemsCount B) (size : v.peer.groups=groups)
    (emitted : ∀(x : Fin (2^k)) (sign : Bool) (slot : Slot) (p : Row v.newHosts groups v.peer.lanes),
      (v.received floor s safe).image m
        (v.stemOutput floor+(finProdFinEquiv (x,(ord) (sign,slot))).val*(v.newHosts*chunks groups v.peer.lanes)+
          (row v.newHosts groups v.peer.lanes p).val)=
        ((data (fun r g₀=>(originalTrunkRack B r).elim 0 (fun a=>DescentResetFieldAssembler.raw v.metaBits («meta» B ((g₀,a),x)
          (localOrigin B ((g₀,a),x) (stemIndex B sign slot))))) p).val:Word bw)) :
    (v.trunkScene floor s safe).Runs m ∧ ∀(x : Fin (2^k)) (j : Fin (stemsCount B)),
      (v.stemOperand floor x.val j.val).Fits bw (v.trunkEnd floor) ∧
        Source (v.stemOperand floor x.val j.val)
          (fun (r : Fin v.newHosts) g₀=>DescentResetFieldAssembler.raw v.metaBits (actualMeta B (originalTrunkRack B) x (stemShelf B j) r g₀))
          v.peer.lanes ((v.trunkScene floor s safe).image m) :=by
  refine ⟨(v.trunkScene_any floor s safe m room).1,?_⟩
  intro x j
  apply v.stem_operand_at_indices floor s blocks queries size safe m room x j
  intro p
  have observed:=emitted x (stemTag B j).1 (stemTag B j).2 p
  have idx : (ord) ((stemTag B j).1,(stemTag B j).2)=j:=(ord).apply_symm_apply j
  rw [idx,stem_shelf_number] at observed
  have same :
      (fun (r : Fin v.newHosts) (g₀ : Fin groups)=>(originalTrunkRack B r).elim 0 (fun a=>DescentResetFieldAssembler.raw v.metaBits
        («meta» B ((g₀,a),x) (localOrigin B ((g₀,a),x) (stemShelf B j)))))=
      fun r g₀=>DescentResetFieldAssembler.raw v.metaBits (actualMeta B (originalTrunkRack B) x (stemShelf B j) r g₀) :=by
    funext r g₀
    cases found:originalTrunkRack B r <;> simp [actualMeta,found,DescentResetTrunkIssue.zero_raw]
  rw [same] at observed
  exact observed

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
