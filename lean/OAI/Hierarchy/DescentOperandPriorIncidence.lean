import OAI.Hierarchy.DescentRetainedOriginFacts
import OAI.Hierarchy.DescentDatedOriginCodes
import OAI.Hierarchy.DescentTerminalSignedGrainWord
import OAI.Hierarchy.DescentIssuedFallbackPanel

namespace OAI
/-! # Recovering the signed old port of a retained cable operand from the packed census -/
namespace Hierarchy.DescentOperandPriorIncidence
open DescentSixParty DescentColonies DescentSharedCableNames DescentTerminalPointerDigits
open DescentTerminalSignedGrainWord DescentStageEdgeReceipt DescentGroupPeerOrder
open DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescentPackedColony
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i w M G H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {T : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W T q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
  (ready : A.StateBounds S i) (groups : J↪Fin G) (hosts : V↪Fin H)
set_option quotPrecheck false
local notation "names" => cableNames k (groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding))
local notation "board" => Prepare.signed A native S ready groups hosts
variable (cables : Block k→Fin (2*A.cap)→Bank) (mem : Memory w)
  (prior : ∀ (x : Block k) (j : Fin (2*A.cap)), DescentPackedColony.Reads (cables x j)
      (fun h g => DescentSignedCableCodec.encode (D:=A.degree) (cap:=A.cap)
        (Prepare.signed A native S ready groups hosts x j h g)) M mem)
  (pos : 0<M) (wide : DescentSignedCableCodec.width A.degree A.cap*M≤w)
  (v : W.graph.Site) (coords : Function.Injective (fun s=>(A.pos s,A.block s)))
local notation "home" => Stage.home A v
local notation "live" => Stage.live A native S ready names home
local notation "tokenAt" => DescentTerminalPointerDigits.token A native S ready names v
local notation "ports" => A.CellPorts (home).1.1 (home).1.2 (home).2
local notation "signed" => Stage.signed A native S ready (home).1 (home).2

def fromBank (s : Fin (2*A.cap)) : Option (ℕ×ℕ) :=
  point A.degree A.cap (project A.degree A.cap
    (chip (cables (home).2 s) mem (hosts (home).1.2) (groups (home).1.1) pos))

include prior wide in
theorem read_port (p : ports) (e : Incident W.graph v) (j : Fin (A.grainCount e.val))
    (same : Stage.recover A home p=⟨e.val,j⟩) :
    fromBank A groups hosts cables mem pos v (signed p)=some (tokenAt ⟨e,j⟩) := by
  have stored := stage_grain A native S ready groups hosts cables mem prior pos wide home.2 (signed p) home.1
  refine stored.trans ?_
  rw [Stage.signed_read A native S ready names home p, Option.map_some, grain_read A native S ready names v p e j same]

include prior wide coords in
theorem resolve_slot (s : Fin (2*A.cap)) (e : Incident W.graph v) (j : Fin (A.grainCount e.val))
    (hit : fromBank A groups hosts cables mem pos v s=some (tokenAt ⟨e,j⟩)) :
    ∃p : ports,signed p=s ∧ Stage.recover A home p=⟨e.val,j⟩ := by
  have hit := (stage_grain A native S ready groups hosts cables mem prior pos wide home.2 s home.1).symm.trans hit
  by_cases found : ∃p : ports,signed p=s
  · obtain ⟨p,rfl⟩:=found
    rw [Stage.signed_read,Option.map_some,Option.some.injEq] at hit
    refine ⟨p,rfl,?_⟩
    cases p with
    | inl l =>
      rcases l with ⟨⟨e',ep,eb⟩,u⟩
      let edge : Incident W.graph v:=⟨e',Or.inl (coords (Prod.ext ep eb))⟩
      have eqn := (tokenAt).injective ((grain_read A native S ready names v _ edge u rfl).symm.trans hit)
      exact congrArg (fun a : SiteGrains A v=>(⟨a.1.val,a.2⟩:Stage.Grain A)) eqn
    | inr l =>
      rcases l with ⟨⟨e',ep,eb⟩,u⟩
      let edge : Incident W.graph v:=⟨e',Or.inr (coords (Prod.ext ep eb))⟩
      have eqn := (tokenAt).injective ((grain_read A native S ready names v _ edge u rfl).symm.trans hit)
      exact congrArg (fun a : SiteGrains A v=>(⟨a.1.val,a.2⟩:Stage.Grain A)) eqn
  · rw [Stage.signed_empty _ _ _ _ _ _ _ (not_exists.mp found)] at hit
    contradiction

include prior wide coords in
theorem seek_port (p : ports) (e : Incident W.graph v) (j : Fin (A.grainCount e.val))
    (same : Stage.recover A home p=⟨e.val,j⟩) :
    seek (fromBank A groups hosts cables mem pos v) (Stage.signedBit A home p)
      (tokenAt ⟨e,j⟩)=some (signed p) := by
  apply seek_exact
  intro slot
  constructor
  · rintro ⟨side,output⟩
    obtain ⟨b,rfl,got⟩:=resolve_slot A native S ready groups hosts cables mem prior pos wide v coords _ e j output
    rw [sign_real] at side
    exact congrArg signed (port_unique A v b p (got.trans same.symm) side)
  · rintro rfl
    exact ⟨sign_real A native S ready v p,
      read_port A native S ready groups hosts cables mem prior pos wide v p e j same⟩

end
end Hierarchy.DescentOperandPriorIncidence

end OAI
