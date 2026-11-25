import OAI.Hierarchy.DescentDatedOriginCodes
import OAI.Hierarchy.DescentOperandPriorIncidence
import OAI.Hierarchy.DescentDatedOperandDigits

namespace OAI
/-! # Recover the old outgoing ticket from a previous operand's stored cable name -/
namespace Hierarchy.DescentOperandPriorIncidence
open DescentSixParty DescentColonies DescentSharedCableNames DescentTerminalPointerDigits
open DescentTerminalSignedGrainWord DescentStageEdgeReceipt DescentGroupPeerOrder
open DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescentPackedColony
open scoped Classical Fin.CommRing
noncomputable section

private theorem seek_hit {cap : ℕ} (row : Fin (2*cap)→Option (ℕ×ℕ)) (face : Fin 2)
    (key : ℕ×ℕ) (s : Fin (2*cap)) (hit : seek row face key=some s) : row s=some key :=
  (of_decide_eq_true (List.find?_some
    (p := fun j : Fin (2*cap) => decide (sign cap j=face ∧ row j=some key))
    (l := List.finRange (2*cap)) (a := s) hit)).2

private theorem originIndex_hit {cap : ℕ} (row : Fin (2*cap)→Option (ℕ×ℕ)) (key : ℕ×ℕ)
    (s : Fin (2*cap)) (hit : originIndex row key=some s) : row s=some key := by
  cases first : seek row 0 key with
  | none=>exact seek_hit row 1 key s (by simpa [originIndex,first] using hit)
  | some t=>
    have eqn : t=s:=Option.some.inj (by simpa only [originIndex,first] using hit)
    exact eqn ▸ seek_hit row 0 key t first

private theorem originIndex_present {cap : ℕ} (row : Fin (2*cap)→Option (ℕ×ℕ)) (key : ℕ×ℕ)
    (face : Fin 2) (s : Fin (2*cap)) (hit : seek row face key=some s) : originIndex row key≠none := by
  fin_cases face
  · change seek row 0 key = some s at hit
    simp [originIndex,hit]
  · change seek row 1 key = some s at hit
    cases first : seek row 0 key <;> simp [originIndex,first,hit]


/-- The original outgoing ticket is a separate field of the old signed census,
available even when the operand is on the target face of that cable. -/
def rawTicket {D cap : ℕ} (words : Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap))
    (peer first : ℕ) (role : Fin 11) :=
  (origin words (peer*cap+first,0)).elim 0 (fun live=>DescentRawCablePanel.DepotRAM.Operand.ticket live.sourceWire role)

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i w M G H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {T : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W T q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
  (ready : A.StateBounds S i) (groups : J↪Fin G) (hosts : V↪Fin H)
set_option quotPrecheck false
local notation "names" => cableNames k (groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding))
local notation "board" => Prepare.signed A native S ready groups hosts
variable (cables : Block k→Fin (2*A.cap)→Bank) (mem : Memory w)
  (prior : ∀ (x : Block k) (s : Fin (2*A.cap)), DescentPackedColony.Reads (cables x s)
      (fun h g => DescentSignedCableCodec.encode (D:=A.degree) (cap:=A.cap)
        (Prepare.signed A native S ready groups hosts x s h g)) M mem)
  (pos : 0<M) (wide : DescentSignedCableCodec.width A.degree A.cap*M≤ w)
  (v : W.graph.Site) (coords : Function.Injective (fun s=>(A.pos s,A.block s)))
local notation "home" => Stage.home A v
local notation "live" => Stage.live A native S ready names home
local notation "tokenAt" => DescentTerminalPointerDigits.token A native S ready names v
local notation "ports" => A.CellPorts (home).1.1 (home).1.2 (home).2
local notation "signed" => Stage.signed A native S ready (home).1 (home).2
local notation "oldWords" => fun s=>chip (cables (home).2 s) mem (hosts (home).1.2) (groups (home).1.1) pos

include prior wide coords in
theorem origin_read (p : ports) (e : Incident W.graph v) (j : Fin (A.grainCount e.val))
    (atPort : Stage.recover A home p=⟨e.val,j⟩) :
    ∃p' : ports, Stage.recover A home p'=⟨e.val,j⟩ ∧
      origin (D:=A.degree) (cap:=A.cap) oldWords (tokenAt ⟨e,j⟩)=some (live p') := by
  let row:=fromBank A groups hosts cables mem pos v
  have seen:=seek_port A native S ready groups hosts cables mem prior pos wide v coords p e j atPort
  cases selected : originIndex row (tokenAt ⟨e,j⟩) with
  | none =>
    exact False.elim (originIndex_present row _ _ _ seen selected)
  | some s =>
    have match_ : row s=some (tokenAt ⟨e,j⟩):=originIndex_hit row _ s selected
    obtain ⟨p',atSlot,recovered⟩:=resolve_slot A native S ready groups hosts cables mem prior pos wide v coords s e j match_
    refine ⟨p',recovered,?_⟩
    change (originIndex row _).bind _=_
    rw [selected,Option.bind_some]
    change wing A.degree A.cap (cables (home).2 s) mem (hosts (home).1.2) (groups (home).1.1) pos=_
    rw [stage_wing A native S ready groups hosts cables mem prior pos wide,←atSlot,Stage.signed_read]

include prior wide coords in
/-- The source census wins whenever it actually has the original endpoint,
in particular for a loop with both signed records at this same site. -/
theorem source_preferred (p : ports) (e : Incident W.graph v) (j : Fin (A.grainCount e.val))
    (atPort : Stage.recover A home p=⟨e.val,j⟩) (source : Stage.signedBit A home p=0) :
    origin (D:=A.degree) (cap:=A.cap) oldWords (tokenAt ⟨e,j⟩)=some (live p) := by
  have real:=seek_port A native S ready groups hosts cables mem prior pos wide v coords p e j atPort
  rw [source] at real
  change (originIndex (fromBank A groups hosts cables mem pos v) _).bind _=_
  rw [originIndex,real,Option.bind_some]
  change wing A.degree A.cap (cables (home).2 (signed p)) mem (hosts (home).1.2) (groups (home).1.1) pos=_
  rw [stage_wing A native S ready groups hosts cables mem prior pos wide,Stage.signed_read]

include prior wide coords in
theorem original_ticket (p : ports) (e : Incident W.graph v) (positive : 0<A.grainCount e.val)
    (peer first : ℕ) (role : Fin 11) (atPort : Stage.recover A home p=⟨e.val,⟨0,positive⟩⟩)
    (header : peer*A.cap+first=(tokenAt ⟨e,⟨0,positive⟩⟩).1) :
    rawTicket (D:=A.degree) (cap:=A.cap) oldWords peer first role=DescentRawCablePanel.DepotRAM.Operand.ticket
      (Stage.outgoing A native S ready ⟨e.val,positive⟩) role := by
  obtain ⟨p',r,read⟩:=origin_read A native S ready groups hosts cables mem prior pos wide v coords p e _ atPort
  have address : (peer*A.cap+first,0)=tokenAt ⟨e,⟨0,positive⟩⟩:=Prod.ext header rfl
  rw [rawTicket,address,read,Option.elim_some]
  change DescentRawCablePanel.DepotRAM.Operand.ticket
    (Stage.outgoing A native S ready ⟨(Stage.recover A home p').1,_⟩) role=_
  simp only [r]

end
end Hierarchy.DescentOperandPriorIncidence

end OAI
