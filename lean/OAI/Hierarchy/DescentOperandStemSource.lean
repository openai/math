import OAI.Hierarchy.DescentOperandPriorTicket
import OAI.Hierarchy.DescentResetStemRoster

namespace OAI
/-! # The retained cable query selects its true signed old face in the physical reset depot -/
namespace Hierarchy.DescentOperandPriorIncidence
open DescentSixParty DescentColonies DescentSharedCableNames DescentTerminalPointerDigits
open DescentTerminalSignedGrainWord DescentStageEdgeReceipt DescentGroupPeerOrder
open DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentOperandStateBanks
open DescentOperandSignedSearch
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
local notation "tokenAt" => DescentTerminalPointerDigits.token A native S ready names v
local notation "ports" => A.CellPorts (home).1.1 (home).1.2 (home).2
local notation "signed" => Stage.signed A native S ready (home).1 (home).2
local notation "cell" s => (chip (cables (home).2 s) mem (hosts (home).1.2) (groups (home).1.1) pos :
  Cell (DescentSignedCableCodec.width A.degree A.cap))

include prior wide coords in
theorem signed_sum (p : ports) (e : Incident W.graph v) (j : Fin (A.grainCount e.val))
    (same : Stage.recover A home p=⟨e.val,j⟩) (wanted : Fin (A.degree*A.cap*A.cap))
    (measured : point A.degree A.cap (Packed.token (some wanted))=some (tokenAt ⟨e,j⟩)) :
    (resultCell A.degree A.cap (Stage.signedBit A home p) (Packed.token (some wanted))
      (fun s=>cell s)).val=(signed p).val+1 := by
  apply result_one
  intro a
  change ((Packed.token (some wanted)).val≠0 ∧ sign A.cap a=Stage.signedBit A home p ∧
    project A.degree A.cap (cell a)=Packed.token (some wanted)) ↔ _
  rw [DescentOperandPriorTicket.signal,measured]
  constructor
  · rintro ⟨_,side,output⟩
    have hit : fromBank A groups hosts cables mem pos v a = some (tokenAt ⟨e,j⟩) := output
    obtain ⟨t,where_,back⟩ := resolve_slot A native S ready groups hosts cables mem prior pos wide v coords a e j hit
    have direction : Stage.signedBit A home t = Stage.signedBit A home p :=
      (sign_real A native S ready v t).symm.trans ((congrArg (sign A.cap) where_).trans side)
    exact where_.symm.trans (congrArg signed (port_unique A v t p (back.trans same.symm) direction))
  · rintro rfl
    exact ⟨Nat.succ_ne_zero _,sign_real A native S ready v p,
      read_port A native S ready groups hosts cables mem prior pos wide v p e j same⟩

include prior wide coords in
theorem prior_key {b : ℕ} (p : ports) (e : Incident W.graph v) (j : Fin (A.grainCount e.val))
    (same : Stage.recover A home p=⟨e.val,j⟩)
    (x : Fin 4→Cell b) (previous : ℕ) (units start peer : ℕ)
    (read : ∀f,(x f).val=(Pointer.cable peer start previous).header f)
    (neighbor : peer<A.degree) (first : start<A.cap) (within : previous/units=j.val)
    (old : peer*A.cap+start=(DescentTerminalPortChart.label A native S ready names v e
      (Nat.zero_lt_of_lt j.isLt)).val) :
    (resultCell A.degree A.cap (Stage.signedBit A home p)
      (DescentOperandPriorTicket.key A.degree A.cap units x) (fun s=>cell s)).val=(signed p).val+1 := by
  have bound := (Stage.grain_room A native S ready e.val)
  have jcap : previous/units<A.cap:=by rw [within];exact j.isLt.trans_le bound
  rw [DescentOperandPriorTicket.cable _ _ _ _ _ _ x read neighbor first jcap]
  apply signed_sum A native S ready groups hosts cables mem prior pos wide v coords p e j same
  simp only [point,Packed.token_back,Option.map_some,Equiv.symm_apply_apply,Option.some.injEq,
    DescentTerminalPointerDigits.token,finProdFinEquiv_apply_val]
  apply Prod.ext _ within
  change _ = (DescentTerminalPortChart.label A native S ready names v e (Nat.zero_lt_of_lt j.isLt)).val
  simpa only [Nat.add_comm,Nat.mul_comm] using old

end
end Hierarchy.DescentOperandPriorIncidence

end OAI
