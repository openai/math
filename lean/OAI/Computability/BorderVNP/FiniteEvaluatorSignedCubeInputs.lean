import OAI.Computability.BorderVNP.FiniteEvaluatorSignedCubeAllocation
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeArenaDictionary

/-! # True signed-arena finite field lookup after the reconstructed physical team return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally FiniteEvaluator RoutingISA
open VPVNP.BurstRAM DiagonalTallyPacketEmit
open scoped Classical

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R) (u : Fin (R+1))
variable (header profile cells cables maxRows stride : ℕ)
variable (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
variable (params : SignedTaskArena.Parameters)

local notation "ar" => planArena L R header profile cells cables maxRows stride
local notation "packet" => CubeHeaderInstall.Inputs.packetBase (CubeArena.Layout.header ar)
local notation "single" => CubeArena.Layout.singleBank ar
local notation "fresh" => CubeArena.Layout.stop ar
local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "number" => Fin.val ∘ V.owners R (Sigma.fst (Prod.fst raw))

/-- The field plan uses the same signed task layout, fixed scalar ID table and sparse
fragment reservation as the machine's length-only extension. -/
noncomputable def signedPlanArena (L : FieldPacketPlan N F) (R header profile cells cables maxRows stride : ℕ)
    (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
    (p : SignedTaskArena.Parameters) : SignedTaskArena.Layout :=
  ⟨planArena L R header profile cells cables maxRows stride,CubeDeck.entry table,p⟩

local notation "signed" => signedPlanArena L R header profile cells cables maxRows stride table params
local notation "f" => SignedTaskArena.Layout.lookupFrame signed (List.length (teamPairs V R raw u))
local notation "dst" => DiagonalTallyAllocation.AfterTasks.ids (SignedTaskArena.Layout.after signed)

/-- The exact lookup whose descriptor and reference outputs follow all fragment,
report and private call reservations in the signed evaluator. -/
noncomputable def signedInputs :=
  V.cubeInputs R raw u packet f rfl table fresh dst

local notation "Y" => signedInputs V R raw u header profile cells cables maxRows stride table params

set_option maxHeartbeats 1600000 in
/-- For an allocated signed layout every original lookup operand is in the
primary frame, the earlier packet/triple area, or the actual fixed field deck. -/
theorem signedRead_location (pub : Arg → Word w) {addr : ℕ} (read : CubePacket.ReadAt Y pub addr) :
    (∃ j ∈ CubePacket.frameWords, addr=(pub 0).val+j) ∨ (packet ≤ addr ∧ addr<(ar).cellBank) ∨
      (fresh ≤ addr ∧ addr<CubeConstants.arenaEnd fresh (CubeDeck.entry table)) := by
  let A := V.bankData R raw packet single
  have bounded : (V.teamPairs R raw u).length ≤ (ar).vertexCap :=
    (congrArg List.length (V.numbered_pairs R raw u)).symm ▸ CubeAllocation.team_count ar axis number u.val
  exact CubeAllocation.read_location_frame ar table f dst rfl A rfl bounded (V.teamVisit R raw packet u)
    (fun i => ⟨((V.teamPairs R raw u).get i).1,rfl⟩) D pub read

set_option maxHeartbeats 1600000 in
/-- Source readiness and all generated lookup addresses for the signed task windows,
including the physical fragment area preceding those windows. -/
theorem signed_cube_of_readback (pub : Arg → Word w) (initial mem : Memory w) (offsets control : ℕ)
    (read : CubeTriple.Readback (l := (ar).scanner (pub 0).val u.val (axis).val (ar).rowSelectorBits)
      (V.bankData R raw packet single) number (ar).powerBase (ar).vertexBase (ar).publicBase initial mem)
    (boot : CubeDeck.At table f fresh (readings initial))
    (frameWords : Frame.resident {f with count := readings initial ((pub 0).val+46)} (readings pub) (readings initial))
    (tableWord : readings initial ((pub 0).val+47) = CubeConstants.idBase fresh L.dimension L.bitWidth L.copies L.alternatives L.supply)
    (dstWord : readings initial ((pub 0).val+71) = dst)
    (primary : (pub 0).val+112 ≤ header) (fit : (signed).after.packed ≤ 2^w)
    (countRoom : (V.teamPairs R raw u).length ≤ params.report.vertices)
    (digits : argumentWidth L.dimension L.bitWidth L.copies L.alternatives L.supply ≤ params.report.cubeWidth) :
    CubePacket.Prepared Y pub mem ∧ CubePacket.Sources Y ((signed).tasks u.val (pub 0).val offsets control) := by
  let A := V.bankData R raw packet single
  have length := congrArg List.length (V.numbered_pairs R raw u)
  have bounded : (V.teamPairs R raw u).length ≤ (ar).vertexCap := length.symm ▸ CubeAllocation.team_count ar axis number u.val
  have place : (ar).publicBase ≤ fresh := (ar).separated.2.2.2.1.trans ((Nat.le_add_right ..).trans (ar).separated.2.2.2.2.2)
  have triple := V.team_triples R raw u packet single (ar).vertexBase mem read.triples
  have views x (who : V.owners R raw.1.1 (x.row axis).1=u) := read.views x (congrArg Fin.val who)
  have deck := read.deck table f f fresh place boot
  have frame := read.resident f (pub := pub) rfl length.symm frameWords
  obtain ⟨frameRoom,deckRoom,tripleRoom,banks,rows,refs,word⟩ :=
    (signed).lookup_rooms A rfl bounded countRoom digits primary fit
  have ranges := (signed).lookup_sources u.val (pub 0).val offsets control A rfl bounded
  exact ⟨V.cubeInputs_original R raw u packet f rfl table fresh dst single deck frame triple views
    ((read.field 47 (by decide) (by decide)).trans tableWord) ((read.field 71 (by decide) (by decide)).trans dstWord)
    frameRoom deckRoom tripleRoom (fun j => banks ((V.teamPairs R raw u).get j).1) rows refs word,
    V.cubeInputs_sources R raw u packet f rfl table fresh dst _ ranges.1 ranges.2.1
      (fun j => ranges.2.2 ((V.teamPairs R raw u).get j).1)⟩

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
