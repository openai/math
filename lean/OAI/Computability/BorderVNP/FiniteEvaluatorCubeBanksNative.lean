import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanksAllocation
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanksInputs
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleNative

/-! # Preparing every routed field visit with the actual owned-group program

The physical traversal reads its delivered row inputs, makes the exact private
choices of the finite path, publishes the number of genuine vertices and
retains the static deck. Its returned memory and the length-only allocation
supply all lookup hypotheses needed before the field cell evaluator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical Padding.Banks TeamRowSources
open VPVNP.BurstRAM RoutingISA DiagonalTallyPacketEmit

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout} {A : Data n l.d blocks b h K s}
variable {owner : Fin l.d → ℕ} {power base stop : ℕ} {initial final : Memory w}

/-- Any allocated frame word except the owned count is unchanged after the physical traversal. -/
theorem Readback.field (h : Readback (l:=l) A owner power base stop initial final) (j : ℕ) (hj : j<112) (other : j≠46) :
    readings final (l.frame+j)=readings initial (l.frame+j) :=
  congrArg Fin.val (h.sourceWords _ (primary hj) (by omega))

/-- The primary frame becomes the genuine cube lookup frame when the count is published.
The original arbitrary count word is immaterial. -/
theorem Readback.resident (h : Readback (l:=l) A owner power base stop initial final) (f : Frame)
    {pub : Arg → Word w} (ptr : readings pub 0=l.frame)
    (count : f.count=(CubeVisits.teamList A.axis blocks owner l.teamID).length)
    (initialFrame : Frame.resident {f with count:=readings initial (l.frame+46)} (readings pub) (readings initial)) :
    f.resident (readings pub) (readings final) := by
  dsimp only [Frame.resident] at initialFrame ⊢
  rw [ptr] at initialFrame ⊢
  obtain ⟨_,tr,rec,ref,ds,z,o,wd,vt⟩ := initialFrame
  exact ⟨h.count.trans count.symm,(h.field 78 (by decide) (by decide)).trans tr,(h.field 79 (by decide) (by decide)).trans rec,
    (h.field 80 (by decide) (by decide)).trans ref,(h.field 45 (by decide) (by decide)).trans ds,
    (h.field 81 (by decide) (by decide)).trans z,(h.field 82 (by decide) (by decide)).trans o,
    (h.field 83 (by decide) (by decide)).trans wd,(h.field 84 (by decide) (by decide)).trans vt⟩

end FiniteEvaluator.CubeTriple

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally Padding.Banks
open FiniteEvaluator RoutingISA VPVNP.BurstRAM DiagonalTallyPacketEmit
open scoped Classical

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R) (t : Fin (R+1))

/-- Place the paper's finite packet plan in the native length-only routing arena.
The secondary header starts immediately after the supplied geometry allocation. -/
def planArena (L : FieldPacketPlan N F) (R header profile cells cables maxRows stride : ℕ) : CubeArena.Layout :=
  ⟨⟨header,L.alphabet,L.dimension+1,L.blocks,profile,declarationCap L.dimension L.alphabet L.blocks L.bitWidth L.copies L.supply⟩,
    L.dimension,L.bitWidth,L.copies,L.alternatives,L.supply,cells,cables,maxRows,R+1,stride⟩

variable (header profile cells cables maxRows stride : ℕ)
variable (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
variable (B : DiagonalTallyAllocation.Bounds) (l : TypedTaskBuilder.Layout) (sw bw : ℕ)
variable (pub : Arg → Word w)

local notation "arena" => planArena L R header profile cells cables maxRows stride
local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "number" => Fin.val ∘ V.owners R (Sigma.fst (Prod.fst raw))
local notation "packetBase" => CubeHeaderInstall.Inputs.packetBase (CubeArena.Layout.header arena)
local notation "singleBase" => CubeArena.Layout.singleBank arena
local notation "A" => bankData V R raw packetBase singleBase
local notation "scan" => CubeArena.Layout.scanner arena (Fin.val (pub 0)) (Fin.val t) (Fin.val axis) (CubeArena.Layout.rowSelectorBits arena)
local notation "vBase" => CubeArena.Layout.vertexBase arena
local notation "publicBase" => CubeArena.Layout.publicBase arena
local notation "power" => CubeArena.Layout.powerBase arena
local notation "fresh" => CubeArena.Layout.stop arena
local notation "f" => CubeAllocation.frame arena table B l sw bw (List.length (teamPairs V R raw t))
local notation "dst" => DiagonalTallyAllocation.AfterTasks.ids (CubeAllocation.after arena table B l sw bw)
local notation "ptr" => CubeConstants.idBase fresh L.dimension L.bitWidth L.copies L.alternatives L.supply
local notation "Y" => cubeInputs V R raw t packetBase f rfl table fresh dst

/-- Original cube precondition and allocated sources at any genuine readback,
also for an inverse-reconstructed physical history. -/
theorem cube_ready_of_readback (initial mem : Memory w)
    (h : CubeTriple.Readback (l:=scan) A number power vBase publicBase initial mem)
    (boot : CubeDeck.At table f fresh (readings initial))
    (initialFrame : Frame.resident {f with count:=readings initial ((pub 0).val+46)} (readings pub) (readings initial))
    (tableWord : readings initial ((pub 0).val+47)=ptr) (dstWord : readings initial ((pub 0).val+71)=dst)
    (first : (pub 0).val+112 ≤ header) (word : (CubeAllocation.after arena table B l sw bw).packed ≤ 2^w) :
    CubePacket.Prepared Y pub mem ∧ CubePacket.Sources Y (CubeAllocation.tasks arena table B l sw bw) := by
  have ordered := V.numbered_pairs R raw t
  have cap := CubeAllocation.team_count arena axis number t.val
  have length := congrArg List.length ordered
  have bounded : (V.teamPairs R raw t).length ≤ (arena).vertexCap := length.symm ▸ cap
  have place : publicBase ≤ fresh := by
    have ss := (arena).separated
    have pair : (arena).pairBase ≤ (arena).cellBank := Nat.le_add_right ..
    exact ss.2.2.2.1.trans (pair.trans ss.2.2.2.2.2)
  have triple := V.team_triples R raw t packetBase singleBase vBase mem h.triples
  have views x (who : V.owners R raw.1.1 (x.row axis).1=t) := h.views x (congrArg Fin.val who)
  have deck := h.deck table f f fresh place boot
  have frame := h.resident f (pub:=pub) rfl length.symm initialFrame
  have room := CubeAllocation.rooms arena table B l sw bw A rfl bounded first word
  obtain ⟨frameRoom,deckRoom,tripleRoom,bankRoom,descs,refs,endWord⟩ := room
  have regions := CubeAllocation.sources arena table B l sw bw A rfl bounded
  exact ⟨V.cubeInputs_original R raw t packetBase f rfl table fresh dst singleBase deck frame triple views
    ((h.field 47 (by decide) (by decide)).trans tableWord) ((h.field 71 (by decide) (by decide)).trans dstWord)
    frameRoom deckRoom tripleRoom (fun j => bankRoom ((V.teamPairs R raw t).get j).1) descs refs endWord,
    V.cubeInputs_sources R raw t packetBase f rfl table fresh dst _ regions.1 regions.2.1
      (fun j => regions.2.2 ((V.teamPairs R raw t).get j).1)⟩

/-- The native outer loop consumes the original private routed word and returns
with the actual cube inputs ready for evaluation in shared memory. Both the
pre-cell lookup precondition and all regions protected during the cell stage
come from this run and the jointly allocated address space. -/
theorem owned_cube_ready (mac : TeamOpcode.Macros w 8) (r : Bank w) (initial : Memory w)
    (actual claimed : ℕ) (rows : Sym2 (Fin L.alphabet) → Fin (L.dimension+1) → ℕ)
    (setup : TeamRows.PhysicalSetup (l:=scan) A number power vBase publicBase actual claimed rows pub initial)
    (boot : CubeDeck.At table f fresh (readings initial))
    (initialFrame : Frame.resident {f with count:=readings initial ((pub 0).val+46)} (readings pub) (readings initial))
    (tableWord : readings initial ((pub 0).val+47)=ptr) (dstWord : readings initial ((pub 0).val+71)=dst)
    (first : (pub 0).val+112 ≤ header) (word : (CubeAllocation.after arena table B l sw bw).packed ≤ 2^w) :
    let tape := (((Scatter.nativeWordsEquiv L.bitWidth L.supply raw.1.1 axis (V.owners R raw.1.1)) raw.1.2).2 t).val
    Owned.TraceRun pub mac (TeamRows.ownedGroups L.dimension L.bitWidth L.copies L.alternatives L.supply)
      r initial tape (4+(TeamRows.ticks scan (TeamRows.wordOwner number)
        (TeamRows.physicalCostAt scan L.blocks L.bitWidth L.copies L.alternatives L.supply axis)+11))
      (fun _ mem => CubePacket.Prepared Y pub mem ∧ CubePacket.Sources Y (CubeAllocation.tasks arena table B l sw bw)) := by
  intro tape
  have run := CubeTriple.native_run setup mac r
  have script := V.team_tape R raw t scan rfl rfl packetBase singleBase
  rw [show tape = _ from script]
  apply run.mono le_rfl
  intro _ mem h
  exact V.cube_ready_of_readback R raw t header profile cells cables maxRows stride table B l sw bw pub
    initial mem h boot initialFrame tableWord dstWord first word

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
