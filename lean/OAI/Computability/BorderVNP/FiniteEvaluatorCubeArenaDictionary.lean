import OAI.Computability.BorderVNP.FiniteEvaluatorCubeRawDictionary
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanksNative
import OAI.Computability.BorderVNP.CubeTeamOwnedReplaySetup

/-! # The native cube lookup on every history in a physical field arena

Actual decoder words and received strict-row buffers instantiate the team
setup. The same fixed field deck serves the whole private fiber. Each native
return carries the prepared lookup at its actual memory endpoint, including
the source separation needed for the intervening private cell routines.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.Tally
open BorderVNP.Cube.TeamRows FiniteEvaluator RoutingISA VPVNP.BurstRAM DiagonalTallyPacketEmit
open scoped BigOperators Classical

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R)
variable (header profile cells cables maxRows stride : ℕ)
variable (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
variable (B : DiagonalTallyAllocation.Bounds) (task : Fin (R+1) → TypedTaskBuilder.Layout) (sw bw : ℕ)
variable (pub : Fin (R+1) → Arg → Word w) (mac : Fin (R+1) → TeamOpcode.Macros w 8)
variable (regs : Fin (R+1) → Bank w) (initial : Fin (R+1) → Memory w)

local notation "arena" => planArena L R header profile cells cables maxRows stride
local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "number" => Fin.val ∘ V.owners R (Sigma.fst (Prod.fst raw))
local notation "decl" => Assignment.Routed.trueDeclaration L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "enc" => nativeWordsEquiv L.bitWidth L.supply (Sigma.fst (Prod.fst raw)) axis (V.owners R (Sigma.fst (Prod.fst raw)))
local notation "packet" => CubeHeaderInstall.Inputs.packetBase (CubeArena.Layout.header arena)
local notation "single" => CubeArena.Layout.singleBank arena
local notation "vbase" => CubeArena.Layout.vertexBase arena
local notation "stop" => CubeArena.Layout.publicBase arena
local notation "power" => CubeArena.Layout.powerBase arena
local notation "fresh" => CubeArena.Layout.stop arena
local notation "ptr" => CubeConstants.idBase fresh L.dimension L.bitWidth L.copies L.alternatives L.supply
local notation "srcRows" => sharedWords decl (Assignment.Routed.physicalShared (V.owners R) (Prod.fst raw))

/-- The native cube lookup inputs as allocated in the true team frame,
including its published visit count and actual selected-word destination. -/
noncomputable def allocatedInputs (t : Fin (R+1)) :=
  let f := CubeAllocation.frame arena table B (task t) sw bw (V.teamPairs R raw t).length
  let dst := (CubeAllocation.after arena table B (task t) sw bw).ids
  V.cubeInputs R raw t packet f rfl table fresh dst

/-- Budget of the physically scheduled group traversal at its actual team frame. -/
noncomputable def ownedTicks (t : Fin (R+1)) :=
  let l := (arena).scanner (readings (pub t) 0) t.val (axis).val (arena).rowSelectorBits
  4+(ticks l (wordOwner number) (physicalCostAt l L.blocks L.bitWidth L.copies L.alternatives L.supply axis)+11)

/-- All returning group histories, in both directions, produce the actual field
lookup inputs. Only real scanner words, received buffers, boot table and numeric
allocation bounds are required. -/
theorem arena_dictionary
    (room : ∀ t, (arena).ReplayRoom w (readings (pub t) 0))
    (scanner : ∀ t, (arena).ScannerWords (readings (pub t) 0) t.val (axis).val number (readings (pub t)) (readings (initial t)) (Prod.snd decl))
    (received : ∀ t, (arena).RawViews (readings (pub t) 0) t.val (axis).val number srcRows (initial t))
    (boot : ∀ t, let f := CubeAllocation.frame arena table B (task t) sw bw (V.teamPairs R raw t).length
      CubeDeck.At table f fresh (readings (initial t)))
    (frameWords : ∀ t, let f := CubeAllocation.frame arena table B (task t) sw bw (V.teamPairs R raw t).length
      Frame.resident {f with count:=readings (initial t) ((pub t 0).val+46)} (readings (pub t)) (readings (initial t)))
    (tableWord : ∀ t, readings (initial t) ((pub t 0).val+47)=ptr)
    (dstWord : ∀ t, readings (initial t) ((pub t 0).val+71)=(CubeAllocation.after arena table B (task t) sw bw).ids)
    (word : ∀ t, (CubeAllocation.after arena table B (task t) sw bw).packed ≤ 2^w)
    (fixed : ∀ p, L.table p=table) :
    ∃ E : CubeTriple.Fiber raw.1.2 ≃ CubeTriple.Histories pub mac regs initial L.dimension L.bitWidth L.copies L.alternatives L.supply,
      ∀ f, let next := V.withPrivate R raw f
        let Y := V.allocatedInputs R next header profile cells cables maxRows stride table B task sw bw
        (∀ t, let out := E f t
          DiagonalResidueRAM.TraceOK out.val.1 (((enc f.val).2 t).val) out.val.1.length ∧
            traceCost out.val.1 ≤ V.ownedTicks R raw header profile cells cables maxRows stride pub t ∧
            CubePacket.Prepared (Y t) (pub t) out.val.2.2 ∧
            CubePacket.Sources (Y t) (CubeAllocation.tasks arena table B (task t) sw bw)) ∧
          (∏ t, ∏ i, (Y t).scalar i) = cubeTermWeight L.table (fun _ _ => 1) (V.read R next).2.2 := by
  let scan (t : Fin (R+1)) := (arena).scanner (readings (pub t) 0) t.val (axis).val (arena).rowSelectorBits
  let A := V.bankData R raw packet single
  let actual := (arena).header.header+13
  let claim := (arena).header.header+13+(arena).header.entries
  have setup (t : Fin (R+1)) : PhysicalSetup (l := scan t) A number power vbase stop actual claim (decl).2 (pub t) (initial t) :=
    (arena).replaySetup (V.owners R) Fin.valEmbedding raw.1 t (pub t) (initial t) decl srcRows rfl rfl
      (room t) (scanner t) (received t)
  obtain ⟨E,cert⟩ := V.native_owned_dictionary R raw scan (fun _ => packet) (fun _ => single) (fun _ => power)
    (fun _ => vbase) (fun _ => stop) (fun _ => actual) (fun _ => claim) (decl).2 pub mac regs initial setup
  refine ⟨E,fun f => ?_⟩
  let next := V.withPrivate R raw f
  obtain ⟨vis,product⟩ := cert f
  constructor
  · intro t
    obtain ⟨bits,cost,h,_⟩ := vis t
    have ready := V.cube_ready_of_readback R next t header profile cells cables maxRows stride table B (task t) sw bw
      (pub t) (initial t) (E f t).val.2.2 h (boot t) (frameWords t) (tableWord t) (dstWord t) (room t).primary (word t)
    exact ⟨bits,cost,ready⟩
  · refine (Finset.prod_congr rfl fun t _ => ?_).trans product
    exact V.cubeInputs_product R next t packet _ rfl table fresh _ fixed

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
