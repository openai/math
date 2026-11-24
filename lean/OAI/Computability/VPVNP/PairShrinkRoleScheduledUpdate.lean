import OAI.Computability.VPVNP.PairShrinkRoleVisitEffect
import OAI.Computability.VPVNP.PairShrinkRoleRowUpdate
import OAI.Computability.VPVNP.PairShrinkRoleFieldFrame
import OAI.Computability.VPVNP.PairShrinkVertexFrameScan

/-!
# The cell update at a shrinking vertex of the scheduled tree

The exact field prefix fixes the input memory of the resident map scan. Its
exterior cells preserve both the common vertex frame and the preceding-level
arguments. The private histogram starts at its incoming value, so the
increment of that scan is the increment of the whole visit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression Compression.ShrinkMotif CompressorRecords NetworkKernel
open LocalHistory NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess LeafSourceLoad
open private layout supplyWidth from OAI.Computability.VPVNP.PairShrinkRoleMapWitness
open scoped Fin.CommRing

variable {w n t g : ℕ} {K R : Type*} [_root_.Field K] [CommRing R] {S : BlockSchedule K}
  (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
  (Z : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
  (sel : Z.ShrinkSelection B.shrink)
  (v : (Z.Base × BitWord (packingTagBits (2 ^ S.degreeExponent i.castSucc))) × BitWord g)

open private term parser childOrder from OAI.Computability.VPVNP.PairShrinkRoleVisitEffect
local notation "Tr" => term B f hf i Z sel
local notation "rdr" => parser B f hf i Z sel
local notation "ord" => childOrder B f hf i Z sel v
local notation "rowsAt" => ShrinkHiddenSlots.rows Z (layout B i Z sel) (supplyWidth B i Z sel) v

variable (old : Placed (term B f hf i Z sel).place Z.network.Half v)
  (new : (term B f hf i Z sel).output.Half v)
  (k : ((parser B f hf i Z sel).witness v old new).Choice)
  (placeholder : Placed (Z.packingData.shrinkInternalOwner (layout B i Z sel))
    (internalLabel (supplyWidth B i Z sel) (layout B i Z sel)) v)
  (regions : LeafArena.Regions) (inc : IncidenceDirectory w) (m : Memory w) (older cap : ℕ)
  (desc : Word w → ChildArguments.Descriptor w Z) (arg : Args w)
  (maps : List (Child Z) → List Row → List (ResidentMapLoop.Exact.Action w n))
  (cs hs ms : Setup w n) (node : Word w) (saved : Scratch w n)

local notation "es" => rowsAt (Sigma.fst k)
local notation "addr" => childNode Z older cap
local notation "packetsAt" => TreeDecode.children rdr
  (fun u b => Packet.mk (addr u) (packed Z u b)) v old
local notation "xs" => children (t := Tr) Z v ord old
local notation "heap" => ShrinkCallABI.hiddenBase regions n
local notation "initial" => scratch n (storeRows heap arg.slotStride es
  (storePackets regions.arguments packetsAt (rawScratch saved)))
local notation "visit" => visitReader regions.arguments inc m older cap desc (fun _ => arg)
  (fun _ => rowsAt placeholder) maps cs (fun _ => hs) (fun _ _ => ms)

set_option maxHeartbeats 2000000 in
-- The physical field order and the tree order are the two presentations of this dependent fiber.
/-- Starting on any prepared scratch, a successful read of the given term witness
satisfies the selected row's update contract. Only the resident scan's exterior
and histogram identities are needed after the two native field scans. -/
theorem scheduledRowUpdate (labels : B.Entry ≃ Fin t) (data : Fin 10 → Word w)
    (offset : Word w) (vals : Static 34 → Word w)
    (frame : TreeDecode.VertexFrameData regions data offset vals saved)
    (order : (desc node).sites = List.ofFn fun j => ((ord).entries j).val)
    (childSetup : ∀ s, cs.updated node s = s) (hiddenSetup : ∀ s, hs.updated node s = s)
    (mapSetup : ∀ s, ms.updated node s = s) (base : arg.scratchBase = heap)
    (before : n < regions.histBase) (labelFit : t ≤ regions.histWords)
    (heapFit : heap ≤ 2 ^ w) (rowFit : ∀ e ∈ es, heap + e.1 * arg.slotStride + e.2.length ≤ 2 ^ w)
    (fits : ∀ q ∈ packetsAt, q.Fits regions.arguments w n)
    (nodes : ∀ q ∈ packetsAt, q.node < regions.nodes)
    (above : ∀ q ∈ packetsAt, n < regions.arguments.base q.node)
    (exterior : ∀ events final, ResidentMapLoop.Exact.scan node (maps xs es) initial =
        some (events, final) → ∀ q : Word w, q.val < heap →
      (q.val < regions.histBase ∨ regions.histBase + t ≤ q.val) →
      rawScratch final q = rawScratch initial q)
    (increment : ∀ events final, ResidentMapLoop.Exact.scan node (maps xs es) initial =
        some (events, final) → ∀ l, let a : Word w := (regions.histBase + (labels l).val : ℕ)
      rawScratch final a = rawScratch initial a +
        (((rdr).witness v old new).exponents k l : Word w))
    (tail : List Bool) (job : VisitPath w n)
    (hit : (hook visit).read node saved ((rdr).nodeBits v old new k ++ tail) = some (job, tail)) :
    RowUpdate regions labels data offset vals saved job packetsAt
      (((rdr).witness v old new).exponents k) := by
  have rep : scratch n (rawScratch saved) = saved := by
    funext q
    simp only [DFS.scratch, rawScratch, dite_eq_left q.prop]
  have packetEq : (rdr).childPackets addr v old = packetsAt := by
    have h (u z) : (rdr).halfBits u z = packed Z u z := (packed_eq_encode Z u z).symm
    simp only [TermParsers.childPackets, TreeDecode.children, h]
  have effect := scheduledVisitEffect B f hf i Z sel v old new k placeholder regions.arguments inc
    m older cap desc arg maps cs hs ms node (rawScratch saved) tail order
    childSetup hiddenSetup mapSetup
  dsimp only at effect
  rw [rep, hit, Option.map_some, base, packetEq] at effect
  obtain ⟨⟨events, final⟩, run, equal⟩ := Option.map_eq_some_iff.mp effect.symm
  have finalEq : final = job.update saved := (Prod.mk.inj equal).1
  have exterior' := exterior events final run
  have original : TreeDecode.VertexFrameData regions data offset vals
      (scratch n (rawScratch saved)) := by rwa [rep]
  have fieldFrame := original.after_shrink_fields
    (before.le.trans (Nat.le_add_right ..)) heapFit rowFit fits nodes above
  refine ⟨?_, finalEq ▸ fieldFrame.after_map before labelFit heapFit exterior', ?_, ?_⟩
  · obtain ⟨⟨out, rest⟩, _, eqn⟩ := Option.map_eq_some_iff.mp hit
    cases eqn
    exact fun _ h => h
  · intro a _ ha
    have low := (Nat.mod_le a (2 ^ w)).trans_lt ha
    have below : regions.histBase ≤ regions.cacheBase :=
      (Nat.le_add_right ..).trans regions.hist_before
    have endCache : regions.cacheBase + 38 ≤ heap := Nat.le_add_right ..
    have hi : (a : Word w).val < heap :=
      low.trans_le (below.trans ((Nat.le_add_right _ 38).trans endCache))
    have atWord := exterior' (a : Word w) hi (Or.inl low)
    have keep := fields_arguments (priv := rawScratch saved) (qs := packetsAt) rowFit a ha
    rw [rep] at keep
    exact finalEq ▸ atWord.trans keep
  · intro l
    dsimp only
    rw [← finalEq, increment events final run l]
    exact congrArg (· + _) ((fields_histCell (labels l).val ((labels l).isLt.trans_le labelFit)
      heapFit rowFit fits nodes).trans (congrArg (fun s => rawScratch s _) rep))

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
