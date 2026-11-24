import OAI.Computability.VPVNP.PairShrinkHookBudget
import OAI.Computability.VPVNP.PairShrinkNodeRates
import OAI.Computability.VPVNP.PairShrinkPrologueBudget

/-!
# Ordinal cost of a selected shrinking hook

The selected child and hidden directories bound the two scans before the
resident maps. A map estimate on the scratch reached by these scans bounds
the whole accepted job, including the dispatch from its ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkNodeCost

open BurstRAM BurstRAM.PrivateRAM DFS Compression Compression.ShrinkMotif CompressorRecords
open CompressorRecords.ShrinkSlots NodeArguments NodeArguments.ChildScan LocalHistory NetworkKernel
open ShrinkRole ShrinkHiddenGuess ShrinkVertexImage VertexImage

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)

/-- Instruction length of the installed hidden header at each stage. -/
noncomputable def selectedHeaderLength (i : Fin S.steps) : ℕ :=
  (RegisterSetup.lines (Header.recipe B.shrink.selectorBits (hiddenStride i))).length

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
    {g w endAddr : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (sel : X.ShrinkSelection B.shrink)
    (v : (X.Base × BitWord (packingTagBits (2 ^ S.degreeExponent i.castSucc))) × BitWord g)
    (desc : Word w → ChildArguments.Descriptor w X) (node : Word w)
    (order : (desc node).sites = List.ofFn fun j =>
      ((((shrinkPassReaders B f hf i rfl X).order sel).children v).entries j).val)

variable (placeholder : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
      (internalLabel (ShrinkHiddenRows.widths X B.shrink sel) (selectedLayout X B.shrink sel)) v)
    (A : Arena) (inc : IncidenceDirectory w) (m : Memory w) (older : ℕ) (arg : Args w)
    (maps : List (Child X) → List Row → List (ResidentMapLoop.Exact.Action w endAddr))
    (pub : Fin 11 → Word w) (levels old : ℕ) (head owner : Word w)

/-- The physical hidden row directory at this site of the chosen layout. -/
noncomputable abbrev selectedSeed :=
  ShrinkHiddenSlots.rows X (selectedLayout X B.shrink sel) (ShrinkHiddenRows.widths X B.shrink sel)
    v placeholder

variable (saved : Scratch w endAddr) (bits tail : List Bool) (body : VisitPath w endAddr)
    (mapC n : ℕ) (room : RateRoom S (selectedHeaderLength B) mapC (prologueCoefficient B) n)
    (level : levels - (old + 1) ≤ (S.steps + 1) * (n.log2 + 1)) (wire : X.maxWireWidth ≤ n)
    (mapRates : ∀ (child : Outcome w endAddr (List (Child X))) (mid : List Bool)
      (hidden : Outcome w endAddr (List Row)) (mapOut : Scratch w endAddr) (trace : List (Event w)),
      ChildArguments.reader A inc m older B.recordLimit desc node
        ((selectedChildSetup pub m levels old S.steps i.val (oldExponent i)).updated node saved)
        bits = some (child, mid) →
      hiddenReader arg m (selectedSeed B i X sel v placeholder) node
        ((physicalHiddenSetup B.shrink.selectorBits (hiddenStride i) head.val m).updated node
          child.updated) mid = some (hidden, tail) →
      ResidentMapLoop.Exact.scan node (maps child.value hidden.value)
        ((mapStartSetup m head owner).updated node hidden.updated) = some (trace, mapOut) →
      trace.length ≤ mapC * (X.maxWireWidth + 1) ∧ countProbes trace ≤ mapC)
    (hit : (hook (visitReader A inc m older B.recordLimit desc (fun _ => arg)
      (fun _ => selectedSeed B i X sel v placeholder) maps
      (selectedChildSetup pub m levels old S.steps i.val (oldExponent i))
      (fun _ => physicalHiddenSetup B.shrink.selectorBits (hiddenStride i) head.val m)
      (fun _ _ => mapStartSetup m head owner))).read node saved bits = some (body, tail))

include order room level wire mapRates hit

/-- The successful hook leaves room for the dispatcher in both resource bounds.
The map estimate applies to the exact scratch produced by its two parsers. -/
theorem selected_hook_rates :
    countProbes body.trace + 1 ≤ probeRate S mapC (prologueCoefficient B) * (n.log2 + 1) ∧
      body.trace.length + 9 ≤ n ^ 43 := by
  obtain ⟨child, mid, hidden, mapOut, trace, childRead, hiddenRead, scan, ticks, probes⟩ :=
    hook_counts_reached A inc m older B.recordLimit desc arg (selectedSeed B i X sel v placeholder)
      maps pub levels old S.steps i.val
      B.shrink.selectorBits (hiddenStride i) head owner node saved bits tail body hit
  obtain ⟨mapTime, mapReads⟩ := mapRates child mid hidden mapOut trace childRead hiddenRead scan
  obtain ⟨children, demand, fields, payload⟩ :=
    selected_prologue_bounds B f hf i X sel v (desc node) order placeholder
  exact job_rates S i (selectedHeaderLength B) mapC (prologueCoefficient B) n room level wire
    children demand fields payload mapTime mapReads ticks probes

/-- The actual dispatched job at this ordinal satisfies the common traversal allowance. -/
theorem selected_hook_cost (offset : Word w) :
    ordinalJobCost n 1 (probeRate S mapC (prologueCoefficient B))
      (dispatchJob m offset node saved body) := by
  have bounds := selected_hook_rates B f hf i X sel v desc node order placeholder A inc m older
    arg maps pub levels old head owner saved bits tail body mapC n room level wire mapRates hit
  exact dispatched_ordinal_cost m offset node saved body bounds.1 bounds.2

end PairSimulation.ShrinkNodeCost

end VPVNP
end Computability
end OAI
