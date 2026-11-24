import OAI.Computability.VPVNP.PairShrinkNodeClock
import OAI.Computability.VPVNP.PairShrinkRoleSelectedChildren
import OAI.Computability.VPVNP.PairShrinkRolePhysicalHidden
import OAI.Computability.VPVNP.PairShrinkRoleMapStart

/-! # Native costs at the entry of a physical shrinking hook

The successful hook determines the actual stored child arguments, hidden
bits and resident scan on the outgoing private scratch. The three setup
traces are the linked level selector, cached hidden header, and map reload.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkNodeCost

open BurstRAM PrivateRAM DFS Compression CompressorRecords NodeArguments NodeArguments.ChildScan
open ShrinkRole ShrinkHiddenGuess
open scoped Fin.CommRing

variable {w endAddr a g : ℕ} {X : State a g}

variable (A : Arena) (T : IncidenceDirectory w) (m : Memory w) (older cap : ℕ)
    (desc : Word w → ChildArguments.Descriptor w X) (args : Args w) (seed : List Row)
    (maps : List (Child X) → List Row → List (ResidentMapLoop.Exact.Action w endAddr))
    (pub : Fin 11 → Word w) (levels old stages stage selectors stride : ℕ) (head owner : Word w)
    (node : Word w) (saved : Scratch w endAddr) (bs tail : List Bool) (job : VisitPath w endAddr)
    (hit : (hook (visitReader A T m older cap desc (fun _ => args) (fun _ => seed) maps
      (selectedChildSetup pub m levels old stages stage a)
      (fun _ => physicalHiddenSetup selectors stride head.val m)
      (fun _ _ => ShrinkVertexImage.mapStartSetup m head owner))).read node saved bs =
        some (job, tail))

include hit

set_option maxHeartbeats 600000 in
-- The setup equations unfold the composed selector and physical header traces.
theorem hook_counts :
    ∃ xs hs mapIn mapOut ms, xs.map Child.site = (desc node).sites ∧ hs.length = seed.length ∧
      (stream hs).length = (stream seed).length ∧
      ResidentMapLoop.Exact.scan node (maps xs hs) mapIn = some (ms, mapOut) ∧
      job.trace.length = 88 + 6 * (levels - (old + 1)) + stages + 2 * stage + 2 ^ a +
        VertexLevel.hiddenCount +
        (RegisterSetup.lines (Header.recipe selectors stride)).length +
        (10 + 15 * 2 ^ a) * (desc node).sites.length +
        6 * ChildArguments.demand X (desc node).sites + 25 * seed.length +
        6 * (stream seed).length + ms.length ∧
      countProbes job.trace = 25 + (levels - (old + 1)) +
        (1 + 3 * 2 ^ a) * (desc node).sites.length + 3 * seed.length + countProbes ms := by
  obtain ⟨⟨out, rest⟩, found, hj⟩ := Option.map_eq_some_iff.mp hit
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hj
  exact native_cost A T m older cap desc (fun _ => args) (fun _ => seed) maps pub (old + 1)
    (levels - (old + 1)) stages stage selectors stride head.val owner _ _ _ node saved bs rest out
    rfl (fun _ _ => rfl) (fun _ _ _ => by rw [Fin.cast_val_eq_self]; rfl) found

set_option maxHeartbeats 600000 in
-- The setup equations unfold the composed selector and physical header traces.
/-- The map trace in the hook counts starts at the scratch reached by the
successful child and hidden reads, with the hidden read returning the hook's suffix. -/
theorem hook_counts_reached :
    ∃ child mid hidden mapOut ms,
      ChildArguments.reader A T m older cap desc node
        ((selectedChildSetup pub m levels old stages stage a).updated node saved) bs =
          some (child, mid) ∧
      hiddenReader args m seed node
        ((physicalHiddenSetup selectors stride head.val m).updated node child.updated) mid =
          some (hidden, tail) ∧
      ResidentMapLoop.Exact.scan node (maps child.value hidden.value)
        ((ShrinkVertexImage.mapStartSetup m head owner).updated node hidden.updated) =
          some (ms, mapOut) ∧
      job.trace.length = 88 + 6 * (levels - (old + 1)) + stages + 2 * stage + 2 ^ a +
        VertexLevel.hiddenCount +
        (RegisterSetup.lines (Header.recipe selectors stride)).length +
        (10 + 15 * 2 ^ a) * (desc node).sites.length +
        6 * ChildArguments.demand X (desc node).sites + 25 * seed.length +
        6 * (stream seed).length + ms.length ∧
      countProbes job.trace = 25 + (levels - (old + 1)) +
        (1 + 3 * 2 ^ a) * (desc node).sites.length + 3 * seed.length + countProbes ms := by
  obtain ⟨⟨out, rest⟩, found, hj⟩ := Option.map_eq_some_iff.mp hit
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hj
  obtain ⟨child, mid, hidden, mapOut, ms, readChild, readHidden, scan, _, _, _, ticks, probes⟩ :=
    native_cost_reached A T m older cap desc (fun _ => args) (fun _ => seed) maps pub (old + 1)
      (levels - (old + 1)) stages stage selectors stride head.val owner _ _ _ node saved bs rest out
      rfl (fun _ _ => rfl) (fun _ _ _ => by rw [Fin.cast_val_eq_self]; rfl) found
  exact ⟨child, mid, hidden, mapOut, ms, readChild, readHidden, scan, ticks, probes⟩

end PairSimulation.ShrinkNodeCost

end VPVNP
end Computability
end OAI
