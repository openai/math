import OAI.Computability.VPVNP.PairTerminalGatherGeometry
import OAI.Computability.VPVNP.PairSimulationTerminalRootGather

/-!
# Native terminal gathers in the selected wire geometry

Each vertex reads the final shared bits into its actual root argument before
DFS. The same bit is read at both endpoints. The directory lookups add five
probes per outgoing slot when summed over the whole graph.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalGatherNative

open BurstRAM BurstRAM.PrivateRAM Compression LocalHistory TerminalRootGather TerminalGatherGeometry
open scoped Fin.CommRing

variable {a g w p r : ℕ}

/-- Number of bits in a final site's argument packet, summed over all outgoing and incoming
slots. -/
def argumentSize (X : State a g) (v : X.network.Site) := ∑ d : Bool, ∑ j, X.halfWidth v d j

variable {M : Machine w p r 11} {pc : PC → Fin p} {reg : Reg ↪ Fin r} {done : Fin p}
variable {L : Layout} {X : State a g} {v : X.network.Site}

/-- The actual linked table fills the root store and passes control and the
unconsumed branch stream to its continuation. -/
theorem run (hl : Linked M pc reg done) (mem : Memory w) (num : Numbering X L v)
    (rows : Rows X L mem) (fit : L.Fits mem) (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (bits : ∀ i, mem (L.wires+i.val) = PrivateFields.bitValue w (f i))
    (c : Config w p r) (hc : c.pc = pc (.boot 0)) (saved : Saved L reg c)
    (hn : M.publicData 6 = (L.n : Word w))
    (stride : c.privateMem (c.privateMem (L.n : Word w)+7) = (L.stride : Word w)) :
    ∃ out es, out.pc = done ∧ Frame reg c out ∧
      out.privateMem = PrivateFields.storeBits L.dest (NodeArguments.packed X v (half X f v)) c.privateMem ∧
      Cost es (15+21*2^a+5*argumentSize X v) (5*2^a+argumentSize X v) ∧ Prefix M mem c es out := by
  obtain ⟨out,es,ret,frame,priv,cost,exec⟩ := TerminalRootGather.run hl L mem fit c hc saved hn stride
  refine ⟨out,es,ret,frame,priv.trans (placed_packet num rows f bits fit _),?_,exec⟩
  simpa only [num.degree, packet_eq num rows f bits, List.length_map,
    NodeArguments.packed_length, argumentSize] using cost

/-- Run the gather in the memory actually written by the shared bit scan. -/
theorem run_after_reports (hl : Linked M pc reg done) (initial : Memory w) (num : Numbering X L v)
    (rows : Rows X L initial) (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (countFit : TerminalPrefix.arcCount X < 2 ^ w)
    (headsFit : ∀ head ∈ [L.incomingHead,L.widthHead,L.prefixHead],
      head + TerminalPrefix.arcCount X ≤ 2 ^ w)
    (apart : ∀ head ∈ [L.incomingHead,L.widthHead,L.prefixHead],
      head + TerminalPrefix.arcCount X ≤ L.wires ∨ L.wires + X.totalWidth ≤ head)
    (sharedFit : L.wires + X.totalWidth < 2 ^ w) (privateFit : L.dest + argumentSize X v < 2 ^ w)
    (c : Config w p r) (hc : c.pc = pc (.boot 0)) (saved : Saved L reg c)
    (hn : M.publicData 6 = (L.n : Word w))
    (stride : c.privateMem (c.privateMem (L.n : Word w)+7) = (L.stride : Word w)) :
    let mem := after initial (eventLog (FinalBits.reports w L.wires f))
    ∃ out es, out.pc = done ∧ Frame reg c out ∧
      out.privateMem = PrivateFields.storeBits L.dest (NodeArguments.packed X v (half X f v)) c.privateMem ∧
      Cost es (15+21*2^a+5*argumentSize X v) (5*2^a+argumentSize X v) ∧ Prefix M mem c es out := by
  let mem := after initial (eventLog (FinalBits.reports w L.wires f))
  have fields := rows.after_reports X L f sharedFit apart
  have bits (i) : mem (L.wires+i.val) = PrivateFields.bitValue w (f i) :=
    FinalBits.readback L.wires (by rwa [TerminalPrefix.width_sum]) f initial i
  exact run hl mem num fields (fits num fields f bits countFit headsFit sharedFit privateFit)
    f bits c hc saved hn stride

private theorem sum_side (X : State a g) (d : Bool) :
    ∑ v : X.network.Site, ∑ j, X.halfWidth v d j = X.totalWidth := by
  let target : X.network.Edge ≃ X.network.Edge := if d then X.slots.actualGraph.target.symm else Equiv.refl _
  let ws (e : X.network.Edge) := TerminalPrefix.width X (number X e)
  have eq (v : X.network.Site) (j : Fin (2^a)) : X.halfWidth v d j = ws (target (v,j)) := by
    cases d <;> exact (slot_width X v _ j).symm
  calc
    _ = ∑ e : X.network.Edge, ws (target e) := by
      change _ = ∑ e : X.network.Site × Fin (2^a), ws (target e)
      rw [Fintype.sum_prod_type]; simp_rw [eq]; rfl
    _ = ∑ e : X.network.Edge, ws e := target.sum_comp ws
    _ = ∑ j, TerminalPrefix.width X j := (number X).sum_comp (TerminalPrefix.width X)
    _ = X.totalWidth := TerminalPrefix.width_sum X

theorem argumentSize_total (X : State a g) : ∑ v : X.network.Site, argumentSize X v = 2*X.totalWidth := by
  simp only [argumentSize, Fintype.sum_bool, Finset.sum_add_distrib, sum_side, two_mul]

/-- Exact external traffic of all the actual gather prefixes, including
both occurrences of a loop and each of the five directory probes per arc. -/
theorem probes_total (X : State a g) (es : X.network.Site → List (Event w))
    (cost : ∀ v, Cost (es v) (15+21*2^a+5*argumentSize X v) (5*2^a+argumentSize X v)) :
    ∑ v : X.network.Site, countProbes (es v) = 5*TerminalPrefix.arcCount X + 2*X.totalWidth := by
  have card : Fintype.card X.network.Site = (siteOrder X).length := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder X).entries.symm
  simp only [(cost _).probes, Finset.sum_add_distrib, argumentSize_total, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card]
  change _ = 5 * ((siteOrder X).length * 2 ^ a) + _
  simp only [Nat.cast_id]
  ring

end PairSimulation.TerminalGatherNative

end VPVNP
end Computability
end OAI
