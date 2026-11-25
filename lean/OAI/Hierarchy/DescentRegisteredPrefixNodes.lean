import OAI.Hierarchy.DescentNamedPrivateArchive
import OAI.Hierarchy.DescentNamedPrefixRangeRoom
import OAI.Hierarchy.DescentDatePortArchiveWidths

namespace OAI
/-! # Exact local node capacity at the seed and all its registered successors -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentColonies DescentKernelHistory DescentHistoryOrder Catalyst
open Chronology DescentTerminalObservedExponent Computability.VPVNP.BurstRAM PrivateRAM GadgetNetwork
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k s z wire : ℕ}


private def OneNode {P : Type} {d : ℕ} {bits : P → ℕ}
    {W : MarkedWorld F d P bits} (a : Archive W) : Prop :=
  ∀ v, Fintype.card (a.bit.recipe v).Node = 1

private theorem transported_single {P : Type} {d : ℕ} {bits : P → ℕ}
    {W V : MarkedWorld F d P bits} {a : Archive W} (pkg : ArchiveTransport a V)
    (before : OneNode a) : OneNode pkg.data :=
  (pkg.carry (fun _ b => PLift (OneNode b)) ⟨before⟩).down

private theorem renamed_single {P : Type} {d : ℕ} {bits : P → ℕ}
    {W : MarkedWorld F d P bits} (a : Archive W) (v : Equiv.Perm W.graph.Site)
    (e : Equiv.Perm W.graph.Edge) (before : OneNode a) : OneNode (renamedArchive a v e) :=
  fun i => before (v.symm i)

private theorem seed_single {cp pins : ℕ} (X : Approximation F cp pins) (copies width : ℕ)
    (c : (initialGroup X copies width).Choice) : OneNode (seedArchive X copies width c) := by
  rintro ⟨j, u | pin⟩ <;> change Fintype.card Unit = 1 <;> simp

private theorem single_of_eq {P : Type} {d : ℕ} {bits : P → ℕ}
    {W : MarkedWorld F d P bits} (a b : Archive W) (equal : a = b)
    (single : OneNode a) : OneNode b := equal ▸ single

open private Origin.archive_eq from OAI.Hierarchy.DescentNamedPrivateArchive
attribute [local irreducible] Origin.archivePackage Origin.source

namespace Origin
variable {cp pins : ℕ} {X : Approximation F cp pins}
variable {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin (S:=S) (s:=s) (G:=G) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits)

/-- Renaming the seed rack preserves its one original primitive per vertex. -/
theorem node_card (v : ((initial X S.copies s (S.groupCount 0) k digits).state c).graph.Site) : Fintype.card (o.archive.bit.recipe v).Node=1 := by
  have transported : OneNode o.archivePackage.data :=
    transported_single o.archivePackage (renamed_single (seedArchive X S.copies s c)
      (site o.raw) (edge o.raw) (seed_single X S.copies s c))
  exact single_of_eq o.archivePackage.data o.archive (Origin.archive_eq o).symm transported v


end Origin
end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentKernelHistory DescentPrimitivePalette DescentCompiler Chronology
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
attribute [local irreducible] Origin.source
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k}
    {run : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies, Fin (Fintype.card (Port pins X.width)))
      (fun _ => S.firstWidth G.b p * 1)} {i z D : ℕ}
    {tick : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)))
      (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k i z D
      (S.epochPower ^ S.priceExponent) (S.firstWidth G.b p)}
    (hp : 0<p) (hh : 0<S.height)
    (before : Path br.origin.source tick) (after : Path tick br.target)
    (cut : before.append after=br.path)

private theorem seed_count_at {F Q : Type} [Field F] {d p : ℕ} {bits : Q→ℕ}
    {U V : MarkedWorld F d Q bits} {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
    {k init D₀ j z D wire hist : ℕ} {r : Reached U G q ε S k 0 init D₀ wire hist}
    {u : Reached V G q ε S k j z D wire hist} (a : Archive U) (hp : 0<p)
    (seed : ∀v,Fintype.card (a.bit.recipe v).Node=1) (path : Path r u) (zero : j=0)
    (wh : path.whole p) (v : V.graph.Site) : Fintype.card (((path.archive p hp a wh).bit.recipe v).Node)=1 :=by
  cases path with
  | here=>exact seed v
  | ordinary prev ticket=>omega
  | reset prev closed=>omega

include hh cut in
private theorem prefix_node_bound (whole : before.whole p) (v : W.graph.Site) :
    Fintype.card (((before.archive p hp br.origin.archive whole).bit.recipe v).Node) ≤
      if i = 0 then 1 else S.retainedNodes := by
  split
  · rename_i zero
    exact (seed_count_at br.origin.archive hp br.origin.node_card before zero whole v).le
  · exact prefix_nodes X G S br hp hh before after cut whole v

include hh cut in
theorem prefix_registered_nodes (whole : before.whole p) (ports : DatePorts) (op : RotorSpec)
    (tail drift degree payload : ℕ) (chart : DatePorts.ArchiveWidths G S op ports k tail p drift degree payload i)
    (v : W.graph.Site) : Fintype.card (((before.archive p hp br.origin.archive whole).bit.recipe v).Node)≤ports.nodes :=by
  rw [chart.nodes]
  exact prefix_node_bound X G S br hp hh before after cut whole v

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
