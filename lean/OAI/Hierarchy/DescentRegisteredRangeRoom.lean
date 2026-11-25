import OAI.Hierarchy.DescentRegisteredPrefixNodes
import OAI.Hierarchy.DescentRegisteredOrdinaryHosts
import OAI.Hierarchy.DescentDatePopulation
import OAI.Hierarchy.DescentDatePortArchivePitchRoom

namespace OAI
/-! # Dated range-room receipts for the actual archived prefix registers -/
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

include hh cut in
theorem prefix_range_room (whole : before.whole p) (ports : DatePorts) (op : RotorSpec)
    (tail drift degree payload argUnit roleUnit : ℕ)
    (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree payload i)
    (population : DatePorts.Population S ports i)
    (density : ports.ArchivePitchRoom (S.groupCount i) payload argUnit roleUnit)
    (kAt : ports.venue.k=k) (occupied : Fintype.card tick.V≤ports.operandHosts) :
    DatePorts.RangeRoom ports tick (before.archive p hp br.origin.archive whole).bit :=
  ⟨prefix_registered_nodes X G S br hp hh before after cut whole ports op tail drift degree payload widths,
    fun v=>(tick.vertex (tick.placement.pos v).2).isLt.trans_le occupied,
    population.groups.symm,kAt.symm,density.operandPos⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM ProtocolRAM Catalyst
noncomputable section
variable {F P : Type} [Field F] {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
    {d k wire hist : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

theorem seed_occupied {cp p : ℕ} (X : Approximation F cp p) (op : RotorSpec)
    (R : ℕ) (l : DescentDatedSeedStartup.Layout) (H groups payload Z : ℕ)
    {z D : ℕ} (r : Reached W G q ε S k 0 z D wire hist) (before : S.hostSize 0≤H) :
    Fintype.card r.V≤(initial G op X R l k H groups payload Z).operandHosts := r.valid.host.trans before

theorem reset_occupied {n deg : ℕ} (board : NonlinearExpanders.Graph n deg)
    (tail age p f g drift degree h : ℕ) (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec)
    (s Z oldOperand oldPrimitive : ℕ) (old : StageVenueTail.Date) (addr : ℕ→ℕ→Bank) (roster : Bank)
    (floor atFloor : ℕ) {w : ℕ}
    (inputs : (PhysicalReset.scheduled G S board k tail age p f g drift degree h ordinary op s Z oldOperand oldPrimitive old addr roster floor).DateInputs atFloor w)
    {z D : ℕ} (r : Reached W G q ε S k (age+1) z D wire hist) :
    let a:=PhysicalReset.scheduled G S board k tail age p f g drift degree h ordinary op s Z oldOperand oldPrimitive old addr roster floor
    Fintype.card r.V≤(reset a atFloor inputs).operandHosts :=r.valid.host

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
