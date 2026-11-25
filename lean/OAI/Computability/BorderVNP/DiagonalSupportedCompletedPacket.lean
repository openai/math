import OAI.Computability.BorderVNP.DiagonalPreparedCompletedPacket
import OAI.Computability.BorderVNP.DiagonalBootedLeadInput
import OAI.Computability.BorderVNP.DiagonalJointBootedSupport

/-! # The lead reader of the actual jointly supported teams -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier ResidueRates
open DiagonalResidueRAM VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena
open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader RoutingISA.Evaluator
open CompactMachine CellMacro.Generator BorderVNP.Cube DiagonalTallyCellReports
open scoped Classical BigOperators
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 3000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {common : CommonField G aux q k s ord} {chart : AdvisedBranch common}
    [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    {R r mult w pin : ℕ} (reader : ChosenReader chart (R+1) r mult w w pin)
local notation "bits" => (pairedTableParameters (k+1) s+2)*pin
local notation "query" => Fintype.card (Board.Physical (pairedTableParameters (k+1) s) pin w (G.Entry ⊕ ι))
local notation "dim" => pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)

variable (l : SignedTaskArena.Layout) (A : StartupArena)
    {sites time link inner n : ℕ} {Edge : Type} {gen : Fragment IO}
    (wire : Wiring R sites time ((pairedTableParameters (k+1) s+2)*pin) link inner n Edge)
    {pub : Fin (R+1) → Arg → Word w} {regs : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    (col : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool)
    (boot : (x : {ext // PositiveExterior wire args col w ext}) → (u : Fin (R+1)) →
      BootedPinStart gen wire pub regs args col x.val u)
    (limit burst : ℕ) (cap : TeamScales.width n (1/2) ≤ burst)
    (next : (x : {ext // PositiveExterior wire args col w ext ∧ PinStart.preCallSupport (fun z u => (boot z u).start) l.id ext}) →
      (u : Fin (R+1)) → let b := boot ⟨x.val,x.property.1⟩ u
        PositiveContinuation l.id gen n (pub u) (TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n))
          b.start.bank b.memory b.pins b.used limit)

local notation3 (prettyPrint := false) "teams" => BootedPinStart.supportedTeam l.id boot limit burst cap next

/-- Each jointly reached prefix already carries its actual pinned digits on
the lead team. Applying the boot reader and its native protected-memory return
gives the complete pre-finish packet on precisely those digits. -/
noncomputable def ChosenReader.supportedLeadPacket
    (source : ∀ x, reader.ProtectedReader l A wire (boot x 0) limit burst cap)
    (kept : ∀ z : JointBeforeCells teams, let b := boot ⟨z.1.val,z.1.property.1⟩ 0
      ReaderKept A (6+3*reader.gates+query) bits b.memory (b.pins (z.2 0).1).val.2.2 (z.2 0).2.val.2.2)
    (z : JointBeforeCells teams) : (row : Fin bits → Bool) × reader.LeadPacketAt l A wire (teams z.1 0) (z.2 0) row col :=
  ⟨(z.2 0).1,source ⟨z.1.val,z.1.property.1⟩ (next z.1 0) (z.2 0) (kept z)⟩

/-- The row supplied by a reached lead packet is the actual raw pin vector
of the positive prefix. -/
theorem ChosenReader.supportedLeadPacket_digits
    (source : ∀ x, reader.ProtectedReader l A wire (boot x 0) limit burst cap)
    (kept : ∀ z : JointBeforeCells teams, let b := boot ⟨z.1.val,z.1.property.1⟩ 0
      ReaderKept A (6+3*reader.gates+query) bits b.memory (b.pins (z.2 0).1).val.2.2 (z.2 0).2.val.2.2)
    (z : JointBeforeCells teams) :
    List.ofFn (reader.supportedLeadPacket l A wire col boot limit burst cap next source kept z).1 = List.ofFn (z.2 0).1 := rfl

local notation3 (prettyPrint := false) "runTeams" N:arg => BootedPinStart.supportedTeam l.id boot limit burst cap N

/-- The lead packet on each supported continuation and original checked
completion of this fixed boot. -/
def ChosenReader.SupportedColumnPackets : Type 1 :=
  ∀ (nextRun : (x : {ext // PositiveExterior wire args col w ext ∧ PinStart.preCallSupport (fun z u => (boot z u).start) l.id ext}) →
      (u : Fin (R+1)) → let b := boot ⟨x.val,x.property.1⟩ u
        PositiveContinuation l.id gen n (pub u) (TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n))
          b.start.bank b.memory b.pins b.used limit)
    {Hist : Type} {Route : Hist → Type} {Private : Hist → Type}
    {Report : (i : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (q : Hist) → Route q → Type}
    {digits reserve groups capacity : ℕ}
    (joined : ∀ (x : {ext // PositiveExterior wire args col w ext ∧ PinStart.preCallSupport (fun z u => (boot z u).start) l.id ext}) (p : (u : Fin (R+1)) → ((runTeams nextRun) x u).Prefix),
      JoinedCells (fun u => ((runTeams nextRun) x u).pub) (fun u => ((runTeams nextRun) x u).postMemory) (fun u => ((runTeams nextRun) x u).generated) p)
    (prep : JointBeforeCells (runTeams nextRun) ≃ PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
      (Fin ((R+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool) Route Report)
    (banks : ∀ f : PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
      (Fin ((R+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool) Route Report,
      (joined (prep.symm f).1 (prep.symm f).2).Private ≃ Private f.2.1)
    {i : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool} {hist : Hist} {v : Route hist × Private hist}
    (rows : PreparedCellRows (runTeams nextRun) joined prep banks i hist v)
    (fields : PositiveFields reserve l.cube.n groups capacity (R+1) (pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)) digits)
    (H : rows.candidate.Completion fields)
    (ib hb sb : Fin (R+1) → ℕ)
    (_protectedWords : ∀ t,H.Protected rows.candidate (PositiveFields.canonicalSubtotals digits H.rows) t l A)
    (_kept : ∀ z : JointBeforeCells (runTeams nextRun), let b := boot ⟨z.1.val,z.1.property.1⟩ 0
      ReaderKept A (6+3*reader.gates+query) bits b.memory (b.pins (z.2 0).1).val.2.2 (z.2 0).2.val.2.2)
    (_decoded : ∀ f : PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
      (Fin ((R+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool) Route Report, let z : JointBeforeCells (runTeams nextRun) := prep.symm f
      List.ofFn (z.2 0).1=List.ofFn ((wire.jointGuess ib hb sb).symm f.1 0)),
    reader.CompletedPacket wire rows.candidate H i col

/-- The same native return that completes the report core supplies its
post-call Fourier packet. Only the actual pin-digit readback is used to
interpret its original row. -/
noncomputable def ChosenReader.completedPacketAtSupported
    (source : ∀ x, reader.ProtectedReader l A wire (boot x 0) limit burst cap)
    (pdim : l.p.parameters = pairedTableParameters (k+1) s)
    (gdim : Fintype.card (G.Entry ⊕ ι)=l.p.report.gadgets) (nt : l.cube.teams=R+1)
    : reader.SupportedColumnPackets l A wire col boot limit burst cap := by
  intro nextRun Hist Route Private Report digits reserve groups capacity joined prep banks i hist v rows fields H ib hb sb
    protectedWords kept decoded
  exact reader.completedPacketAtPrepared l A wire (runTeams nextRun) joined prep banks rows fields H col ib hb sb pdim gdim nt protectedWords
    (reader.supportedLeadPacket l A wire col boot limit burst cap nextRun source kept)
    (reader.supportedLeadPacket_digits l A wire col boot limit burst cap nextRun source kept) decoded
/-- The protected completion of a real guarded bank and its exact original
column can be chosen together with the routed packet of that same completion. -/
theorem ChosenReader.guardedPacketsAtSupported
    (source : ∀ x, reader.ProtectedReader l A wire (boot x 0) limit burst cap)
    (pdim : l.p.parameters = pairedTableParameters (k+1) s)
    (gdim : Fintype.card (G.Entry ⊕ ι)=l.p.report.gadgets) (nt : l.cube.teams=R+1)
    (nextRun : (x : {ext // PositiveExterior wire args col w ext ∧ PinStart.preCallSupport (fun z u => (boot z u).start) l.id ext}) →
      (u : Fin (R+1)) → let b := boot ⟨x.val,x.property.1⟩ u
        PositiveContinuation l.id gen n (pub u) (TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n))
          b.start.bank b.memory b.pins b.used limit)
    {Hist : Type} {Route : Hist → Type} {Private : Hist → Type}
    {Report : (i : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (q : Hist) → Route q → Type}
    {digits reserve groups capacity : ℕ}
    (joined : ∀ (x : {ext // PositiveExterior wire args col w ext ∧ PinStart.preCallSupport (fun z u => (boot z u).start) l.id ext}) (p : (u : Fin (R+1)) → ((runTeams nextRun) x u).Prefix),
      JoinedCells (fun u => ((runTeams nextRun) x u).pub) (fun u => ((runTeams nextRun) x u).postMemory) (fun u => ((runTeams nextRun) x u).generated) p)
    (prep : JointBeforeCells (runTeams nextRun) ≃ PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
      (Fin ((R+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool) Route Report)
    (banks : ∀ f : PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
      (Fin ((R+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool) Route Report,
      (joined (prep.symm f).1 (prep.symm f).2).Private ≃ Private f.2.1)
    {i : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool} {hist : Hist} {v : Route hist × Private hist}
    (rows : PreparedCellRows (runTeams nextRun) joined prep banks i hist v)
    (fields : PositiveFields reserve l.cube.n groups capacity (R+1) (pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)) digits)
    (actualRows : Fin (R+1) → Fin (pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)) → ℕ)
    (trueColumn : Fin (pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)) → ℕ)
    (completed : ∃ H : rows.candidate.Completion fields, H.rows=actualRows ∧
      (∀ proposal t,H.Protected rows.candidate proposal t l A) ∧ ∀ c, (∑ t,H.rows t c)=trueColumn c)
    (ib hb sb : Fin (R+1) → ℕ)
    (kept : ∀ z : JointBeforeCells (runTeams nextRun), let b := boot ⟨z.1.val,z.1.property.1⟩ 0
      ReaderKept A (6+3*reader.gates+query) bits b.memory (b.pins (z.2 0).1).val.2.2 (z.2 0).2.val.2.2)
    (decoded : ∀ f : PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
      (Fin ((R+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool) Route Report, let z : JointBeforeCells (runTeams nextRun) := prep.symm f
      List.ofFn (z.2 0).1=List.ofFn ((wire.jointGuess ib hb sb).symm f.1 0)) :
    ∃ H : rows.candidate.Completion fields, Nonempty (reader.CompletedPacket wire rows.candidate H i col) ∧
      ∀ c,(∑ t,H.rows t c)=trueColumn c := by
  obtain ⟨H,_,safe,ok⟩ := completed
  refine ⟨H,⟨?_⟩,ok⟩
  exact reader.completedPacketAtSupported l A wire col boot limit burst cap source pdim gdim nt nextRun joined prep banks
    rows fields H ib hb sb (safe (PositiveFields.canonicalSubtotals digits H.rows)) kept decoded

end Diagonal

end BorderVNP
end Computability
end OAI
