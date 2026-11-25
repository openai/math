import OAI.Computability.BorderVNP.DiagonalBootedLeadPacket
import OAI.Computability.BorderVNP.DiagonalAcceptedGuardedCores

/-! # The actual accepted route supplies the lead packet of its own completion -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier ResidueRates
open DiagonalResidueRAM VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena
open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader RoutingISA.Evaluator
open CompactMachine CellMacro.Generator BorderVNP.Cube DiagonalTallyCellReports
open scoped Classical BigOperators
set_option maxHeartbeats 950000
set_option synthInstance.maxSize 3000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {R : CommonField G aux q k s ord} {chart : AdvisedBranch R}
    [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
    {T r mult w pin : ℕ} (reader : ChosenReader chart (T+1) r mult w w pin)
local notation "par" => pairedTableParameters (k+1) s
local notation "J" => G.Entry ⊕ ι
local notation "query" => Board.Physical par pin w J
local notation "guess" => Guess (Fin par) reader.gridRank (Nat.clog 2 R.p+1) (Nat.clog 2 R.p)
local notation "bits" => (par+2)*pin
local notation "dim" => par+Fintype.card J

variable {axes box lanes selectors symbols n sites time link inner length : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO} {Edge : Type}
    (l : SignedTaskArena.Layout) (A : StartupArena)
    (W : Wiring T sites time ((pairedTableParameters (k+1) s+2)*pin) link inner length Edge)

variable {X Hist : Type} {Route : Hist → Type} {Private : Hist → Type}
  {Report : (i : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (q : Hist) → Route q → Type}
  {digits reserve groups cap : ℕ}
  (S : X → Fin (T+1) → PositiveTeam id gen n w)
  (joined : ∀ x (p : (u : Fin (T+1)) → (S x u).Prefix),
    JoinedCells (fun u => (S x u).pub) (fun u => (S x u).postMemory) (fun u => (S x u).generated) p)

variable (prep : JointBeforeCells S ≃ PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
    (Fin ((T+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool) Route Report)
  (banks : ∀ f : PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
    (Fin ((T+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool) Route Report, (joined (prep.symm f).1 (prep.symm f).2).Private ≃ Private f.2.1)
  {i : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool} {hist : Hist} {v : Route hist × Private hist}
  (rows : PreparedCellRows S joined prep banks i hist v)
  (fields : PositiveFields reserve axes groups cap (T+1) (pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)) digits)
  (H : rows.candidate.Completion fields)

/-- The canonical report and subtotal of this completion select a unique
original pre-call prefix. Its physical pinned Fourier packet yields the
post-call packet required for the column proof on that same candidate. -/
noncomputable def ChosenReader.completedPacketAtPrepared
    (col : Fin bits → Bool) (ib hb sb : Fin (T+1) → ℕ)
    (pdim : l.p.parameters=par) (gdim : Fintype.card J=l.p.report.gadgets) (teamCount : l.cube.teams=T+1)
    (protectedWords : ∀ u, H.Protected rows.candidate (PositiveFields.canonicalSubtotals digits H.rows) u l A)
    (lead : ∀ z : JointBeforeCells S, (row : Fin bits → Bool) ×
      reader.LeadPacketAt l A W (S z.1 0) (z.2 0) row col)
    (guessed : ∀ z : JointBeforeCells S, List.ofFn (lead z).1=List.ofFn (z.2 0).1)
    (decoded : ∀ f : PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
    (Fin ((T+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool) Route Report, let z := prep.symm f
      List.ofFn (z.2 0).1=List.ofFn ((W.jointGuess ib hb sb).symm f.1 0)) :
    reader.CompletedPacket W rows.candidate H i col := by
  let claim := PositiveFields.canonicalSubtotals digits H.rows
  let reported := canonicalReports rows.candidate.assigned H.core
  let f : PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
    (Fin ((T+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool) Route Report := ⟨i,hist,v.1,claim,rows.order.symm reported⟩
  let z := prep.symm f
  have packet := ChosenReader.LeadPacketAt.decodedRow reader (lead z).2 ib hb sb ((guessed z).trans (decoded f))
  exact ⟨fun _ => l,fun _ => A,protectedWords,pdim,gdim,teamCount,packet⟩

end Diagonal

end BorderVNP
end Computability
end OAI
