import OAI.Computability.BorderVNP.DiagonalCompletedReader
import OAI.Computability.BorderVNP.DiagonalPreparedColumnFiber

/-! # Actual ledger and lead-packet readback on the canonical inverse of the native fiber -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing ResidueBox ResiduePins ResidueIndex TeamContraction ProcessorSlots TeamContraction.JointHeader
open RoutingISA RoutingISA.Evaluator CellMacro.Generator BorderVNP.Cube
open scoped Classical BigOperators

variable {F : Type} [Field F] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity F D m}
    {aux : ι → F} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField G aux q k s ord} {chart : AdvisedBranch C} [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult w pin exp : ℕ} (reader : ChosenReader chart (R+1) r mult w w pin)

local notation "pdim" => pairedTableParameters (k+1) s
local notation "Idx" => Index (Fin (Module.finrank (ZMod C.p) chart.E)) (Fin pdim) (chart.pinRadius (R+1) r)

variable {axes box lanes sel sym n width : ℕ} {id : TableEntry axes box lanes sel sym → ℕ} {gen : Fragment IO}
    {X Hist : Type} [Fintype X] [Fintype Hist] {Route : Hist → Type} {Bank : Hist → Type}
    {Report : (i : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (q : Hist) → Route q → Type}
    (S : X → Fin (R+1) → PositiveTeam id gen n w)
    (J : ∀ x (p : (u : Fin (R+1)) → (S x u).Prefix),
      JoinedCells (fun u => (S x u).pub) (fun u => (S x u).postMemory) (fun u => (S x u).generated) p)
    (prep : JointBeforeCells S ≃ PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
      (Fin ((R+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*width) → Bool) Route Report)
    (banks : ∀ f : PreparedFields (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) Hist
      (Fin ((R+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*width) → Bool) Route Report, (J (prep.symm f).1 (prep.symm f).2).Private ≃ Bank f.2.1)
    (rows : ∀ i z v, PreparedCellRows S J prep banks i z v)

variable {reserve groups cap : ℕ}
    (header : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (z : Hist) → Route z × Bank z → PositiveFields reserve axes groups cap (R+1) (pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)) width)
    (guard : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → (z : Hist) → Route z × Bank z → Prop)
    (sound : ∀ i z v rr c, let A := (rows i z v).candidate
      (A.joined rr c (A.candidate rr c).1).privateWeight (A.candidate rr c).2 ≠ 0 → guard i z v)
    (complete : ∀ i z v, guard i z v → ((rows i z v).candidate).Completion (header i z v))
    {Term : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → Hist → Type}
    [∀ i z, Fintype (Term i z)]
    (decode : ∀ i z, {v : Route z × Bank z // guard i z v} ≃ Term i z)
    (assigned : ∀ i, (Σ z, Term i z) → Tally (Fin (R+1)) (Fin (pairedTableParameters (k+1) s)) (G.Entry ⊕ ι) exp)

variable {time link inner length : ℕ} {Edge : Type}
    (W : Wiring R r time ((pairedTableParameters (k+1) s+2)*pin) link inner length Edge)
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 4000
open scoped BigOperators Classical

/-- The canonical inverse inserts exactly the guarded source's private data.
Its forced report and claim words put the original numbered team and decoded
path tally in the returning native memory. -/
noncomputable def NativeColumnFiber.ofCompletedPackets (j : Idx)
    (packetAt : ∀ i z v (hv : guard i z v), reader.CompletedPacket W (rows i z v).candidate (complete i z v hv)
      i ((boxPinCodec pdim reader.rankFits reader.boxFits).encode j))
    (totals : ∀ i z v (hv : guard i z v) c,
      (∑ t,(complete i z v hv).rows t c) =
        ∑ t,DiagonalTallyRAM.tallyRow ((assigned i ⟨z,decode i z ⟨v,hv⟩⟩).numberScalars
          (Fintype.equivFin (G.Entry ⊕ ι))) t c) :
    NativeColumnFiber reader S J (fun i => Σ z, Term i z) assigned j := by
  apply NativeColumnFiber.ofPrepared reader S J prep banks rows header guard sound complete decode assigned j
  · intro i z v hv u
    let X := (rows i z v).candidate
    let H := complete i z v hv
    let rr := DiagonalTallyCellReports.canonicalReports X.assigned H.core
    let claim := PositiveFields.canonicalSubtotals width H.rows
    let input := packetAt i z v hv
    have pass := ((X.completed H).pass_iff rr claim).mpr ⟨rfl,rfl⟩
    exact UncheckedCandidate.Completion.teamAt X H rr claim pass u (input.layout u) (input.arena u) (input.protectedWords u)
  · intro i z v hv
    let X := (rows i z v).candidate
    let H := complete i z v hv
    let rr := DiagonalTallyCellReports.canonicalReports X.assigned H.core
    let claim := PositiveFields.canonicalSubtotals width H.rows
    let input := packetAt i z v hv
    let term := assigned i ⟨z,decode i z ⟨v,hv⟩⟩
    have pass := ((X.completed H).pass_iff rr claim).mpr ⟨rfl,rfl⟩
    exact readerAtCompletedCandidate reader (input.layout 0) (input.arena 0) W X H rr claim pass input.parameters
      input.gadgets input.teams i ((boxPinCodec pdim reader.rankFits reader.boxFits).encode j) term
      (input.protectedWords 0) input.leadPacket (totals i z v hv)

end Diagonal

end BorderVNP
end Computability
end OAI
