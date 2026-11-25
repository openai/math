import OAI.Computability.BorderVNP.DiagonalJointFiberColumn
import OAI.Computability.BorderVNP.DiagonalNativePositivePacket

/-! # The live column from the accepted physical executions of the chosen signed program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing ResidueBox ResiduePins ResidueIndex TeamContraction ProcessorSlots
open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator CompactMachine CellMacro.Generator BorderVNP.Cube
open scoped Classical BigOperators
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {e : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField e aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult tally w pin exp t link inner : ℕ} (reader : ChosenReader chart (R+1) r mult tally w pin)
    {Edge : Type} {dim box lanes selectors symbols : ℕ}
    (id : TableEntry dim box lanes selectors symbols → ℕ) (gen : Fragment IO)

local notation "h" => pairedTableParameters (k+1) s
local notation "Raw" => Fin ((h+2)*pin) → Bool
local notation "Idx" => Index (Fin (Module.finrank (ZMod C.p) chart.E)) (Fin h) (chart.pinRadius (R+1) r)
local notation "codec" => boxPinCodec h reader.rankFits reader.boxFits
local notation "Counts" => Tally (Fin (R+1)) (Fin h) (e.Entry ⊕ ι) exp

variable (G : Wiring R r t ((pairedTableParameters (k+1) s+2)*pin) link inner (k+1) Edge) (args : Fin (R+1) → UnitAddresses)
    (mac : TeamOpcode.Macros w 8) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (limit burst : ℕ) (Path : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → Type) [∀ raw, Fintype (Path raw)]
    (assigned : ∀ raw, Path raw → Tally (Fin (R+1)) (Fin (pairedTableParameters (k+1) s)) (e.Entry ⊕ ι) exp)

/-- The data obtained after running the startup and the private calls for
one live pin. Each team is indexed by the same assignment of the original
exterior wires. The decoder recovers complete substituted paths from the
actual accepted native returns, including the true reader memory image. -/
structure ChosenReader.WiredPinExecution (j : Idx) where
  /-- Shared exteriors on which every team can reach the private call. -/
  supported : (Exterior R r link → Bool) → Prop
  /-- A failed pre-call preparation on an agreeing exterior contributes zero. -/
  unsupported : ∀ ext, PositiveExterior G args ((codec).encode j) w ext → ¬ supported ext →
    (∏ u, positiveMaskedNativeValue G (signedBody id) mac pub reg args ((codec).encode j)
      limit burst ((k+1)^25) ext u) = 0
  /-- Returning program for each team on the jointly prepared exteriors. -/
  model : {ext : Exterior R r link → Bool // PositiveExterior G args ((codec).encode j) w ext ∧ supported ext} →
    Fin (R+1) → PositiveTeam id gen (k+1) w
  /-- Cell preparations on the same physical private bit banks. -/
  joined : ∀ x (a : (u : Fin (R+1)) → (model x u).Prefix), JoinedCells (fun u => (model x u).pub)
    (fun u => (model x u).postMemory) (fun u => (model x u).generated) a
  /-- Value and remaining cutoff after the real exterior startup. -/
  boot : ∀ x u, positiveMaskedNativeValue G (signedBody id) mac pub reg args ((codec).encode j)
    limit burst ((k+1)^25) x.val u =
    boundedValue (signedBody id) (model x u).pub (install gen (k+1) (model x u).routines)
      (model x u).bank (model x u).memory ((model x u).limit-(model x u).used) (model x u).burst ((k+1)^25)
  /-- Bijection and reader input for the full profile and original private assignments. -/
  fiber : NativeColumnFiber reader model joined Path assigned j

variable {reader id gen G args mac pub reg limit burst Path assigned}

/-- On this pin the physically installed program has exactly the desired
column. The signed mode split, startup rejection, positive execution, and
the four numerical reader inputs refer to one shared wiring and one clock. -/
theorem ChosenReader.WiredPinExecution.column [Fintype Edge] {j : Idx}
    (run : reader.WiredPinExecution id gen G args mac pub reg limit burst Path assigned j)
    (modes : signedContraction G.slot ((codec).encode j) =
      (if (codec).encode j = (codec).encode reader.star then 1 else 0) +
        ∑ ext, ∏ u, positiveMaskedNativeValue G (signedBody id) mac pub reg args ((codec).encode j)
          limit burst ((k+1)^25) ext u)
    (reject : ∀ ext, ¬ PositiveExterior G args ((codec).encode j) w ext →
      (∏ u, positiveMaskedNativeValue G (signedBody id) mac pub reg args ((codec).encode j)
        limit burst ((k+1)^25) ext u) = 0)
    (bounds : ∀ raw a, let z := assigned raw a
      Fits (chart.pinRadius (R+1) r) (parameterShift z.exponents) ∧
      (∀ i, z.exponents i < 2^tally) ∧ (∀ g, ∑ u, z.counts u g < 2^mult) ∧ (∀ g, ∑ u, z.counts u g < 2^tally)) :
    (signedContraction G.slot ((codec).encode j) : ZMod C.p) =
      (if j = reader.star then 1 else 0) + ∑ i, ∑ a : Path ((codec).encode i),
        entryWeight C.p (Module.finBasis (ZMod C.p) chart.E) (chart.pinRadius (R+1) r) (C.p^reader.power)
          (pow_pos C.prime.pos reader.power) (signedEquations chart.E k s ord chart.advice)
          (assigned ((codec).encode i) a).exponents i j ((assigned ((codec).encode i) a).coefficient chart.gadgets) := by
  have combine := sum_accepted_exteriors G args ((codec).encode j) (signedBody id) mac pub reg limit burst
    (Nat.succ_pos k) run.model run.joined (fun ext bad => by
      by_cases agrees : PositiveExterior G args ((codec).encode j) w ext
      · exact run.unsupported ext agrees (fun ready => bad ⟨agrees,ready⟩)
      · exact reject ext agrees) run.boot
  have bits : (codec).encode j = (codec).encode reader.star ↔ j = reader.star := by
    constructor
    · intro eqn
      have a := ((codec).decode_eq_some ((codec).encode j) j).2 rfl
      have b := ((codec).decode_eq_some ((codec).encode j) reader.star).2 eqn
      exact Option.some.inj (a.symm.trans b)
    · rintro rfl
      rfl
  have weighted := NativeColumnFiber.sum reader run.model run.joined Path assigned run.fiber bounds
  rw [modes, combine, Int.cast_add]
  apply congrArg₂ (·+·)
  · by_cases same : j = reader.star
    · simp only [ite_eq_left (bits.mpr same), ite_eq_left same, Int.cast_one]
    · simp only [ite_eq_right (mt bits.mp same), ite_eq_right same, Int.cast_zero]
  · refine Eq.trans (congrArg (fun v : ℤ => (v : ZMod C.p)) ?_) weighted
    exact Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _)) fun _ _ => rfl

end Diagonal

end BorderVNP
end Computability
end OAI
