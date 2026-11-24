import OAI.Computability.VPVNP.PairSimulationMapHandlerAction
import OAI.Computability.VPVNP.PairSimulationMapHandlerClock
import OAI.Computability.VPVNP.PairSimulationMapEntryExact

/-! # Counting an actual finite matrix action from its trace

The register-writer trace contributes its fixed loads. The remaining
instructions are private ticks for the selector, the repeated rows and
the histogram update. This bound applies at the scratch snapshot used
by the surrounding resident loop.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapHandlerImage.Family

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifEntry
open BurstRAM PrivateRAM CompressorRecords MapConstants
open private eval_cost from OAI.Computability.VPVNP.CompressorRecordsRowRecipe
open private lines_probes from OAI.Computability.VPVNP.CompressorRecordRegisterSetup

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'} {t shared w : ℕ}

private theorem dispatch_le {α : Type*} (ss : List α) (s : α) :
    MapDriver.Program.dispatchSteps ss s ≤ 2*ss.length := by
  induction ss with
  | nil => exact le_rfl
  | cons a as ih =>
    rw [MapDriver.Program.dispatchSteps,List.length_cons,Nat.mul_succ]
    split <;> omega

private theorem tick_probes (n : ℕ) : countProbes (List.replicate n (.tick : Event w))=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,countProbes] using ih

set_option maxHeartbeats 650000 in
-- Unfold the physical selector and row clocks for this dependent matrix layout.
theorem successEvents_cost (F : Family B t shared) (hp : ∀ e, 0 < p₀ e)
    (I : LocalHistory.EntryInput B)
    (hw : widthThreshold B ≤ w) (pub : Fin 5 → BurstRAM.Word w)
    (state : BurstRAM.Word w) (m : Memory w) :
    let key := (demandGrid B hp I.demand,I.party)
    let es := F.successEvents hp I hw pub state m
    es.length ≤ F.clock key (repetitions B I.demand) ∧ countProbes es = F.probes key := by
  intro key es
  let L := F.layout key
  let P := MapInline.callProgram L
  let u := repetitions B I.demand
  let d := demandBits src dst I.party I.demandBits
  let x := mapHalf G (fun _ ↦ inputBits) I.supplyBits
  let fd := (fits_of_threshold B hw).2.1 key.1
  let fs := (fits_of_threshold B hw).2.2.1
  let words := (MapConstants.source (w:=w) L F.ordinal).publicData
  let ports := (MapPortAgreement.ports G I.party L.core.edgeOrder).length
  have bounded (θ : Fin u → Selector B) :
      entryTicks hp I L F.ordinal hw θ ≤
        L.lines.length+(1+3*ports)+MapNativeClock.cap B key.1 key.2 u := by
    let rc := MapRowLoop.rowCap B key.1 key.2
    let ticks :=
      MapRowLoop.rowSteps B key.1 key.2 I.demand I.payload d x θ fd fs P.bank.keyPort words
    have rows (i : Fin u) : ticks i ≤ rc :=
      (MapRow.exactSteps_le_cap B key.1 (θ i) i key.2 I.demand I.payload d x
        (fun e => MotifEntry.offset (fun l => basePayload B (θ l) e) i) fd (fs _)
        (P.bank.keyPort _) words).trans
        (Finset.single_le_sum (fun s _ => Nat.zero_le (MapRow.cap B key.1 s key.2))
          (Finset.mem_univ (θ i)))
    have body : P.driverTicks d x θ fd fs words ≤ (5+2*(selectorTable B).length+rc)*u+1 := by
      unfold MapEntry.Program.driverTicks MapDriver.Program.exactSteps
      apply Nat.add_le_add_right
      calc
        _ ≤ ∑ _ : Fin u, (5+2*(selectorTable B).length+rc) := by
          apply Finset.sum_le_sum
          intro i _
          exact Nat.add_le_add (Nat.add_le_add_left (dispatch_le _ _) 5) (rows i)
        _ = _ := by simp [Nat.mul_comm]
    have guard := P.selector.successTicks_le (selectorCode B) θ ports
    have numPorts := MapPortAgreement.ports_length_le G I.party L.core.edgeOrder
    change ports ≤ 2*Fintype.card E at numPorts
    have selector : P.selector.successTicks (selectorCode B) θ ports ≤
        (7*(u*B.selectorBits)+6)*(2*Fintype.card E)+3+
        ((6*B.selectorBits+1+(2*(selectorTable B).length+1)+5)*u+1) :=
      guard.trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ numPorts) _) _)
    change L.lines.length+(1+3*ports)+P.successTicks d x θ fd fs words ≤ _
    apply Nat.add_le_add_left
    unfold MapEntry.Program.successTicks MapNativeClock.cap
    change P.selector.successTicks (selectorCode B) θ ports + P.driverTicks d x θ fd fs words +
      ((Fintype.card E+1)+(7*u+1)) ≤
      (7*(u*B.selectorBits)+6)*(2*Fintype.card E)+3+
      ((6*B.selectorBits+1+(2*(selectorTable B).length+1)+5)*u+1)+
      ((5+2*(selectorTable B).length+rc)*u+1)+(Fintype.card E+1)+(7*u+1)
    omega
  let recipe := MapArgumentWriter.recipes (F.base key) (F.fields key)
  have writer := eval_cost pub state m (RegisterSetup.lines recipe) (fun _ => 0)
  have probes := lines_probes recipe pub state m (fun _ => 0)
  have wrLen : (MapArgumentWriter.events (F.base key) (F.fields key) pub state m).length=
      MapArgumentWriter.clock (F.base key) (F.fields key) := by
    simp only [MapArgumentWriter.events,List.length_append,List.length_replicate,
      MapArgumentWriter.clock]
    exact congrArg (·+_) writer.1
  have wrPr : countProbes (MapArgumentWriter.events (F.base key) (F.fields key) pub state m) =
      F.probes key := by
    simp only [MapArgumentWriter.events,countProbes_append,tick_probes,Nat.add_zero]
    exact probes
  change (F.successEvents hp I hw pub state m).length ≤ _ ∧
    countProbes (F.successEvents hp I hw pub state m)=_
  simp only [successEvents,List.length_append,List.length_replicate,
    countProbes_append,tick_probes,Nat.add_zero]
  refine ⟨?_,wrPr⟩
  rw [wrLen]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  change ((selectorRun G (selectorTable B) (selectorCode B) I.payload I.party x).1.elim
    0 (entryTicks hp I L F.ordinal hw)) ≤
    L.lines.length+(1+3*ports)+MapNativeClock.cap B key.1 key.2 u
  cases (selectorRun G (selectorTable B) (selectorCode B) I.payload I.party x).1 with
  | none => exact Nat.zero_le _
  | some θ => exact bounded θ

end PairSimulation.MapHandlerImage.Family

end VPVNP
end Computability
end OAI
