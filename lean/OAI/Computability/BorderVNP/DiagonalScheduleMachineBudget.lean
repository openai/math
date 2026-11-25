import OAI.Computability.BorderVNP.DiagonalAdmissibleRange
import OAI.Computability.BorderVNP.CellPacketGlobalClock
import OAI.Computability.BorderVNP.FiniteProcessorScale

/-! # A common admissible batch exponent for the private packet and finite field processor

The packet word and transition allowances refer to the physical packed burst
and the generated sparse validator. The team installation uses the exact
register, argument and routine counts of the fixed diagonal machine. The
batch exponent is chosen before the field, processor code and private returns.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales TeamContraction TeamSite VPVNP BurstRAM
open RoutingISA CellSparse CellMacro CellMacro.Generator
universe u

/-- The manuscript's packed-word and native step allowances for each actual compact
packet at this length and batch count, with the separate physical translation clock. -/
def PacketBudgetAt (A B j n r : ℕ) : Prop :=
  ∀ M E w p t : ℕ, M ≤ width n (1/5) → E ≤ width n (1/4) → 0 < w → w ≤ n →
    ∀ (D : Directory) (ext : List Bool), ext.length ≤ E →
    D.StaticBounds A M → D.CompactFields p (4*(M+E+1)^3) →
    D.records.length ≤ 4*(M+E+1)^3 → D.reportedCounts.length ≤ 4*(M+E+1)^3 →
    Packet.storedMass D ≤ A*(M+1)^2 → (∀ v ∈ Packet.words D p, v.size ≤ B*(logWidth r n+1)^j) →
    t ≤ B*(M+E+1)^96*(logWidth r n+1)^j →
    (CompactFrame.pack w (Packet.input D p ext)).length ≤ width n (1/2) ∧
    let s := D.program p
    let ops := (CompactMachine.withExternal ext s).expand []
    2*(3*((CompactFrame.pack w (Packet.input D p ext)).length*w)+
      CompactPacket.generationCost 8 (Packet.bits D p) ext s t+(2*(stream ops).length+1)+budget ops) ≤ n^25

/-- The actual finite-field installation and path/weight correspondence, at every exterior
team count, on the physical word and Batcher-sort geometry for this diagonal schedule. -/
def FieldBudgetAt (α τ : ℝ) (E : ℕ) {pc m g : ℕ} {Q Γ : Type} [Fintype Q]
    {F : Type u} [Field F] [Fintype F] (P : TeamOpcode.Program pc 64 32 8)
    (lib : Fin 8 → Macro Q Γ m g) (weights : FieldProcessor.Returns Q Γ F m 8) (n r : ℕ) : Prop :=
  ∀ hr : 0 < r, ∀ other : ℕ,
    ∃ geo : FieldProcessor.Scale (FieldProcessor.machine P lib weights) pc 64 32 α (τ/5) r n other
      ((logWidth r n)^(E+1)) (Wires.sortExponent (block (τ/5) n)),
      FieldProcessor.AtScale P lib weights geo hr

/-- A single admissible batch exponent simultaneously bounds the validator, word-width
logarithms, interior port count, and the actual installations over all finite fields. -/
structure MachineBudget (α τ : ℝ) (E d A B j : ℕ) (ω : ℝ) : Prop where
  packet : AdmissibleRange ω (PacketBudgetAt A B j)
  log : AdmissibleRange ω (fun n r => (logWidth r n : ℝ)^d ≤ (n : ℝ)^(τ/2000))
  ports : ∀ c : ℕ, AdmissibleRange ω (fun n r =>
    let w := (logWidth r n)^(E+1)
    c*Wires.innerWidth r 64 w (Wires.sortExponent (block (τ/5) n)) (w+1) ≤ n)
  field : ∀ {pc m g : ℕ} {Q Γ : Type} [Fintype Q] {F : Type u} [Field F] [Fintype F]
    (P : TeamOpcode.Program pc 64 32 8) (lib : Fin 8 → Macro Q Γ m g)
    (weights : FieldProcessor.Returns Q Γ F m 8), AdmissibleRange ω (FieldBudgetAt α τ E P lib weights)

/-- Any smaller batch exponent preserves the same four uniform machine guarantees. -/
theorem MachineBudget.shrink {α τ u' v : ℝ} {E d A B j : ℕ} (h : MachineBudget.{u} α τ E d A B j v)
    (huv : u' ≤ v) : MachineBudget.{u} α τ E d A B j u' where
  packet := h.packet.shrink huv
  log := h.log.shrink huv
  ports c := (h.ports c).shrink huv
  field P lib weights := (h.field P lib weights).shrink huv

/-- Choose a common strictly positive exponent before fixing a field, processor,
private library, or return weights. Thresholds for their installations may depend on
these subsequently fixed data. -/
theorem exists_machineBudget {α τ : ℝ} (hα : 0 < α) (ha : α < 1/1000) (hτ : 0 < τ)
    (ht : τ < α/100) (E d A B j : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ MachineBudget.{u} α τ E d A B j ω := by
  obtain ⟨v,hv,packet⟩ := CompactPacket.eventually_global_clock A B j
  obtain ⟨w,hw,log,ports,field⟩ := FieldProcessor.lemma7_1.{u} E d (α := α) (ξ := τ/5) (γ := τ/2000)
    (by linarith only [ha]) (by positivity) (by linarith only [ha,ht])
    (by linarith only [hα,ht]) (by positivity)
  have packet' : AdmissibleRange v (PacketBudgetAt A B j) := by
    filter_upwards [packet] with n atPacket
    intro r hr room M E' w' p t hm he hpos hlen
    exact atPacket r M E' w' p t hr room hm he hpos hlen
  refine ⟨min v w,lt_min hv hw,packet'.shrink (min_le_left ..),?_,?_,?_⟩
  · exact (show AdmissibleRange w (fun n r => (logWidth r n : ℝ)^d ≤ (n : ℝ)^(τ/2000)) from log).shrink
      (min_le_right ..)
  · intro c
    exact (show AdmissibleRange w _ from ports 64 c).shrink (min_le_right ..)
  · intro pc m g Q Γ instQ F instF fintypeF P lib weights
    apply AdmissibleRange.shrink (v := w) _ (min_le_right ..)
    filter_upwards [field P lib weights] with n atField
    intro r hr room positive other
    exact atField r positive room other

end Diagonal

end BorderVNP
end Computability
end OAI
