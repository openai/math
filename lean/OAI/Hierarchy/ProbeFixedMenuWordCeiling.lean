import OAI.Hierarchy.ProbeFixedRowPages
import OAI.Hierarchy.ProbeStripThreshold

namespace OAI
/-! # A uniform bound on every word of the fixed discrepancy ROMs -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen AttemptGate
open scoped Classical Fin.CommRing

/-- Reducing the natural ROM word modulo the CPU word size can only lower
its normalized score, even when the exact discrepancy does not fit. -/
theorem resident_ceiling_le {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
    {k digits w : ℕ} [Nonempty (Fin k)] (edge : E → LinearAlgebra.SpectralBooks.ChordGraph.Chord k)
    (req : A → E) (test : StripTest digits) (grid : (Fin digits → Fin test.radix) → E → ℝ)
    (mem : Memory w) (i : Fin test.rows) (key : Fin digits → Fin test.radix) (B : ℝ)
    (pos : 0 ≤ B) (hp : 0 < test.precision) (printed : ∀ e,0 ≤ grid key e ∧ grid key e ≤ B)
    (digitsRead : ∀ j,(test.quoted j).eval mem (i.val:Word w) = ((key j).val:Word w))
    (rom : test.table.read mem ((finFunctionFinEquiv key).val:Word w) =
      (discrepancyWord F edge req grid test.precision key:Word w)) :
    (test.failure.value mem i:ℝ)/test.precision ≤ B := by
  by_cases asleep : test.live.eval mem (i.val:Word w) = 0
  · simpa [FailureWords.value,FailureWords.effective,StripTest.failure,Expr.eval,asleep,
      ThreeFlat.RAM.DescriptorExpr.Comparison.test] using pos
  have selected : (menuLookup test.table test.radix (List.ofFn test.quoted)).eval mem (i.val:Word w) =
      (discrepancyWord F edge req grid test.precision key:Word w) := by
    change test.table.read mem _ = _
    rw [eval_menuKey _ _ _ key digitsRead]
    exact rom
  have raw : test.failure.value mem i ≤ discrepancyWord F edge req grid test.precision key := by
    simp only [FailureWords.value,FailureWords.effective,StripTest.failure,Expr.eval,
      ThreeFlat.RAM.DescriptorExpr.Comparison.test,Nat.cast_zero,beq_iff_eq,
      ite_eq_right asleep]
    exact (congrArg Fin.val selected).le.trans (Nat.mod_le _ _)
  refine (div_le_div_of_nonneg_right (Nat.cast_le.mpr raw) (Nat.cast_nonneg (α:=ℝ) test.precision)).trans ?_
  let score := Probe.discrepancy F edge req (grid key)
  change (⌊(test.precision:ℝ)*score⌋₊:ℝ)/test.precision ≤ B
  by_cases nonneg : 0 ≤ score
  · exact Probe.quantized_ceiling hp nonneg (Probe.discrepancy_box_bound edge req (grid key) B pos printed)
  · have prod : (test.precision:ℝ)*score ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_ge nonneg)
    simpa only [Nat.floor_of_nonpos prod,Nat.cast_zero,zero_div] using pos

end Hierarchy.ProtocolRAM.StripDirectory

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory PurchaseCT
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "wall" => wallCap v.radius (upperBox (publicStages v.W) v.radius)

private theorem wall_nonneg : 0 ≤ wall := by
  have box : 0 ≤ upperBox (publicStages v.W) v.radius := (Nat.cast_nonneg _).trans (le_max_left ..)
  unfold wallCap
  positivity

/-- The last integer key is still billed by the same public ceiling as every
actual stock quote. This also covers padded and unused rows of the ROM. -/
theorem digit_ceiling (j : Fin v.digitRadix) :
    0 ≤ (j.val : ℝ) / v.precision ∧ (j.val : ℝ) / v.precision ≤ wall := by
  have size : j.val ≤ v.precision * (publicStages v.W + v.radius + 2) :=
    Nat.le_of_lt_succ j.isLt
  have h : (j.val : ℝ) ≤ (v.precision : ℝ) * ((publicStages v.W : ℝ) + v.radius + 2) := by
    exact_mod_cast size
  have prec : 0 < (v.precision : ℝ) := Nat.cast_pos.mpr v.clock.precision_pos
  have box : (publicStages v.W : ℝ) ≤ upperBox (publicStages v.W) v.radius := le_max_left ..
  have scaled : (j.val : ℝ) / v.precision ≤ (publicStages v.W : ℝ) + v.radius + 2 :=
    (div_le_iff₀ prec).2 (h.trans_eq (mul_comm ..))
  refine ⟨div_nonneg (Nat.cast_nonneg _) prec.le, scaled.trans ?_⟩
  unfold wallCap
  linarith only [box, Nat.cast_nonneg (α:=ℝ) v.radius,
    abs_nonneg ((⌈Real.sqrt 2*(v.radius:ℝ)⌉:ℤ):ℝ)]

private theorem printed {C H A E : Type*} (length : H → ℝ) (cost : ∀ h,0≤length h ∧ length h≤1)
    (value : A → ℝ) (bounds : ∀ a,0≤value a ∧ value a≤wall) (r : ColumnWires.Role C H (A ⊕ E) k) :
    0 ≤ ColumnWires.quote (v.radius:ℝ) length (LocalCommodity.extraPrice value) r ∧
      ColumnWires.quote (v.radius:ℝ) length (LocalCommodity.extraPrice value) r ≤ wall := by
  have box : 0 ≤ upperBox (publicStages v.W) v.radius := (Nat.cast_nonneg _).trans (le_max_left ..)
  have fixed := printed_bounds (Nat.cast_nonneg v.radius) box length cost (fun _ : A => (0:ℝ))
    (fun _ => ⟨le_rfl,box⟩) r
  cases r with
  | catalyst => exact fixed
  | radius => exact fixed
  | cross => exact fixed
  | horizontal => exact fixed
  | extra x => cases x with
    | inl a => exact bounds a
    | inr _ => exact fixed

variable (P : v.Placement) (z width : ℕ)
local notation "N" => Stages z (2^v.W)

theorem payload_page_ceiling (u : Fin (DeadlineROM.count v.mesh))
    (key : Fin (Fintype.card (PayloadStrip.Quotes N k)) → Fin v.digitRadix) (role : PayloadRole N k) :
    0 ≤ v.payloadPagePrice z width u key role ∧ v.payloadPagePrice z width u key role ≤ wall := by
  simp only [v.payload_page_grid z width u key]
  exact v.printed (PayloadStrip.length N) (fun h => by unfold PayloadStrip.length; split <;> norm_num)
    (payloadGrid v.digitRadix v.precision key) (fun a => v.digit_ceiling (key (Fintype.equivFin _ a))) role

theorem purchased_page_ceiling (u : Fin (DeadlineROM.count v.mesh))
    (key : Fin (Fintype.card (ChainStrip.Axes v.depth k)) → Fin v.digitRadix) (role : PurchasedRole v.depth k) :
    0 ≤ v.purchasedPagePrice width u key role ∧ v.purchasedPagePrice width u key role ≤ wall := by
  simp only [v.purchased_page_grid width u key]
  exact v.printed (ChainStrip.length v.depth) (fun h => by unfold ChainStrip.length; split <;> norm_num)
    (gridAxes v.digitRadix v.precision key) (fun a => v.digit_ceiling (key (Fintype.equivFin _ a))) role

local notation "W" => wordBits z (2^v.W) copies
local notation "H" => v.publicHeader P z width

section
variable (phase trial : ℕ)
local notation "test" => v.payloadTest P z width phase trial
local notation "date" => DeadlineROM.index v.mesh (.outer phase trial)

/-- Price of the actual gated payload failure word in the mounted memory,
including ROM pages whose natural entries exceed the native word size. -/
theorem payload_failure_ceiling_of_resident (state : Memory W) (header : (H).Resident state)
    (i : Fin (test).rows) (key : Fin (Fintype.card (PayloadStrip.Quotes N k)) → Fin v.digitRadix)
    (digits : ∀ j,((test).quoted j).eval state (i.val : Word W) = ((key j).val : Word W)) :
    ((test).failure.value state i : ℝ) / v.precision ≤ wall := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  let : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
  apply resident_ceiling_le (F:=F) (PayloadStrip.wires N k) (PayloadStrip.demands N k) test
    (v.payloadPagePrice z width date) state i key wall v.wall_nonneg v.clock.precision_pos
    (v.payload_page_ceiling z width date key) digits
  exact (header.payload date key).trans
    (congrArg (fun n : ℕ => (n : Word W)) (v.payload_vector_word P z width date key))

theorem payload_failure_ceiling (state : Memory W) (header : (H).Resident state)
    (_maxWord : (H).payload.maxWord < 2^W) (i : Fin (test).rows)
    (key : Fin (Fintype.card (PayloadStrip.Quotes N k)) → Fin v.digitRadix)
    (digits : ∀ j,((test).quoted j).eval state (i.val : Word W) = ((key j).val : Word W)) :
    ((test).failure.value state i : ℝ) / v.precision ≤ wall :=
  v.payload_failure_ceiling_of_resident P z width phase trial state header i key digits
end

section
variable (phase trial slice inner : ℕ)
local notation "test" => v.purchasedTest P z width phase trial slice inner
local notation "date" => DeadlineROM.index v.mesh (.inner phase trial slice inner)

/-- Price of the actual gated purchased failure word with modular ROM entries. -/
theorem purchased_failure_ceiling_of_resident (state : Memory W) (header : (H).Resident state)
    (i : Fin (test).rows) (key : Fin (Fintype.card (ChainStrip.Axes v.depth k)) → Fin v.digitRadix)
    (digits : ∀ j,((test).quoted j).eval state (i.val : Word W) = ((key j).val : Word W)) :
    ((test).failure.value state i : ℝ) / v.precision ≤ wall := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  apply resident_ceiling_le (F:=F) (ChainStrip.wires v.depth k) (ChainStrip.demands v.depth k) test
    (v.purchasedPagePrice width date) state i key wall v.wall_nonneg v.clock.precision_pos
    (v.purchased_page_ceiling width date key) digits
  exact (header.bought date key).trans
    (congrArg (fun n : ℕ => (n : Word W)) (v.purchased_vector_word P z width date key))

theorem purchased_failure_ceiling (state : Memory W) (header : (H).Resident state)
    (_maxWord : (H).bought.maxWord < 2^W) (i : Fin (test).rows)
    (key : Fin (Fintype.card (ChainStrip.Axes v.depth k)) → Fin v.digitRadix)
    (digits : ∀ j,((test).quoted j).eval state (i.val : Word W) = ((key j).val : Word W)) :
    ((test).failure.value state i : ℝ) / v.precision ≤ wall :=
  v.purchased_failure_ceiling_of_resident P z width phase trial slice inner state header i key digits
end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
