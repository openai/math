import OAI.Computability.MultitapeWeakETH.RefreshRecipe

/-! # Reading actual refresh operand locations and widths from the selected pass -/

namespace OAI.Computability.MultitapeWeakETH.RefreshOperands

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords PortRefresh OperandInputs PhaseRecipe PairSimulation.NodeArguments
open DescriptorSpace NewSlots StackInterpreter TerminalWords
open private finitePort finitePort_eq widthExpr from OAI.Computability.MultitapeWeakETH.RefreshRecipe
open scoped Fin.CommRing
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

private theorem capped_word {v cap w : ℕ} (fits : v < 2^w) (bound : v ≤ cap) :
    capped (wordBits (word (bits:=w) v),tally cap) = tally v := by
  simp only [capped,NativeGrid.value_native,tally_length]
  change tally (min (v % 2^w) cap) = tally v
  rw [Nat.mod_eq_of_lt fits,Nat.min_eq_left bound]

variable {A k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {w g : ℕ} (L : Layout) (i n : ℕ) (X : State S.portExponent (S.portExponent+g))
local notation "s₀" => RefreshBlockPlan.shape B
local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "Id" => MapFrameFields.FieldId D H
local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)
variable (choice : DyadicRefreshChoice (a₀ := S.degreeExponent 0) (g := g) X S.graph (Nat.two_pow_pos S.expanderExponent) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
local notation "Y" => dyadicRefreshNext X S.graph hE hC B.refresh S.port_order (And.right S.degree_bounds) choice
local notation "U" => packedIncidence L w i (X.positions*D)
local notation "V" => packedIncidence L w (i+1) (State.positions Y*2^(S.degreeExponent 0))
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv S.portExponent) (splitWidths X)
  S.graph hE hC B.refresh choice
local notation "demand" => blockDemandWidths (splitSlots X) (bitWordFinEquiv S.portExponent) (splitWidths X)
local notation "Pl" => Allocation.plan X (S.degreeExponent 0) H (LevelRecipe.Shape.ties s₀)
  (LevelRecipe.Shape.stride s₀) (arrayBase L i)
variable (p : (X.Base × BitWord g) × Fin (2^S.portExponent)) (C : LevelRecipe.Context w)
local notation "nominal" => MapFrameFields.nominal (demand (Prod.fst p)) (Subtype.val (choice (Prod.fst p)))
local notation "base" => RefreshMapOperands.operandBase X p S.graph.toSlotGraph S.port_order
  (And.right S.degree_bounds) internal ⟨0,0⟩ 0 0

private theorem width_read {f : Id} {ctx : A} {old new : Bits.Word} {cap v : ℕ} {eval : Expr → Query A → Bits.Word}
    (run : eval (widthExpr B f) (encode ctx C old new cap) = wordBits (C.eval (widthExpr B f)))
    (val : C.eval (widthExpr B f) = word v) (fits : v < 2^w) (bound : v ≤ cap) :
    width B eval f (encode ctx C old new cap) = tally v :=
  (congrArg (fun z => capped (z,tally cap)) (run.trans (congrArg wordBits val))).trans (capped_word fits bound)

/-- The compiled recipe yields every field's physical base and nominal length. Widths
are read for all fields, including those absent at the selected party. -/
theorem readback (ctx : A) (old new : Bits.Word) (cap : ℕ) (eval : Expr → Query A → Bits.Word)
    (run : ∀ e, eval e (encode ctx C old new cap) = wordBits (C.eval e))
    (stored : RefreshPayloadHistory.Data B L i n X choice C.memory)
    (state : C.state.val = levelStart L i) (succ : (C.pub 2).val = levelStart L (i+1))
    (site : (C.pub 0).val = (sites X.baseIndex (bitWordFinEquiv g) p).val) (lanes : 2^g < 2^w)
    (dFit : D < 2^w) (limit : ∀ f : Id, nominal f ≤ cap) (fits : ∀ f : Id, nominal f < 2^w) :
    let x := encode ctx C old new cap
    party B eval x = ⟨p.2⟩ ∧ (∀ f : Id, width B eval f x = tally (nominal f)) ∧
      ∀ f : Id, eval (baseExpr B f) x = wordBits ((base f : ℕ) : BurstRAM.Word w) :=
  let args : Describes (input s₀) C.pub C.state C.memory X p S.graph.toSlotGraph S.port_order
      S.degree_bounds.2 internal ⟨0,0⟩ 0 0 U V ((Pl).scratch w) (word (Pl).demand) (word (Pl).term) :=
    describes s₀ X p S.graph.toSlotGraph S.port_order S.degree_bounds.2 internal
    U V C stored.geometry state succ site lanes
  let pj := ArgumentSite.portIndex_eval X p C.pub C.state C.memory (input s₀).parent.siteOrd
    (input s₀).lanes args.site args.lanes dFit
  let address (f : Id) := MapFrameFields.base_eval X p S.graph.toSlotGraph S.port_order S.degree_bounds.2 internal
    ⟨0,0⟩ 0 0 U V ((Pl).scratch w) (word (Pl).demand) (word (Pl).term) C.pub C.state C.memory (input s₀)
    args stored.old.actual stored.new.actual stored.stored.segments dFit f
  let length (f : Id) := MapFrameFields.storedWidth_eval B X choice p ⟨0,0⟩ 0 0 U V (RefreshBlockPlan.order B)
    (arrayBase L i) (s₀).stride C.pub C.state C.memory (input s₀) args stored.stored dFit f
  ⟨(congrArg (finitePort S.portExponent) ((run (siteExpr B)).trans (congrArg wordBits pj))).trans
      (finitePort_eq p.2 dFit.le),
    fun f => width_read (A:=A) B C (eval:=eval) (ctx:=ctx) (old:=old) (new:=new) (cap:=cap) (v:=nominal f) (f:=f) (run (widthExpr B f)) (length f) (fits f) (limit f),
    fun f => (run (baseExpr B f)).trans (congrArg wordBits (address f))⟩
end
end OAI.Computability.MultitapeWeakETH.RefreshOperands
