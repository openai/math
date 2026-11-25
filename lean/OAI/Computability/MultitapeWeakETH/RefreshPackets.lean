import OAI.Computability.MultitapeWeakETH.RefreshRecipe

/-! # Reconstructing the refresh map input from the two independent node packets -/

namespace OAI.Computability.MultitapeWeakETH.RefreshOperands

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords PairSimulation NodeArguments StackInterpreter PortRefresh NewSlots
open MotifConversion LocalHistory RefreshMapOperands PhaseRecipe
open private packet from OAI.Computability.MultitapeWeakETH.RefreshRecipe
open scoped Fin.CommRing
noncomputable section

set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

variable {A k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {w g : ℕ} (X : State S.portExponent (S.portExponent+g))
local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "Id" => MapFrameFields.FieldId D H
local notation "P" => S.graph.toSlotGraph
local notation "hD" => S.port_order
local notation "hd" => And.right S.degree_bounds
local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)
variable (choice : DyadicRefreshChoice (a₀:=S.degreeExponent 0) (g:=g) X S.graph (Nat.two_pow_pos S.expanderExponent) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
local notation "Y" => dyadicRefreshNext X S.graph hE hC B.refresh hD hd choice
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv S.portExponent) (splitWidths X)
  S.graph hE hC B.refresh choice
variable (p : (X.Base × BitWord g) × Fin (2^S.portExponent))
variable (old : X.network.Half (oldSite X p))
  (parentBits : (dyadicRefreshNext X S.graph (Nat.two_pow_pos S.expanderExponent) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh S.port_order S.degree_bounds.2 choice).network.Half
    (promotedSites p))
local notation "E₀" => entryInput B X choice p old parentBits
local notation "base" => operandBase X p P hD hd internal ⟨0,0⟩ 0 0
local notation "before" => packed X (oldSite X p) old
local notation "after₀" => packed Y (promotedSites p) parentBits

/-- On the native addresses, both old and new ports give exactly the typed refresh
input. Incoming supply fields use the reverse edge's port. -/
theorem packets (wide : 0<w) (oldFit : (before).length ≤ 2^w) (newFit : (after₀).length ≤ 2^w)
    (eval : Expr → Query A → Bits.Word) (x : Query A) (bs : x.2.1 = (before,after₀))
    (port : party B eval x = ⟨p.2⟩)
    (dem : ∀ e, width B eval (.inl (false,e)) x = tally ((E₀).demand e))
    (pay : ∀ e, width B eval (.inr (false,e)) x = tally ((E₀).payload e))
    (addr : ∀ f : Id, eval (baseExpr B f) x = wordBits ((base f : ℕ) : BurstRAM.Word w)) :
    arguments B eval x = MotifFields.fixedInput B.refresh E₀ := by
  have oldData := OperandSpan.node_fields X (oldSite X p) old oldFit
  have newData := OperandSpan.node_fields Y (promotedSites p) parentBits newFit
  apply MotifFields.bufferInput_eq B.refresh _ _ _ _ _ x E₀ port dem pay
  · intro e he
    unfold field
    rw [addr]
    change OperandSpan.span ((x.2.1.1,_),_) = _
    rw [bs]
    apply OperandSpan.span_eq wide
    exact demand_out_read X p P hD hd internal ⟨0,0⟩ 0 0 old parentBits _ oldData e he
  · intro e he
    unfold field
    rw [addr]
    change OperandSpan.span ((x.2.1.2,_),_) = _
    rw [bs]
    apply OperandSpan.span_eq wide
    exact demand_in_read X p P hD hd internal ⟨0,0⟩ 0 0 old parentBits _ newData e he
  · intro e he
    unfold field
    rw [addr]
    change OperandSpan.span ((x.2.1.2,_),_) = _
    rw [bs]
    apply OperandSpan.span_eq wide
    exact supply_out_read X p P hD hd internal ⟨0,0⟩ 0 parentBits _ newData e he
  · intro e he
    unfold field
    rw [addr]
    change OperandSpan.span ((x.2.1.2,_),_) = _
    rw [bs]
    apply OperandSpan.span_eq wide
    exact supply_in_read X p P hD hd internal ⟨0,0⟩ 0 parentBits _ newData e he

end
end OAI.Computability.MultitapeWeakETH.RefreshOperands
