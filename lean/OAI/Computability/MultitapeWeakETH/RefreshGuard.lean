import OAI.Computability.MultitapeWeakETH.RefreshDiagonal

/-! # Correctness of the refresh guard for the two independently stored halves -/

namespace OAI.Computability.MultitapeWeakETH.RefreshOperands

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords PortRefresh OperandInputs PhaseRecipe PairSimulation NodeArguments
open RefreshMapOperands NewSlots NetworkKernel StackInterpreter
open scoped Fin.CommRing
noncomputable section

set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

variable {A : Type} {a b g dH w : ℕ} (X : State a (a+g)) (v : (X.Base × BitWord g) × Fin (2^a))
  (P : SlotGraph (Fin (2^a)) dH) (hD : 1 < 2^a) (hd : dH+1 ≤ 2^b)
  (internal : X.Base × BitWord g → Fin (2^a) × Fin dH → ℕ)
  (old : X.network.Half (oldSite X v))
  (new : (newState X P hD hd internal).network.Half (promotedSites v))
local notation "Y" => newState X P hD hd internal
local notation "G" => splitSlots X
local notation "port" => bitWordFinEquiv a
local notation "ws" => groupedWidths port (splitWidths X)
local notation "perm" => oldPortMatching G port
local notation "outer" => segments X v P hD hd internal new
local notation "arg" => oldHalf X v old
local notation "bs" => packed X (oldSite X v) old
local notation "cs" => packed Y (promotedSites v) new
local notation "wo" => ws (v,Prod.snd v)
local notation "wi" => ws (Equiv.symm perm (v,Prod.snd v))
local notation "Z" => (⟨0,0⟩ : Arena)

theorem diagonal_test (I : Input) (C : LevelRecipe.Context w) (T U : IncidenceDirectory w)
    (q : Fin 8 → W w) (demand term : W w)
    {fit : Fintype.card X.Base*2^a*2^g*2^a ≤ 2^w}
    (args : Describes I C.pub C.state C.memory X v P hD hd internal Z 0 0 T U q demand term)
    (oldRows : T.ActualColumns X C.memory) (newRows : U.ActualColumns Y C.memory)
    (data : SegmentFields X q fit C.memory) (degree : 2^a < 2^w)
    (eval : Expr → Query A → Bits.Word) (x : Query A)
    (exec : ∀ e, eval e x = wordBits (C.eval e)) (rows : x.2.1 = (bs,cs))
    (oldFits : (bs).length ≤ 2^w) (newFits : (cs).length ≤ 2^w)
    (cap : X.maxWireWidth ≤ x.2.2.length) (fits : X.maxWireWidth < 2^w) :
    let f := DiagonalFrame.fields (2^a) (refreshSlots hd (.inl 0)) I
    (compareSpan eval (f 0) (f 1) (f 2) x && compareSpan eval (f 3) (f 4) (f 5) x) =
      decide (portDiagonal perm ws v.1 v.2 arg outer = (1:ℤ)) := by
  intro f
  have wide : 0 < w := by
    by_contra! bad
    rw [show w=0 by omega,pow_zero] at degree
    omega
  have ptr := DiagonalFrame.values X v P hD hd internal Z 0 0 T U q demand term I C.pub C.state C.memory
    args oldRows newRows data degree
  have oldData := OperandSpan.node_fields X (oldSite X v) old oldFits
  have newData := OperandSpan.node_fields Y (promotedSites v) new newFits
  let oldBase (dir : Bool) := (Z).fieldAddress X (oldSite X v) 0 dir v.2
  let newBase (dir : Bool) := (Z).fieldAddress Y (promotedSites v) 0 dir (refreshSlots hd (.inl 0)) +
    externalOffset X v dir v.2
  have ol : wo ≤ X.maxWireWidth := X.width_le_maxWireWidth _
  have il : wi ≤ X.maxWireWidth := X.width_le_maxWireWidth _
  let oo : Fin wo → Bool := (arg).1 (v,v.2) rfl
  let eo : Fin wo → Bool := (outer).1 v.2
  let oi : Fin wi → Bool := incomingHalf (R:=ℤ) perm ws v.1 v.2 v.2 arg
  let ei : Fin wi → Bool := (outer).2 v.2
  have out : compareSpan eval (f 0) (f 1) (f 2) x = decide (oo=eo) := by
    refine compareSpan_eq eval wide x C exec _ _ _ (oldBase false) (newBase false) (ptr 0) (ptr 2) (ptr 1)
      (ol.trans_lt fits) (ol.trans cap) ((arg).1 (v,v.2) rfl) ((outer).1 v.2) ?_ ?_
    · rw [rows]; exact old_out_read X v Z 0 old _ oldData v.2
    · rw [rows]; exact external_out_read X v P hD hd internal Z 0 new _ newData v.2
  have inc : compareSpan eval (f 3) (f 4) (f 5) x =
      decide (oi=ei) := by
    refine compareSpan_eq eval wide x C exec _ _ _ (oldBase true) (newBase true) (ptr 3) (ptr 5) (ptr 4)
      (il.trans_lt fits) (il.trans cap) (incomingHalf (R:=ℤ) perm ws v.1 v.2 v.2 arg) ((outer).2 v.2) ?_ ?_
    · rw [rows]; exact old_in_read X v Z 0 old _ oldData v.2
    · rw [rows]; exact external_in_read X v P hD hd internal Z 0 new _ newData v.2
  rw [out,inc]
  unfold portDiagonal segmentTest
  change (decide (oo=eo) && decide (oi=ei)) = decide ((@ite ℤ (oo=eo) (Classical.propDecidable _) 1 0) * (@ite ℤ (ei=oi) (Classical.propDecidable _) 1 0) = 1)
  by_cases ho : oo=eo <;> by_cases hi : oi=ei
  · simp only [ho,hi,decide_true,Bool.and_self,ite_true,mul_one]
  · simp only [decide_eq_true ho,decide_eq_false hi,Bool.and_false,ite_eq_left ho,ite_eq_right (Ne.symm hi),mul_zero,zero_ne_one,decide_false]
  · simp only [decide_eq_false ho,Bool.false_and,ite_eq_right ho,zero_mul,zero_ne_one,decide_false]
  · simp only [decide_eq_false ho,Bool.false_and,ite_eq_right ho,zero_mul,zero_ne_one,decide_false]

end
end OAI.Computability.MultitapeWeakETH.RefreshOperands
