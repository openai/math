import OAI.Computability.VPVNP.MacaulayEntryExecution
import OAI.Computability.VPVNP.MacaulayBaseAdvice

/-! # Native read of an appended powered-monomial matrix row

The source and column ordinals have already been produced by the numeric
row decoder. The complete powered phase compares both monomials, returns
the field encoding of the formal coefficient, and restores all work ports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.Arms

open RAMTape BurstRAM MacaulayRowDispatch RadicalCertificate.MonomialIndex

variable {K : Type} [DecidableEq K] {p e w A S v : ℕ} [Fact p.Prime] {c : SliceArithmetic.Vector p e}

/-- The suffix of the augmented matrix consists of monomials raised to the
certificate power. This is the coefficient returned by its physical branch. -/
theorem appended_power (rs : Reg → Word w) (data : Bool → PairCall.Inputs)
    (constants : Bool → List Bool) (aux : Stacks K)
    (pre : Preload (w := w) A data constants aux) (hw : 1≤w)
    (source : Fin (size (data true).arity ((data true).degree false)))
    (column : Fin (size (data true).arity ((data true).degree true)))
    (hsource : (rs (outReg 2)).val=source.val) (hcolumn : (rs (outReg 3)).val=column.val)
    (hm : (data true).mark=0) (hc : ∀ bit : Bool, constants bit = Engine.scalar v (if bit then (1 : Scalar c) else 0))
    (hwidth : PairCall.requiredWidth (data true) ≤ w)
    (hspace : PairCall.poweredSpace w A ≤ S) (htrans : transient A (data true).arity w ≤ S) :
    ∃ n ≤ PairCall.scanClock w A (data true) + PairCall.powerClock (data true).arity w A +
      PairCall.clearCost w + postTicks A (data true).arity w (5*A+2),
      (phase true (emit true)).BoundedRun S n (frame rs [] (storage w data blank blank constants aux))
        (frame rs (Engine.scalar v (powerEntry (K := Scalar c) (data true).scale (indexedDigits source) column))
          (storage w data blank blank constants aux)) := by
  let d := addressed rs (data true)
  let ords : PairCall.Ordinals d := fun b => match b with
    | false => source
    | true => column
  have hk (b : Bool) : d.ordinal b=(ords b).val := by cases b; exact hsource; exact hcolumn
  obtain ⟨fit,efit⟩ := PairCall.fits_of_width d ords hwidth
  obtain ⟨n,hn,run⟩ := powered_execution rs data constants aux pre hw ords hk fit efit hspace htrans
  let flag := PairCall.powerMatch d (PairCall.monomial d ords false) (PairCall.monomial d ords true)
  have hval : constants flag = Engine.scalar v
      (powerEntry (K := Scalar c) (data true).scale (indexedDigits source) column) := by
    rw [hc]
    exact congrArg (Engine.scalar v) (PairCall.powerMatch_entry (K := Scalar c) d ords hm)
  change (phase true (emit true)).BoundedRun S n _ (frame rs (constants flag) _) at run
  exact ⟨n,hn,hval ▸ run⟩

/-- Specialization to the actual ordinary-reader advice and its uniform
budget. Only the two decoded ordinals depend on the selected matrix entry. -/
theorem appended_power_plan {F : Type*} (P : ReaderPlan) (Q : QueryData P.arity (P.equations+P.pins) F)
    (h : P.Covers Q) {E V : ℕ} (he : e ≤ E) (hv : v ≤ V) (sp ex : ℕ)
    (hw : P.wordWidth ≤ w) (rs : Reg → Word w) (aux : Stacks K)
    (pre : Preload (w := w) (P.live E V w sp) (BaseAdvice.inputs Q) (BaseAdvice.scalars c v) aux)
    (source : Fin (size P.arity Q.pointBound)) (column : Fin (size P.arity Q.columnDegree))
    (hsource : (rs (outReg 2)).val = source.val) (hcolumn : (rs (outReg 3)).val = column.val) :
    ∃ n ≤ P.armTime E V w sp ex, (phase true (emit true)).BoundedRun (P.armSpace E V w sp) n
      (frame rs [] (storage w (BaseAdvice.inputs Q) blank blank (BaseAdvice.scalars c v) aux))
      (frame rs (Engine.scalar v (powerEntry (K := Scalar c) Q.power (indexedDigits source) column))
        (storage w (BaseAdvice.inputs Q) blank blank (BaseAdvice.scalars c v) aux)) := by
  let A := P.live E V w sp
  let d := BaseAdvice.inputs Q true
  have hL : d.degree false ≤ P.source := h.points_le.trans (le_max_left ..)
  have hD : d.degree true ≤ P.column := h.degrees.2.2
  have hscaled : Q.power ≤ Q.power*Q.fieldOrder := Nat.le_mul_of_pos_right _ ((by decide : 0 < 2).trans_le h.order_two)
  have hw' := (P.pairWidth_le d rfl hL hD (hscaled.trans (h.targetParams .frobenius).1) (Nat.zero_le _)).trans hw
  obtain ⟨_,hs,_⟩ := P.leaf_bounds w sp ex he hv d rfl hL hD
  obtain ⟨steps,ht,run⟩ := appended_power rs (BaseAdvice.inputs Q) (BaseAdvice.scalars c v) aux pre
    ((by decide : 1≤2).trans (P.dispatchWidth.2.2.trans hw)) source column hsource hcolumn rfl (fun _ => rfl)
    hw' hs.2.1 hs.2.2.2.1
  have hscan := (P.scan_bounds w A d rfl hL hD).2.1
  have hpost : postTicks A P.arity w (5*A+2) ≤ postTicks A P.arity w (P.scalarTime E V w ex) := by
    unfold postTicks
    rw [max_self]
    exact Nat.add_le_add_right (Nat.add_le_add_left (le_max_left ..) _) _
  exact ⟨steps, ht.trans (Nat.add_le_add hscan hpost), run⟩

end RankQuery.Stack.MacaulayRead.Arms

end VPVNP
end Computability
end OAI
