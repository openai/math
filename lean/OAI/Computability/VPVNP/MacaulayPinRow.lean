import OAI.Computability.VPVNP.MacaulayAppendedPower

/-! # Complete physical Macaulay read for a coordinate-pin row

The ordinal scans produce the two monomials and their divisibility flag.
On a divisible column the coefficient program reads the nominated affine
pin and the residual exponent. Otherwise the phase emits its stored zero
scalar. Cleanup restores the common reader bank in both cases.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.Arms

open RAMTape BurstRAM MacaulayRowDispatch RadicalCertificate RadicalCertificate.MonomialIndex SliceArithmetic
open UniversalCountStack (digits)

set_option synthInstance.maxSize 3000

variable {p e w v : ℕ} [Fact p.Prime] [NeZero e] {c : Vector p e}
variable {F ι : Type*} [Field F] [Algebra (ZMod p) F]

theorem pin_row_plan (P : ReaderPlan) (Q : QueryData P.arity (P.equations+P.pins) F)
    (h : P.Covers Q) {E V : ℕ} (he : e ≤ E) (hv : v ≤ V) (sp ex : ℕ)
    (hw : P.wordWidth ≤ w) (working : SliceArithmetic.Word.workingWidth p ≤ v)
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (system : ι → MvPolynomial (Fin P.arity) F)
    (pins : Finset (Fin P.arity)) (values : Fin P.arity → F) (row : Fin P.arity)
    (L : JointScalar.Leaf.Layout) (hlayout : JointScalar.Leaf.bankSize L w (P.arity*w) ≤ sp)
    (rs : Reg → BurstRAM.Word w) (hrow : (rs (outReg 1)).val=row.val)
    (source : Fin (size P.arity Q.multiplierDegree)) (column : Fin (size P.arity Q.columnDegree))
    (hsource : (rs (outReg 2)).val=source.val) (hcolumn : (rs (outReg 3)).val=column.val) :
    let data := BaseAdvice.inputs Q
    let constants := BaseAdvice.scalars c v
    let aux := coefficientAdvice L w v pins (fun j => AffinePin.Query.encode φ (values j))
    let a := enumeration P.arity Q.multiplierDegree source
    let b := enumeration P.arity Q.columnDegree column
    let val := if a.val ≤ b.val then AffinePin.Query.encode φ
        ((SliceGeometry.pinnedEquations system pins values (.inr row)).coeff (b.val-a.val)) else 0
    ∃ n ≤ P.armTime E V w sp ex,
      (phase false (Pin.machine (K := CoefficientPort) Function.Embedding.inr)).BoundedRun (P.armSpace E V w sp) n
        (frame rs [] (storage w data blank blank constants aux))
        (frame rs (Engine.scalar v val) (storage w data blank blank constants aux)) := by
  intro data constants aux a b val
  let A := P.live E V w sp
  let S := P.armSpace E V w sp
  let d := addressed rs (data false)
  let ords : PairCall.Ordinals d := fun b => match b with
    | false => source | true => column
  have hk (j : Bool) : d.ordinal j = (ords j).val := by cases j; exact hsource; exact hcolumn
  have hL : d.degree false ≤ P.source := h.degrees.2.1.trans (le_max_right ..)
  have hD : d.degree true ≤ P.column := h.degrees.2.2
  have hwidth := (P.pairWidth_le d rfl hL hD (le_max_left ..) (Nat.zero_le _)).trans hw
  obtain ⟨fit,_⟩ := PairCall.fits_of_width d ords hwidth
  obtain ⟨live,cap,_⟩ := P.leaf_bounds w sp ex he hv d rfl hL hD
  have hpre : Preload (w := w) A data constants aux :=
    coefficientAdvice_preload rfl he hv hlayout pins _ data (fun _ => rfl) constants
      (fun bit => (Engine.scalar_length v (if bit then (1 : Scalar c) else 0)).le)
  have pinReady := (coefficientAdvice_loaded L w v pins (fun j => AffinePin.Query.encode φ (values j))).2
  have hw1 : 1 ≤ w := (by decide : 1≤2).trans (P.dispatchWidth.2.2.trans hw)
  let delta := b.val-a.val
  let scalar := AffinePin.Query.encode φ ((SliceGeometry.pinnedEquations system pins values (.inr row)).coeff delta)
  let pack := selected false (PairCall.difference w a b)
  let flag := selected false (digits w (decide (a.val ≤ b.val)).toNat)
  let leaf := Pin.machine (K := CoefficientPort) Function.Embedding.inr
  have dfit (j : Fin P.arity) : delta j < 2^w := by
    have limit : Q.columnDegree+1 < 2^w := (fit true).base_lt
    exact (Nat.sub_le ..).trans_lt ((b.encode j).isLt.trans limit)
  have yes (_ : a.val ≤ b.val) : ∃ n ≤ Pin.cost P.arity e w v, ∃ rest : List Bool, rest.length ≤ P.arity*w ∧
      leaf.BoundedRun S n (frame rs [] (storage w data pack flag constants aux))
        (frame rs (Engine.scalar v scalar) (storage w data (selected false rest) flag constants aux)) := by
    have hbuf (bit : Bool) : (pack bit).length ≤ A := by
      cases bit <;> simp [pack,selected,blank]
      exact live.2.2.1
    have hflag (bit : Bool) : (flag bit).length ≤ A := by
      cases bit <;> simp [flag,selected,blank]
      exact live.1
    have hf := frame_bound rs [] data pack flag constants aux hpre.words (by simp) hpre.arity hbuf hflag hpre.scalars hpre.payload
    have room (z) : (frame rs [] (storage w data pack flag constants aux) z).length+(5*w+2) ≤ S :=
      (Nat.add_le_add_right ((hf z).trans (le_max_left ..)) _).trans cap.2.2.2.2
    have haS : AffinePin.Query.space P.arity e w v ≤ S := live.2.2.2.2.2.trans
      ((Nat.le_add_right A _).trans cap.2.2.1)
    obtain ⟨n,hn,hr⟩ := Pin.coefficient φ system (K := CoefficientPort) Function.Embedding.inr
      hw1 working pins values row delta dfit rs hrow data pack flag constants aux
      (by rw [show pack false=PairCall.difference w a b from Function.update_self ..]; rfl)
      pinReady haS room
    have eq : Function.update pack false [] = selected false [] := Function.update_idem ..
    refine ⟨n,hn,[],by simp,?_⟩
    rw [← eq]
    exact hr
  have hlen : (Engine.scalar v scalar).length ≤ A := (Engine.scalar_length v scalar).le.trans live.2.2.2.1
  obtain ⟨n,hn,run⟩ := equation_execution rs data constants aux hpre hw1 leaf (Engine.scalar v scalar) hlen
    (Pin.cost P.arity e w v) ords hk fit cap.1 cap.2.2.2.1 yes
  have scan := (P.scan_bounds w A d rfl hL hD).1
  have hp : Pin.cost P.arity e w v ≤ P.scalarTime E V w ex :=
    (Nat.add_le_add_left (ReaderPlan.pin_cost_mono P.arity w he hv) _).trans ((le_max_left ..).trans (le_max_right ..))
  have post : postTicks A P.arity w (Pin.cost P.arity e w v) ≤ postTicks A P.arity w (P.scalarTime E V w ex) := by
    unfold postTicks; gcongr
  refine ⟨n,hn.trans (Nat.add_le_add scan post),?_⟩
  change (phase false leaf).BoundedRun S n _ (frame rs (if a.val ≤ b.val then Engine.scalar v scalar else constants false) _) at run
  by_cases div : a.val ≤ b.val
  · simpa only [val,div,ite_true,scalar] using run
  · have hz : constants false = Engine.scalar v (0 : Scalar c) := by simp [constants,BaseAdvice.scalars]
    simpa only [val,div,ite_false,hz] using run

end RankQuery.Stack.MacaulayRead.Arms

end VPVNP
end Computability
end OAI
