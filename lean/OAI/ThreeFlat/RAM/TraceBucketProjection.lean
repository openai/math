import OAI.ThreeFlat.RAM.TraceBucketAtom

namespace OAI
/-! # Projecting the selected native term of an initial physical bucket -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing

variable {W n : ℕ}

def operands (e : Fin n → Term W 1 4) (data : Fin 1 → Word W) (m : Memory W)
    (v : Fin 4 → Word W) : Fin n → ℕ := fun j => ((e j).eval data m v).val

private theorem natural_term (e : Fin n → Term W 1 4) (f : Formula n) (data : Fin 1 → Word W)
    (m : Memory W) (v : Fin 4 → Word W)
    (fits : f.Fits W (fun _ => (data 0).val) (fun i => (m i).val) (operands e data m v)) :
    ((f.compile (fun _ => (0 : Fin 1))).instantiate e).eval data m v =
      (f.natural W (fun _ => (data 0).val) (fun i => (m i).val) (operands e data m v) : Word W) := by
  rw [Term.eval_instantiate,Formula.eval_compile]
  simpa [operands,Function.comp_def] using
    f.value_eq_natural (fun _ => (data 0).val) (fun i => (m i).val) (operands e data m v) fits

/-- Evaluate only the row comparison. The two native programs stay opaque
even when the branch that was skipped is a large instantiated formula. -/
private theorem chooseRow (data : Fin 1 → Word W) (m : Memory W) (v : Fin 4 → Word W)
    (cut : ℕ) (bound : cut<2^W) (yes no : Term W 1 4) :
    (Term.select .lt (.result 0) (.literal (cut:Word W)) yes no).eval data m v =
      if (v 0).val<cut then yes.eval data m v else no.eval data m v := by
  rw [Term.eval_select,Term.eval_literal]
  simp only [Term.eval,Comparison.test,Fin.lt_def,Fin.val_cast_of_lt bound,decide_eq_true_eq]

set_option maxHeartbeats 400000 in
/-- Each branch may read a different subset of memory. Word-fit
certificates are only required at the branch that supplies the result. -/
theorem selected_word (s : Layout) (data : Fin 1 → Word W) (m : Memory W) (v : Fin 4 → Word W)
    (shapeFit : s.relays+s.gates+s.tags<2^W) :
    let natData := fun _ : Param => (data 0).val
    let natMem := fun i => (m i).val
    let relay := operands (relayArgs s) data m v
    let original := operands (origArgs s) data m v
    let comparison := operands (cmpArgs s) data m v
    let padding := operands (holeArgs s) data m v
    let row := (v 0).val
    (if row<s.relays then Diagonal.TraceBucketRelay.formula.Fits W natData natMem relay
     else if row<s.relays+s.gates then TraceBucketFields.original.Fits W natData natMem original
     else if row<s.relays+s.gates+s.tags then TraceBucketFields.compare.Fits W natData natMem comparison
     else TraceBucketFields.hole.Fits W natData natMem padding) →
    (program W s).eval data m v =
      ((if row<s.relays then Diagonal.TraceBucketRelay.formula.natural W natData natMem relay
        else if row<s.relays+s.gates then TraceBucketFields.originalNat natMem original
        else if row<s.relays+s.gates+s.tags then TraceBucketFields.compareNat comparison
        else if padding 0<3 then 2+padding 1+padding 2+padding 3 else
          if padding 4=0 then padding 5 else padding 6) : Word W) := by
  intro natData natMem relay original cmp hole row fit
  have cut₀ : s.relays<2^W := by omega
  have cut₁ : s.relays+s.gates<2^W := by omega
  unfold program
  rw [chooseRow data m v _ cut₀, chooseRow data m v _ cut₁, chooseRow data m v _ shapeFit]
  dsimp only [row] at fit ⊢
  by_cases h : (v 0).val<s.relays
  · simp only [h,ite_true] at fit ⊢
    exact natural_term (relayArgs s) Diagonal.TraceBucketRelay.formula data m v fit
  · by_cases g : (v 0).val<s.relays+s.gates
    · simp only [h,g,ite_false,ite_true] at fit ⊢
      simpa only [TraceBucketFields.original_nat] using natural_term (origArgs s) TraceBucketFields.original data m v fit
    · by_cases a : (v 0).val<s.relays+s.gates+s.tags
      · simp only [h,g,a,ite_false,ite_true] at fit ⊢
        simpa only [TraceBucketFields.compare_nat] using natural_term (cmpArgs s) TraceBucketFields.compare data m v fit
      · simp only [h,g,a,ite_false] at fit ⊢
        have eqn := natural_term (holeArgs s) TraceBucketFields.hole data m v fit
        rw [TraceBucketFields.hole_nat] at eqn
        change _ = (((if hole 0<3 then 2+hole 1+hole 2+hole 3
          else if hole 4=0 then hole 5 else hole 6) : ℕ) : Word W) at eqn
        by_cases field : hole 0<3 <;> by_cases valid : hole 4=0 <;>
          simpa [field,valid,Nat.cast_add] using eqn

end ThreeFlat.RAM.TraceBucketAtom

end OAI
