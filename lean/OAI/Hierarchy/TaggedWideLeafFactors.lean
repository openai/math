import OAI.Hierarchy.TaggedWideLeafFiniteSums

namespace OAI
/-! # Summing the paid cuts, private endpoint tests and decoded output -/

noncomputable section
namespace Hierarchy.Tagged.WideStack.Leaf
open ProtocolStackContraction
open scoped Classical BigOperators

variable {F : Type*} [CommSemiring F] {T E H P : Type}
    [Fintype T] [Fintype E] [Fintype H] [Fintype P]
    (b : T → Board F) (cap : E → ℕ)
    (live : ∀ t, Edge (b t).counts → Fin (b t).width → Prop)

private theorem gate_product (on good : Prop) [Decidable on] [Decidable good] (charge eqv dec val : F) :
    charge*((if on then 1 else 0)*((if good then eqv else 0)*(dec*val))) =
      charge*(if on then dec*(if good then eqv*val else 0) else 0) := by
  by_cases occupied : on <;> by_cases fits : good <;> simp [occupied,fits,mul_left_comm,mul_comm]

/-- The workspace integral with an arbitrary site term. Each cut is closed on
its real two-ended board. The decoder's fibre sum determines the output word
at which the remaining site term is evaluated. -/
theorem close_factors
    (fits : PrivatePorts cap → Prop) [DecidablePred fits] (weight : PrivatePorts cap → F)
    (decode : (∀ t, (b t).Slots) → (P → Bool))
    (readPlane : (∀ t, (b t).Slots) → (P → Bool) → F)
    (cut : T → (Pin b cap H P → Bool) → F)
    (pad privateGate plane site : (Pin b cap H P → Bool) → F)
    (cuts : ∀ z y h p t, cut t (write b cap z y h p)=(b t).settings.close (z t))
    (padded : ∀ z y h p, pad (write b cap z y h p)=if supported b live z then 1 else 0)
    (privateRead : ∀ z y h p, privateGate (write b cap z y h p)=if fits y then weight y else 0)
    (planeRead : ∀ z y h p, plane (write b cap z y h p)=readPlane z p)
    (inputs : Fintype (Pin b cap H P → Bool)) (labels : Fintype (∀ t,(b t).Labels))
    (privates : Fintype (PrivatePorts cap)) (histories : Fintype (H → Bool)) (planes : Fintype (P → Bool))
    (readSum : ∀ z (f : (P → Bool) → F), sumWith planes (fun p=>readPlane z p*f p)=f (decode z)) :
    sumWith inputs (fun d=>(∏ t,cut t d)*(pad d*(privateGate d*(plane d*site d)))) =
      sumWith labels (fun a=> if bounded b live a then sumWith privates (fun y=>
        weight y*(if fits y then sumWith histories (fun h=>
          site (write b cap (placed b a) y h (decode (placed b a)))) else 0)) else 0) := by
  let phi (z : ∀ t,(b t).Slots) (y : PrivatePorts cap) (h : H→Bool) (p : P→Bool) :=
    readPlane z p*(if fits y then weight y*site (write b cap z y h p) else 0)
  let gate (d : Pin b cap H P → Bool) := (∏t,cut t d)*(pad d*(privateGate d*(plane d*site d)))
  have localRead z y h p : gate (write b cap z y h p) =
      (∏t,(b t).settings.close (z t))*(if supported b live z then phi z y h p else 0) := by
    simp only [gate,phi,cuts,padded,privateRead,planeRead]
    exact gate_product (supported b live z) (fits y) _ _ _ _
  refine (close_workspace_fintypes b cap live phi gate localRead inputs labels privates histories planes).trans ?_
  apply Finset.sum_congr rfl
  intro a _
  by_cases keep : bounded b live a
  · simp only [keep,ite_true]
    apply Finset.sum_congr rfl
    intro y _
    let z := placed b a
    have readAt (h : H → Bool) : sumWith planes (phi z y h) =
        if fits y then weight y*site (write b cap z y h (decode z)) else 0 :=
      readSum z (fun p=>if fits y then weight y*site (write b cap z y h p) else 0)
    change (@Finset.univ (H → Bool) histories).sum (fun h=>sumWith planes (phi z y h))=_
    simp_rw [readAt]
    by_cases ok : fits y <;> simp [ok,sumWith,Finset.mul_sum,z]
  · simp [keep]

end Hierarchy.Tagged.WideStack.Leaf

end
end OAI
