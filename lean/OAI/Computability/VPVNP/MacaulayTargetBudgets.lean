import OAI.Computability.VPVNP.MacaulayLeafBudgets
import OAI.Computability.VPVNP.RankCoordinateTargetRead

/-! # The staged target reader uses the common raw matrix-reader budgets -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.ReaderPlan

open RankQuery.Stack Coordinate

variable {F : Type*}

/-- Both the prepared target row and the original matrix fit the same
clock and space caps, including the target's native flag-selected copy. -/
theorem target_bounds {P : ReaderPlan} {S : QueryData P.arity (P.equations+P.pins) F}
    (h : P.Covers S) (op : QueryData.Operation P.arity) (d : PairCall.Inputs)
    (ht : d.arity=P.arity) (hL : d.degree false=S.pointBound) (hD : d.degree true=S.columnDegree)
    (hs : d.scale=PairCall.targetScale S op) (hm : d.mark=PairCall.targetMark op)
    {E V e v w : ℕ} (he : e≤E) (hv : v≤V) (hw : P.wordWidth≤w) (signedSpace signedExp : ℕ) :
    let b := P.live E V w signedSpace
    PairCall.requiredWidth d ≤ w ∧ w ≤ b ∧ d.arity ≤ b ∧ max b (e*v) ≤ b ∧
      TargetRead.clock w b e v d ≤ P.readTime E V w signedSpace signedExp ∧
      TargetRead.space w b e v ≤ P.armSpace E V w signedSpace := by
  intro b
  have hl : d.degree false ≤ P.source := hL ▸ h.points_le.trans (le_max_left ..)
  have hd : d.degree true ≤ P.column := hD ▸ h.degrees.2.2
  have hfit := P.pairWidth_le d ht hl hd (hs ▸ (h.targetParams op).1) (hm ▸ (h.targetParams op).2)
  have hab := P.leaf_bounds w signedSpace signedExp he hv d ht hl hd
  have hword := hab.1.1
  have har := hab.1.2.1
  have hscalar : e*v ≤ b := hab.1.2.2.2.1
  have hscan := (P.scan_bounds w b d ht hl hd).2.1
  have hwork := (P.scan_bounds w b d ht hl hd).2.2.2
  have hbank : w ≤ b := hword
  have hbase : d.arity ≤ b := ht ▸ har
  refine ⟨hfit.trans hw,hbank,hbase,max_le le_rfl hscalar,?_,?_⟩
  · have copyBound : 5*(e*v)+2 ≤ max (5*b+2) (P.scalarTime E V w signedExp) :=
      (Nat.add_le_add_right (Nat.mul_le_mul_left 5 hscalar) 2).trans (le_max_left ..)
    change _ ≤ MacaulayRowDispatch.ticks w + (4 + (P.scanTime w b + MacaulayRead.Arms.postTicks b P.arity w _))
    unfold TargetRead.clock MacaulayRead.Arms.postTicks
    omega
  · change _ ≤ P.scanSpace w b + MacaulayRead.Arms.transient b P.arity w + _
    unfold TargetRead.space MacaulayRead.Arms.transient
    omega

end RadicalCertificate.MonomialIndex.ReaderPlan

end VPVNP
end Computability
end OAI
