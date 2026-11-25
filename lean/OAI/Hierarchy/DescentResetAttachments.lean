import OAI.Hierarchy.DescentRouterBank

namespace OAI
/-! # Reattaching the retained local tensor tables to the physical reset bank -/

namespace Hierarchy.DescentResetAttachments
open DescentNamedContact DescentRouterBank Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section

variable {n d : ℕ} {P : Type*} {bits : P→ℕ} (N : Network n P bits)
variable {Q : Type} [Fintype Q] (group : Bool→N.Edge→Q)

def ends : Bool → N.Edge → N.Site
  | false => N.src
  | true => N.dst

abbrev poolWidth := publicWidth group N.width
variable (R : Network d (Bool×Q) (poolWidth N group))

/-- The original site of each endpoint is connected to the actual electrical
attachment of its new packed row. This permits different endpoints at the same
old site to belong to different rows, and different old sites to share a row. -/
abbrev network : Network d P bits where
  Site := N.Site ⊕ R.Site
  Edge := (Bool×N.Edge) ⊕ R.Edge
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := Sum.elim (fun q=>.inl (ends N q.1 q.2)) (fun e=>.inr (R.src e))
  dst := Sum.elim (fun q=>.inr (R.attach (q.1,group q.1 q.2))) (fun e=>.inr (R.dst e))
  width := Sum.elim (fun q=>N.width q.2) R.width
  attach p := .inl (N.attach p)
  position := Sum.elim (fun _=>0) R.position
  in_ball := by
    rintro (v|v)
    · simp
    · exact R.in_ball v

local notation "M" => network N group R

/-- Two independent fine labelings plus the router's own internal cables. -/
def split : (M).Assignment ≃ (Bool→N.Assignment) × R.Assignment where
  toFun a := ⟨fun s e=>a (.inl (s,e)),fun e=>a (.inr e)⟩
  invFun p := fun | .inl q => p.1 q.1 q.2 | .inr e => p.2 e
  left_inv a := by funext e;cases e <;> rfl
  right_inv _ := rfl

def side (v : N.Site) (e : N.Edge) : Bool := decide (N.src e≠v)

theorem side_local (v : N.Site) (e : N.Edge) (h : N.src e=v ∨ N.dst e=v) :
    ends N (side N v e) e=v := by
  by_cases eqn : N.src e=v
  · simp [side,eqn,ends]
  · simp [side,eqn,ends,h.resolve_left eqn]

def oldRows (x : Bool→N.Assignment) (v : N.Site) : N.Assignment :=
  fun e=>x (side N v e) e

variable {F : Type*} [CommSemiring F] (T : N.Tables F) (S : R.Tables F)

def localFactors (a : (M).Assignment) (x : Ports bits) : (M).Site→F
  | .inl v => N.read T (oldRows N ((split N group R a).1) v) x v
  | .inr v => R.read S ((split N group R a).2) (publicWords group N.width ((split N group R a).1)) v

omit [Fintype Q] [CommSemiring F] in
theorem factors_supported : DescentLocalTables.Supported M (localFactors N group R T S) := by
  rintro (v|v) a b x y inner outer
  · apply congrArg₂ (T v)
    · funext e
      exact inner (.inl (side N v e.val,e.val))
        (Or.inl (congrArg Sum.inl (side_local N v e.val e.property)))
    · funext p
      exact outer p.val (congrArg Sum.inl p.property)
  · apply congrArg₂ (S v)
    · funext e
      exact inner (.inr e.val) (e.property.imp (congrArg Sum.inr) (congrArg Sum.inr))
    · funext p
      rcases p with ⟨⟨s,t⟩,hit⟩
      let packed := DescentContactTree.Physical.concat (fun i : Fibre (group s) t => N.width i.val)
      change packed.symm (fun i => a (.inl (s,i.val))) =
        packed.symm (fun i => b (.inl (s,i.val)))
      apply congrArg packed.symm
      funext i
      have aligned : R.attach (s,group s i.val)=v := by rw [i.property];exact hit
      exact inner (.inl (s,i.val)) (Or.inr (congrArg Sum.inr aligned))

def tables : (M).Tables F := DescentLocalTables.tables M (localFactors N group R T S)

omit [Fintype Q] in
theorem value_expand (x : Ports bits) :
    (M).value (tables N group R T S) x =
      ∑ rows : Bool→N.Assignment, (∏v,N.read T (oldRows N rows v) x v)*
        R.value S (publicWords group N.width rows) := by
  unfold Network.value
  let weight (a : (M).Assignment) := ∏ v, (M).read (tables N group R T S) a x v
  refine Eq.trans (b := ∑ a, weight a) ?_ ?_
  · apply Finset.sum_congr (by ext a; simp)
    intro a _
    rfl
  refine ((split N group R).symm.sum_comp weight).symm.trans ?_
  dsimp only [weight]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.prod_sum_type]
  simp only [tables,DescentLocalTables.read _ _ (factors_supported N group R T S)]
  rfl

omit [Fintype Q] in
theorem total_width : (∑e,(M).width e)=(∑e,R.width e)+2*(∑e,N.width e) := by
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
  change (∑e,N.width e)+(∑e,N.width e)+(∑e,R.width e) = (∑e,R.width e)+2*(∑e,N.width e)
  omega

end
end Hierarchy.DescentResetAttachments

end OAI
