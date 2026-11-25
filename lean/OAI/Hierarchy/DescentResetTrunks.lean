import OAI.Hierarchy.DescentResetReadout

namespace OAI
/-! # Group whole old tensors at a terminal with two oriented hardware ports on each side -/

namespace Hierarchy.DescentResetTrunks
open DescentRouterBank DescentNamedContact DescentResetAttachments Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {P Q H F : Type} [Fintype Q] [Fintype H] [CommSemiring F] {d n : ℕ} {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width))
abbrev moved := fun e=>home (N.dst e)
abbrev trunkWidth := width (moved N home) N.width

/-- The false terminal holds the old tensors. Its only link to the true-side
relay is a single cable carrying the entire word from that side. -/
abbrev network : Network d P bits where
  Site := (Bool×H) ⊕ R.Site
  Edge := (Bool×N.Edge) ⊕ (H ⊕ R.Edge)
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src
    | .inl (s,e) => .inl (s,home (ends N s e))
    | .inr (.inl z) => .inl (false,z)
    | .inr (.inr e) => .inr (R.src e)
  dst
    | .inl (s,e) => .inr (R.attach (s,group s e))
    | .inr (.inl z) => .inl (true,z)
    | .inr (.inr e) => .inr (R.dst e)
  width
    | .inl (_,e) => N.width e
    | .inr (.inl z) => trunkWidth N home z
    | .inr (.inr e) => R.width e
  attach p := .inl (false,home (N.attach p))
  position := Sum.elim (fun _=>0) R.position
  in_ball := by
    rintro (_|v)
    · simp
    · exact R.in_ball v

local notation "M" => network N home group R

def decode : (M).Assignment ≃ (Bool→N.Assignment) × (N.Assignment × R.Assignment) where
  toFun a := ⟨fun s e=>a (.inl (s,e)),labels (moved N home) N.width (fun z=>a (.inr (.inl z))),fun e=>a (.inr (.inr e))⟩
  invFun p
    | .inl (s,e) => p.1 s e
    | .inr (.inl z) => (labels (moved N home) N.width).symm p.2.1 z
    | .inr (.inr e) => p.2.2 e
  left_inv a := by
    funext e
    rcases e with ⟨s,e⟩|z|e
    · rfl
    · exact congrFun ((labels (moved N home) N.width).symm_apply_apply _) z
    · rfl
  right_inv p := by rcases p with ⟨x,t,z⟩;simp

def original (a : (M).Assignment) : Bool→N.Assignment
  | false => (decode N home group R a).1 false
  | true => (decode N home group R a).2.1

variable (T : N.Tables F) (S : R.Tables F)
def factor (a : (M).Assignment) (pins : Ports bits) : (M).Site → F
  | .inl (false,h) =>
    ∏v : Fibre home h,N.read T (oldRows N (original N home group R a) v.val) pins v.val
  | .inl (true,h) =>
    if ∀e,moved N home e=h → (decode N home group R a).2.1 e=(decode N home group R a).1 true e then 1 else 0
  | .inr v => R.read S (decode N home group R a).2.2 (publicWords group N.width (decode N home group R a).1) v

omit [Fintype Q] in
private theorem trunk_at (a b : (M).Assignment) {h : H}
    (edge : a (.inr (.inl h))=b (.inr (.inl h))) (e : N.Edge) (atHome : moved N home e=h) :
    (decode N home group R a).2.1 e=(decode N home group R b).2.1 e := by
  subst h
  exact congrFun (congrArg (DescentContactTree.Physical.concat
    (fun i : Fibre (moved N home) (moved N home e)=>N.width i.val)) edge) ⟨e,rfl⟩

omit [Fintype Q] in
theorem local_factor : DescentLocalTables.Supported M (factor N home group R T S) := by
  rintro (⟨s,h⟩|v) a b x y inner outer
  · cases s with
    | false =>
      apply Finset.prod_congr rfl
      intro v _
      apply congrArg₂ (T v.val)
      · funext e
        let side := DescentResetAttachments.side N v.val e.val
        have here : ends N side e.val = v.val := side_local N v.val e.val e.property
        change original N home group R a side e.val=original N home group R b side e.val
        cases hs : side with
        | false =>
          have atSrc : ends N false e.val = v.val := by simpa only [hs] using here
          exact inner (.inl (false,e.val)) (Or.inl (congrArg (fun z=>Sum.inl (false,z))
            ((congrArg home atSrc).trans v.property)))
        | true =>
          have atDst : ends N true e.val = v.val := by simpa only [hs] using here
          apply trunk_at N home group R a b (inner (.inr (.inl h)) (Or.inl rfl))
          exact (congrArg home atDst).trans v.property
      · funext p
        exact outer p.val (congrArg (fun z=>Sum.inl (false,z)) ((congrArg home p.property).trans v.property))
    | true =>
      apply if_congr _ rfl rfl
      apply forall_congr'
      intro e
      apply forall_congr'
      intro hit
      have trunk := trunk_at N home group R a b (inner (.inr (.inl h)) (Or.inr rfl)) e hit
      have wire := inner (.inl (true,e)) (Or.inl (congrArg (fun z=>Sum.inl (true,z)) hit))
      exact ⟨fun same => trunk.symm.trans (same.trans wire),
        fun same => trunk.trans (same.trans wire.symm)⟩
  · apply congrArg₂ (S v)
    · funext e
      exact inner (.inr (.inr e.val)) (e.property.imp (congrArg Sum.inr) (congrArg Sum.inr))
    · funext p
      rcases p with ⟨⟨s,t⟩,hit⟩
      let packed := DescentContactTree.Physical.concat (fun i : Fibre (group s) t => N.width i.val)
      change packed.symm (fun i => a (.inl (s,i.val))) =
        packed.symm (fun i => b (.inl (s,i.val)))
      apply congrArg packed.symm
      funext i
      have aligned : R.attach (s,group s i.val)=v := by rw [i.property];exact hit
      exact inner (.inl (s,i.val)) (Or.inr (congrArg Sum.inr aligned))

def tables := DescentLocalTables.tables M (factor N home group R T S)

private theorem indicator (x t : N.Assignment) :
    (∏h,if ∀e,moved N home e=h→t e=x e then (1:F) else 0)=if t=x then 1 else 0 := by
  have all : (∀ h e, moved N home e = h → t e = x e) ↔ t = x :=
    ⟨fun p => funext (fun e => p (moved N home e) e rfl), fun p _ e _ => congrFun p e⟩
  simp only [Fintype.prod_boole, all]

omit [Fintype Q] in
/-- Every assignment to the real old joins selects exactly one trunk
label. After summing that label, the packed tensors read all old couplings. -/
theorem value (pins : Ports bits) : (M).value (tables N home group R T S) pins =
    (DescentResetAttachments.network N group R).value (DescentResetAttachments.tables N group R T S) pins := by
  rw [DescentResetAttachments.value_expand]
  unfold Network.value
  let weight (a : (M).Assignment) := ∏ v, (M).read (tables N home group R T S) a pins v
  refine Eq.trans (b := ∑ a, weight a) ?_ ?_
  · apply Finset.sum_congr (by ext a; simp)
    intro a _
    rfl
  refine ((decode N home group R).symm.sum_comp weight).symm.trans ?_
  dsimp only [weight]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro rows _
  simp_rw [Fintype.sum_prod_type]
  have expand (t : N.Assignment) (z : R.Assignment) :
      (∏i,(M).read (tables N home group R T S) ((decode N home group R).symm (rows,(t,z))) pins i)=
      (if t=rows true then 1 else 0) *
      (∏v,N.read T (oldRows N (fun s=>if s then t else rows false) v) pins v) *
      (∏v,R.read S z (publicWords group N.width rows) v) := by
    simp only [tables,DescentLocalTables.read _ _ (local_factor N home group R T S),Fintype.prod_sum_type,
      Fintype.prod_prod_type,Fintype.prod_bool,factor,Equiv.apply_symm_apply,indicator N home]
    have fibers (f : N.Site→F) : (∏h,∏v : Fibre home h,f v.val)=∏v,f v := by
      rw [←Fintype.prod_sigma' (fun h (v : Fibre home h)=>f v.val)]
      exact (Equiv.sigmaFiberEquiv home).prod_comp f
    have decoded : original N home group R ((decode N home group R).symm (rows,(t,z))) =
        fun b => if b then t else rows false := by
      funext b
      cases b <;> simp [original]
    rw [decoded]
    refine congrArg₂ (· * ·) ?_ rfl
    refine congrArg₂ (· * ·) rfl ?_
    exact fibers (fun v => N.read T (oldRows N (fun b => if b then t else rows false) v) pins v)
  simp_rw [expand]
  rw [Finset.sum_eq_single_of_mem (rows true) (Finset.mem_univ _)]
  · have eta : (fun s : Bool=>if s then rows true else rows false)=rows := by funext s;cases s <;> rfl
    simp only [ite_true,one_mul,eta,←Finset.mul_sum]
  · intro t _ ne
    simp [ne]

omit [Fintype Q] in
theorem width : (∑e,(M).width e)= (∑e,R.width e)+3*(∑e,N.width e) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
  change (∑e,N.width e)+(∑e,N.width e)+((∑z,trunkWidth N home z)+(∑e,R.width e))=_
  rw [DescentNamedContact.width_sum]
  omega

end
end Hierarchy.DescentResetTrunks

end OAI
