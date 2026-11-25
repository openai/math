import OAI.Hierarchy.DescentOrderedResetRows
import OAI.Hierarchy.DescentResetTrunks

namespace OAI
/-! # Boundary splice with the actual inherited cable order at both source and hub -/

namespace Hierarchy.DescentResetTrunks.Ordered
open DescentRouterBank DescentNamedContact DescentResetAttachments DescentResetTrunks Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {P Q H F : Type} [Fintype Q] [Fintype H] [CommSemiring F] {d n L : ℕ} {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
local notation "M" => DescentResetTrunks.network N home group R

def «public» (x : Bool→N.Assignment) : Ports (publicWidth group N.width) :=
  fun p=>(DescentOrderedReset.words key (group p.1) N.width).symm (x p.1) p.2

def rows (p : Ports (publicWidth group N.width)) (s : Bool) :=
  DescentOrderedReset.words key (group s) N.width (fun r=>p (s,r))

omit [Fintype Q] in
@[simp] theorem rows_public (x : Bool→N.Assignment) (s : Bool) :
    rows N group key («public» N group key x) s=x s := by
  let packed := DescentOrderedReset.words key (group s) N.width
  change packed (packed.symm (x s)) = x s
  exact packed.apply_symm_apply (x s)

def decode : (M).Assignment ≃ (Bool→N.Assignment) × (N.Assignment × R.Assignment) where
  toFun a := ⟨fun s e=>a (.inl (s,e)),DescentOrderedReset.words key (moved N home) N.width (fun z=>a (.inr (.inl z))),fun e=>a (.inr (.inr e))⟩
  invFun p
    | .inl (s,e) => p.1 s e
    | .inr (.inl z) => (DescentOrderedReset.words key (moved N home) N.width).symm p.2.1 z
    | .inr (.inr e) => p.2.2 e
  left_inv a := by
    funext e
    rcases e with ⟨s,e⟩|z|e
    · rfl
    · exact congrFun ((DescentOrderedReset.words key (moved N home) N.width).symm_apply_apply _) z
    · rfl
  right_inv p := by rcases p with ⟨x,t,z⟩; simp

def original (a : (M).Assignment) : Bool→N.Assignment
  | false => (decode N home group R key a).1 false
  | true => (decode N home group R key a).2.1

variable (T : N.Tables F) (S : R.Tables F)
def factor (a : (M).Assignment) (pins : Ports bits) : (M).Site → F
  | .inl (false,h) =>
    ∏v : Fibre home h,N.read T (oldRows N (original N home group R key a) v.val) pins v.val
  | .inl (true,h) =>
    if ∀e,moved N home e=h → (decode N home group R key a).2.1 e=(decode N home group R key a).1 true e then 1 else 0
  | .inr v => R.read S (decode N home group R key a).2.2 («public» N group key (decode N home group R key a).1) v

omit [Fintype Q] in
private theorem trunk_at (a b : (M).Assignment) {h : H}
    (edge : a (.inr (.inl h))=b (.inr (.inl h))) (e : N.Edge) (atHome : moved N home e=h) :
    (decode N home group R key a).2.1 e=(decode N home group R key b).2.1 e := by
  subst h
  funext j
  exact congrFun edge _

omit [Fintype Q] in
theorem local_factor : DescentLocalTables.Supported M (factor N home group R key T S) := by
  rintro (⟨s,h⟩|v) a b x y inner outer
  · cases s with
    | false =>
      apply Finset.prod_congr rfl
      intro v _
      apply congrArg₂ (T v.val)
      · funext e
        let side := DescentResetAttachments.side N v.val e.val
        have here : ends N side e.val = v.val := side_local N v.val e.val e.property
        change original N home group R key a side e.val=original N home group R key b side e.val
        cases hs : side with
        | false =>
          have atSrc : ends N false e.val = v.val := by simpa only [hs] using here
          exact inner (.inl (false,e.val)) (Or.inl (congrArg (fun z=>Sum.inl (false,z))
            ((congrArg home atSrc).trans v.property)))
        | true =>
          have atDst : ends N true e.val = v.val := by simpa only [hs] using here
          apply trunk_at N home group R key a b (inner (.inr (.inl h)) (Or.inl rfl))
          exact (congrArg home atDst).trans v.property
      · funext p
        exact outer p.val (congrArg (fun z=>Sum.inl (false,z)) ((congrArg home p.property).trans v.property))
    | true =>
      apply if_congr _ rfl rfl
      apply forall_congr'
      intro e
      apply forall_congr'
      intro hit
      have trunk := trunk_at N home group R key a b (inner (.inr (.inl h)) (Or.inr rfl)) e hit
      have wire := inner (.inl (true,e)) (Or.inl (congrArg (fun z=>Sum.inl (true,z)) hit))
      exact ⟨fun same => trunk.symm.trans (same.trans wire),
        fun same => trunk.trans (same.trans wire.symm)⟩
  · apply congrArg₂ (S v)
    · funext e
      exact inner (.inr (.inr e.val)) (e.property.imp (congrArg Sum.inr) (congrArg Sum.inr))
    · funext p
      rcases p with ⟨⟨s,t⟩,hit⟩
      let packed := DescentOrderedWords.decode (DescentOrderedReset.fibreKey key (group s) t)
        (fun i : Fibre (group s) t => N.width i.val)
      change packed.symm (fun i => a (.inl (s,i.val))) =
        packed.symm (fun i => b (.inl (s,i.val)))
      apply congrArg packed.symm
      funext i
      have aligned : R.attach (s,group s i.val)=v := by rw [i.property];exact hit
      exact inner (.inl (s,i.val)) (Or.inr (congrArg Sum.inr aligned))

def tables := DescentLocalTables.tables M (factor N home group R key T S)

private theorem indicator (x t : N.Assignment) :
    (∏h,if ∀e,moved N home e=h→t e=x e then (1:F) else 0)=if t=x then 1 else 0 := by
  have all : (∀ h e, moved N home e = h → t e = x e) ↔ t = x :=
    ⟨fun p => funext (fun e => p (moved N home e) e rfl), fun p _ e _ => congrFun p e⟩
  simp only [Fintype.prod_boole, all]

omit [Fintype Q] in
/-- Every assignment to the real old joins selects exactly one trunk
label. After summing that label, the packed tensors read all old couplings. -/
theorem value_expand (pins : Ports bits) : (M).value (tables N home group R key T S) pins =
    ∑ rows : Bool→N.Assignment, (∏v,N.read T (oldRows N rows v) pins v)*
      R.value S («public» N group key rows) := by
  unfold Network.value
  let weight (a : (M).Assignment) := ∏ v, (M).read (tables N home group R key T S) a pins v
  refine Eq.trans (b := ∑ a, weight a) ?_ ?_
  · apply Finset.sum_congr (by ext a; simp)
    intro a _
    rfl
  refine ((decode N home group R key).symm.sum_comp weight).symm.trans ?_
  dsimp only [weight]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro rows _
  simp_rw [Fintype.sum_prod_type]
  have expand (t : N.Assignment) (z : R.Assignment) :
      (∏i,(M).read (tables N home group R key T S) ((decode N home group R key).symm (rows,(t,z))) pins i)=
      (if t=rows true then 1 else 0) *
      (∏v,N.read T (oldRows N (fun s=>if s then t else rows false) v) pins v) *
      (∏v,R.read S z («public» N group key rows) v) := by
    simp only [tables,DescentLocalTables.read _ _ (local_factor N home group R key T S),Fintype.prod_sum_type,
      Fintype.prod_prod_type,Fintype.prod_bool,factor,Equiv.apply_symm_apply,indicator N home]
    have fibers (f : N.Site→F) : (∏h,∏v : Fibre home h,f v.val)=∏v,f v := by
      rw [←Fintype.prod_sigma' (fun h (v : Fibre home h)=>f v.val)]
      exact (Equiv.sigmaFiberEquiv home).prod_comp f
    have decoded : original N home group R key ((decode N home group R key).symm (rows,(t,z))) =
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
theorem value (bank : ∀p,R.value S p=
    if rows N group key p false=rows N group key p true then 1 else 0)
    (x : Ports bits) : (M).value (tables N home group R key T S) x=N.value T x := by
  rw [value_expand,←(Equiv.boolArrowEquivProd N.Assignment).symm.sum_comp,Fintype.sum_prod_type]
  change (∑a : N.Assignment, ∑b : N.Assignment, _) =
    ∑a : N.Assignment,∏v,N.read T a x v
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp [bank,rows_public,Equiv.boolArrowEquivProd]
    rfl
  · intro b _ neq
    simp [bank,rows_public,Equiv.boolArrowEquivProd,Ne.symm neq]
  · simp

omit [Fintype Q] in
/-- The old tensor at a physical hub reads its original bit via the actual
trunk's packed word; the same offset is checked by the neighboring relay. -/
theorem original_true (a : (M).Assignment) (e : N.Edge) (j : Fin (N.width e)) :
    original N home group R key a true e j = a (.inr (.inl (moved N home e)))
      (DescentOrderedWords.bitIndex (DescentOrderedReset.fibreKey key (moved N home) (moved N home e))
        (fun i=>N.width i.val) ⟨⟨e,rfl⟩,j⟩) := rfl

end
end Hierarchy.DescentResetTrunks.Ordered

end OAI
