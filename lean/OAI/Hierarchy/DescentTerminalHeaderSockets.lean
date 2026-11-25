import OAI.Hierarchy.DescentTerminalCanonicalHeaderPrefix
import OAI.Hierarchy.DescentMountedSortedRoster

namespace OAI
/-! # Computing the same canonical header address from the two physical endpoint views -/
namespace Hierarchy.DescentTerminalHeaderSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalGrainProfiles DescentSortedRoster DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H D w:ℕ}
structure Layout where
  roster : Bank
  publicPrefix : Bank
  cablePrefix : Bank

/-- Since the terminal degree is fixed, the host-times-degree offset needs only additions. -/
def times (x : Expr) : ℕ→Expr
  | 0=>.lit 0
  | n+1=>.op .add (times x n) x

def offset (v:Expr) (D j:ℕ) : Expr := .op .add (times v D) (.lit j)
def successor (z:Expr) : Expr := .op .add z (.lit 1)
def targetAt (L:Layout) (v:Expr) (D j:ℕ) : Expr := .lookup L.roster (offset v D j)

def reverse (L:Layout) (v other:Expr) (D : ℕ) : List (Fin D)→Expr
  | []=>.lit 0
  | j::js=>.branch .eq (targetAt L other D j.val) v
    (successor (offset other D j.val)) (reverse L v other D js)

def canonical (L:Layout) (v:Expr) (H D j:ℕ) : Expr :=
  let other:=targetAt L v D j
  .branch .lt other (.lit H)
    (.branch .lt other v (reverse L v other D (List.finRange D)) (successor (offset v D j)))
    (.lit 0)

def starts (tab:Bank) (key:Expr) : Expr :=
  .branch .lt key (.lit 2) (.lit 0) (.lookup tab (.op .sub key (.lit 2)))
def ends (tab:Bank) (key:Expr) : Expr :=
  .branch .eq key (.lit 0) (.lit 0) (.lookup tab (.op .sub key (.lit 1)))

def head (L:Layout) (H D:ℕ) (v:Expr) (j:Fin (D+1)) : Expr :=
  Fin.cases (starts L.publicPrefix (successor v)) (fun s=>starts L.cablePrefix (canonical L v H D s.val)) j

def amount (L:Layout) (H D:ℕ) (v:Expr) (j:Fin (D+1)) : Expr :=
  Fin.cases (.op .sub (ends L.publicPrefix (successor v)) (starts L.publicPrefix (successor v)))
    (fun s=>let code:=canonical L v H D s.val
            .op .sub (ends L.cablePrefix code) (starts L.cablePrefix code)) j

def ordinal (R:Fin H→Fin D→Option (Fin H)) (v:Fin H) (j:Fin D) : Option (Fin (H*D)) := do
  let z←R v j
  if z<v then
    let s←(List.finRange D).find? (fun t=>decide (R z t=some v))
    pure (finProdFinEquiv (z,s))
  else pure (finProdFinEquiv (v,j))

def code {n:ℕ} (o:Option (Fin n)) : ℕ := o.elim 0 (fun i=>i.val+1)

theorem ordinal_key (R:Fin H→Fin D→Option (Fin H)) (v:Fin H) (j:Fin D)
    (k:Fin (H*D)) (hk:ordinal R v j=some k) :
    ∃z,R v j=some z ∧ slotKey R k=some (DescentTerminalCableOrder.pair v z) := by
  cases other:R v j with
  | none=>simp [ordinal,other] at hk
  | some z=>
    refine ⟨z,rfl,?_⟩
    by_cases flip:z<v
    · cases h:(List.finRange D).find? (fun t=>decide (R z t=some v)) with
      | none=>simp [ordinal,other,flip,h] at hk
      | some s=>
        have same:R z s=some v:=of_decide_eq_true
          (List.find?_some (p:=fun t=>decide (R z t=some v)) h)
        simp [ordinal,other,flip,h] at hk
        subst k
        simp [slotKey,picked,same,le_of_lt flip,DescentTerminalCableOrder.pair_swap z v]
    · simp [ordinal,other,flip] at hk
      subst k
      simp [slotKey,picked,other,le_of_not_gt flip]

theorem times_read (m:Memory w) (r:Word w) (x:Expr) (v n:ℕ) (hx:x.eval m r=(v:Word w)) :
    (times x n).eval m r=((v*n:ℕ):Word w) := by
  induction n with
  | zero=>simp [times,Expr.eval]
  | succ n ih=>simp [times,Expr.eval,RowOp.opcode,BinaryOp.eval,hx,ih,Nat.mul_succ]

theorem at_read (m:Memory w) (r:Word w) (x:Expr) (v j D:ℕ) (hx:x.eval m r=(v:Word w)) :
    (offset x D j).eval m r=((v*D+j:ℕ):Word w) := by
  simp only [offset,Expr.eval,RowOp.opcode,BinaryOp.eval,times_read m r x v D hx,Nat.cast_add]

variable (L:Layout) (R:Fin H→Fin D→Option (Fin H)) (m:Memory w) (row:Word w)
variable (bounds:H<2^w) (physical:∀(v:Fin H) (j:Fin D),
    L.roster.read m ((v.val*D+j.val:ℕ):Word w)=(target (R v j):Word w))

include physical in
theorem other_read (v:Fin H) (x:Expr) (hx:x.eval m row=(v.val:Word w)) (j:Fin D) :
    (targetAt L x D j.val).eval m row=(target (R v j):Word w) := by
  change L.roster.read m ((offset x D j.val).eval m row)=_
  rw [at_read m row x v.val j.val D hx,physical]

private theorem address (v:Fin H) (j:Fin D) : (finProdFinEquiv (v,j)).val=v.val*D+j.val := by
  simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]

include physical bounds in
theorem canonical_read (v:Fin H) (x:Expr) (hx:x.eval m row=(v.val:Word w)) (j:Fin D) :
    (canonical L x H D j.val).eval m row=(code (ordinal R v j):Word w) := by
  let y:=targetAt L x D j.val
  have neighborRead:=other_read L R m row physical v x hx j
  have fit (z:Fin H) : z.val<2^w:=z.isLt.trans bounds
  cases other:R v j with
  | none=>
    have sentinel:y.eval m row=(H:Word w):=by simpa [y,other,target] using neighborRead
    change (if DescriptorExpr.Comparison.lt.test (y.eval m row) (H:Word w) then _ else 0)=_
    simp [sentinel,DescriptorExpr.Comparison.test,ordinal,other,code]
  | some z=>
    have hy:y.eval m row=(z.val:Word w):=by simpa [y,other,target] using neighborRead
    have rev (l:List (Fin D)) : (reverse L x y D l).eval m row=
        ((code ((l.find? (fun t=>decide (R z t=some v))).map (fun t=>finProdFinEquiv (z,t)))):Word w) := by
      induction l with
      | nil=>rfl
      | cons t ts ih=>
        have h:=other_read L R m row physical z y hy t
        have eqn : (target (R z t):Word w)=(v.val:Word w) ↔ R z t=some v := by
          cases b:R z t with
          | none=>simp [target,Fin.ext_iff,Fin.val_cast_of_lt bounds,Fin.val_cast_of_lt (fit v),Nat.ne_of_gt v.isLt]
          | some u=>simp [target,Fin.ext_iff,Fin.val_cast_of_lt (fit u),Fin.val_cast_of_lt (fit v)]
        change (if DescriptorExpr.Comparison.eq.test ((targetAt L y D t.val).eval m row) (x.eval m row)
          then (successor (offset y D t.val)).eval m row else (reverse L x y D ts).eval m row)=_
        simp only [h,hx,DescriptorExpr.Comparison.test,beq_iff_eq,eqn,List.find?_cons]
        by_cases hit:R z t=some v <;>
          simp [hit,ih,code,successor,Expr.eval,RowOp.opcode,BinaryOp.eval,
            at_read m row y z.val t.val D hy,Nat.cast_add]; ac_rfl
    change (if DescriptorExpr.Comparison.lt.test (y.eval m row) (H:Word w) then
      if DescriptorExpr.Comparison.lt.test (y.eval m row) (x.eval m row) then (reverse L x y D _).eval m row
      else (successor (offset x D j.val)).eval m row else 0)=_
    simp only [hy,hx,DescriptorExpr.Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt (fit z),
      Fin.val_cast_of_lt (fit v),Fin.val_cast_of_lt bounds,ite_eq_left z.isLt]
    by_cases flip:z<v
    · have zlt : z.val<v.val:=flip
      rw [ite_eq_left zlt,rev]
      cases found:(List.finRange D).find? (fun t=>decide (R z t=some v)) <;> simp [ordinal,other,flip,found,code]
    · have zge : ¬z.val<v.val:=flip
      rw [ite_eq_right zge]
      simp [flip,ordinal,other,code,successor,Expr.eval,RowOp.opcode,BinaryOp.eval,
        at_read m row x v.val j.val D hx,Nat.cast_add]
      ac_rfl


end
end Hierarchy.DescentTerminalHeaderSockets

end OAI
