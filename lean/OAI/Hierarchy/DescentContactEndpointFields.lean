import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentOverlapCount
import OAI.Hierarchy.DescentCandidateMaskRAM

namespace OAI
/-! # Direct-contact incidence in a original host neighborhood -/
namespace Hierarchy.DescentContactEndpointFields
open DescentSIMDLookup DescentPackedZip DescentCandidateMaskRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {a H G M w : ℕ}

/-- The same radix carries the original receiver-relative owner on both ends, including
old host degrees larger than the four ports of a newly installed site. -/
def endpoint (k : ℕ) (shape slot : Cell a) (room : 2^k*shape.val+slot.val<2^a) : Cell a :=
  ⟨2^k*shape.val+slot.val,room⟩

theorem endpoint_eq (k : ℕ) {x i y j : Cell a} (h) (g) (one : i.val<2^k) (two : j.val<2^k) :
    endpoint k x i h=endpoint k y j g ↔ x=y ∧ i=j :=by
  constructor
  · intro e
    have n:=congrArg Fin.val e
    change 2^k*x.val+i.val=2^k*y.val+j.val at n
    have xy : x.val=y.val:=by
      rcases lt_trichotomy x.val y.val with less|same|more
      · have t:=Nat.mul_le_mul_left (2^k) (Nat.succ_le_of_lt less)
        rw [Nat.mul_succ] at t;omega
      · exact same
      · have t:=Nat.mul_le_mul_left (2^k) (Nat.succ_le_of_lt more)
        rw [Nat.mul_succ] at t;omega
    rw [xy] at n
    exact ⟨Fin.ext xy,Fin.ext (by omega)⟩
  · rintro ⟨rfl,rfl⟩;rfl

def times (shape : Expr) : ℕ→Expr
  | 0 => shape
  | k+1 => .op .add (times shape k) (times shape k)
def term (k : ℕ) (shape slot : Expr) : Expr := .op .add (times shape k) slot

theorem fits (k : ℕ) (shape slot : Expr) (out : ℕ) (one : shape.Fits w out) (two : slot.Fits w out) :
    (term k shape slot).Fits w out :=by
  refine ⟨?_,two⟩
  induction k with
  | zero=>exact one
  | succ k ih=>exact ⟨ih,ih⟩

private theorem times_work (k : ℕ) (shape : Expr) :
    (times shape k).work+1=2^k*(shape.work+1):=by
  induction k with
  | zero=>simp [times]
  | succ k ih=>
    simp only [times,Expr.work,pow_succ,Nat.mul_right_comm (2^k) 2 (shape.work+1)]
    omega

theorem work (k : ℕ) (shape slot : Expr) : (term k shape slot).work=2^k*(shape.work+1)+slot.work:=by
  have h:=times_work k shape
  change (times shape k).work+slot.work+1=_
  omega

/-- The input field already carries the endpoint shape. The receiver-relative slot
costs exactly the ceiling logarithm of the original degree plus two. -/
theorem room (degree shapes width : ℕ) (shape slot : Cell a) (small : shape.val<shapes)
    (one : slot.val≤degree+1) (area : 2^(Nat.clog 2 (degree+2))*shapes≤2^width) :
    2^(Nat.clog 2 (degree+2))*shape.val+slot.val<2^width:=by
  let k:=Nat.clog 2 (degree+2)
  have cap : degree+2≤2^k:=Nat.le_pow_clog (by decide) _
  have following:=Nat.mul_le_mul_left (2^k) small
  change 2^k*(shape.val+1)≤2^k*shapes at following
  rw [Nat.mul_succ] at following
  change 2^k*shape.val+slot.val<2^width
  change 2^k*shapes≤2^width at area
  omega

theorem degree_work (degree : ℕ) (shape slot : Expr) :
    (term (Nat.clog 2 (degree+2)) shape slot).work≤2*(degree+2)*(shape.work+1)+slot.work:=by
  rw [work]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (DescentSIMDLookup.Overlap.rounded (degree+1))) _

private theorem times_eval (k : ℕ) (shape : Expr) (m : Memory w) (address : Word w) :
    (times shape k).eval m address=(2:Word w)^k*shape.eval m address:=by
  induction k with
  | zero=>simp [times]
  | succ k ih=>
    simp only [times,Expr.eval,RowOp.opcode,BinaryOp.eval,ih,pow_succ]
    ring

private theorem digits {d m : ℕ} (x : Fin m→Cell d) :
    (encode d m x).val=∑j,(x j).val*(2^d)^j.val:=finFunctionFinEquiv_apply x

theorem word (k : ℕ) (sh sl : Fin H→Fin G→Cell a) (bound : ∀h g,2^k*(sh h g).val+(sl h g).val<2^a) (p : Row H G M) :
    (data (fun h g=>endpoint k (sh h g) (sl h g) (bound h g)) p).val=
      2^k*(data sh p).val+(data sl p).val:=by
  simp only [data,digits,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases alive:p.2.val*M+j.val<G
  · simp only [dite_eq_left alive,endpoint,add_mul,Nat.mul_assoc]
  · simp [alive]

theorem source (k : ℕ) (shape slot : Expr) (sh sl : Fin H→Fin G→Cell a) (m : Memory w)
    (one : Source shape sh M m) (two : Source slot sl M m)
    (bound : ∀h g,2^k*(sh h g).val+(sl h g).val<2^a) :
    Source (term k shape slot) (fun h g=>endpoint k (sh h g) (sl h g) (bound h g)) M m:=by
  intro p
  rw [word k sh sl bound p]
  simp only [term,Expr.eval,RowOp.opcode,BinaryOp.eval,times_eval,one p,two p,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]

/-- Order of the three receiver-local tuples is source, target, receiver. The four
relative rank columns are filled by the subsequent published threshold circuit. -/
def rawWords (units shapeSlot₀ shapeSlot₁ receiver missing : Expr) : Fin 9→Expr :=
  ![units,shapeSlot₀,shapeSlot₁,receiver,.lit 0,.lit 0,.lit 0,missing,units]

theorem visible_iff (k : ℕ) {sh sl : Fin 3→Cell a} {amount missing : Cell a} {rank : Fin 3→Cell a}
    (bound : ∀i,2^k*(sh i).val+(sl i).val<2^a) (short : ∀i,(sl i).val<2^k) :
    let pair:=fun i=>endpoint k (sh i) (sl i) (bound i)
    let x : Fin 9→Cell a:=![amount,pair 0,pair 1,pair 2,rank 0,rank 1,rank 2,missing,amount]
    visible x ↔ 0<amount.val ∧
      ((sh 0=sh 2 ∧ sl 0=sl 2) ∨ (sh 1=sh 2 ∧ sl 1=sl 2)):=by
  let code (i : Fin 3) := endpoint k (sh i) (sl i) (bound i)
  have decode (i : Fin 3) :
      (code i).val=(code 2).val ↔ sh i=sh 2 ∧ sl i=sl 2 := by
    have values : code i=code 2 ↔ (code i).val=(code 2).val := Fin.ext_iff
    exact values.symm.trans
      (endpoint_eq k (bound i) (bound 2) (short i) (short 2))
  change (amount.val≠0 ∧ 0<amount.val ∧
    ((code 0).val=(code 2).val ∨ (code 1).val=(code 2).val)) ↔ _
  rw [decode 0,decode 1]
  exact ⟨fun h=>h.2,fun h=>⟨Nat.ne_of_gt h.1,h⟩⟩

end
end Hierarchy.DescentContactEndpointFields

end OAI
