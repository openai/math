import OAI.ThreeFlat.Diagonal.RefreshDemandRows
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # The transpose between old and fresh site ordinals in a degree refresh

The consumed port occupies the low old lane bits. In successor site order
the remaining lane moves inside the port. The native parent and singleton
child records therefore use inverse mixed-radix transposes.
-/

namespace ThreeFlat.Diagonal.RefreshOwnership

open Computability.VPVNP.Compression RAM.PhysicalPinsExpr CompressorPacking.Native

def oldSite (m L v p l : ℕ) := v*(m*L)+(p+m*l)
def newSite (m L v p l : ℕ) := (v*m+p)*L+l

def child (m L i : ℕ) := oldSite m L (i/L/m) (i/L%m) (i%L)
def owner (m L i : ℕ) := newSite m L (i/(m*L)) (i%(m*L)%m) (i%(m*L)/m)

private theorem splitRow (x : ℕ) {n : ℕ} (i : Fin n) :
    (x*n+i.val)/n=x ∧ (x*n+i.val)%n=i.val := by
  constructor
  · rw [Nat.mul_comm x,Nat.mul_add_div (Nat.zero_lt_of_lt i.isLt),Nat.div_eq_of_lt i.isLt,Nat.add_zero]
  · rw [Nat.mul_comm x,Nat.mul_add_mod,Nat.mod_eq_of_lt i.isLt]

theorem child_new {m L : ℕ} (v : ℕ) (p : Fin m) (l : Fin L) :
    child m L (newSite m L v p.val l.val)=oldSite m L v p.val l.val := by
  have h := splitRow (v*m+p.val) l
  have q := splitRow v p
  simp only [child,newSite,h.1,h.2,q.1,q.2]

theorem owner_old {m L : ℕ} (v : ℕ) (p : Fin m) (l : Fin L) :
    owner m L (oldSite m L v p.val l.val)=newSite m L v p.val l.val := by
  let r : Fin (m*L) := ⟨p.val+m*l.val,by
    calc p.val+m*l.val < m+m*l.val := Nat.add_lt_add_right p.isLt _
         _ = (l.val+1)*m := by ring
         _ ≤ L*m := Nat.mul_le_mul_right m l.isLt
         _ = m*L := Nat.mul_comm ..⟩
  have h := splitRow v r
  have q := splitRow l.val p
  have eq : p.val+m*l.val=l.val*m+p.val := by ac_rfl
  change newSite m L ((v*(m*L)+r.val)/(m*L)) ((v*(m*L)+r.val)%(m*L)%m)
    ((v*(m*L)+r.val)%(m*L)/m) = _
  rw [h.1,h.2]
  change newSite m L v ((p.val+m*l.val)%m) ((p.val+m*l.val)/m)=_
  rw [eq,q.1,q.2]

/-- The formulas apply to a physical old site, in the binary chart consumed
by RefreshTies.arrival and in the numbered successor base/port/lane chart. -/
theorem true_site {v a t : ℕ} (b : Fin v) (p : BitWord a) (l : BitWord t) :
    let old := oldSite (2^a) (2^t) b.val (tagOrdinal a p).val (tagOrdinal t l).val
    let next := newSite (2^a) (2^t) b.val (tagOrdinal a p).val (tagOrdinal t l).val
    child (2^a) (2^t) next=old ∧ owner (2^a) (2^t) old=next :=
  ⟨child_new _ _ _,owner_old _ _ _⟩

/-- Numerical forms embedded directly in the two header scans. -/
def childExpr {n : ℕ} (m : ℕ) (L i : Formula n) : Formula n :=
  let vj := Formula.op .div i L
  let v := Formula.op .div vj (.lit m)
  let j := Formula.op .mod vj (.lit m)
  let l := Formula.op .mod i L
  .op .add (.op .mul v (.op .mul (.lit m) L)) (.op .add j (.op .mul (.lit m) l))

def ownerExpr {n : ℕ} (m : ℕ) (L i : Formula n) : Formula n :=
  let full := Formula.op .mul (.lit m) L
  let v := Formula.op .div i full
  let r := Formula.op .mod i full
  let j := Formula.op .mod r (.lit m)
  let l := Formula.op .div r (.lit m)
  .op .add (.op .mul (.op .add (.op .mul v (.lit m)) j) L) l

theorem childExpr_read {n W : ℕ} (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
    (m : ℕ) (L i : Formula n) :
    let V := Formula.natural W data mem vs
    V (childExpr m L i)=child m (V L) (V i) := rfl

theorem ownerExpr_read {n W : ℕ} (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
    (m : ℕ) (L i : Formula n) :
    let V := Formula.natural W data mem vs
    V (ownerExpr m L i)=owner m (V L) (V i) := rfl

end ThreeFlat.Diagonal.RefreshOwnership

end OAI
