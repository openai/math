import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # A native scan over a row-major cuboid of word addresses -/

namespace Hierarchy.GridTopologyRAM
open ThreeFlat
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorExpr RAM.PhysicalProcedure
open scoped Fin.CommRing

variable {w K : ℕ}
abbrev Term3 (w K : ℕ) := Term w K 3

def index (base b c i j z : ℕ) := base + ((i*b+j)*c+z)

/-- The three incoming registers to a decoded source expression are the
outer, middle and inner digits of its absolute output address. -/
def digits (base b c : ℕ) : Fin 3 → Term w K 1 :=
  let pos := Term.binary .sub (.result 0) (.literal (base:Word w))
  let row := Term.binary .div pos (.literal (c:Word w))
  ![.binary .div row (.literal (b:Word w)),.binary .mod row (.literal (b:Word w)),
    .binary .mod pos (.literal (c:Word w))]

def decoded (e : Term3 w K) (base b c : ℕ) : Term w K 1 := e.instantiate (digits base b c)

private theorem split_div (x s j : ℕ) (hj : j < s) :
    (x*s+j)/s=x := by
  rw [Nat.mul_comm x s,Nat.mul_add_div (Nat.zero_lt_of_lt hj),Nat.div_eq_of_lt hj,Nat.add_zero]

private theorem split_mod (x s j : ℕ) (hj : j < s) : (x*s+j)%s=j := by
  simp [Nat.mod_eq_of_lt hj]

theorem at_index (e : Term3 w K) (base b c i : ℕ) (j : Fin b) (z : Fin c)
    (m : Memory w) (data : Fin K → Word w)
    (fit : index base b c i j.val z.val < 2^w) (bf : b < 2^w) (cf : c < 2^w) :
    (decoded e base b c).eval data m (fun _ => (index base b c i j.val z.val:Word w)) =
      e.eval data m ![(i:Word w),(j.val:Word w),(z.val:Word w)] := by
  let x := i*b+j.val
  let off := x*c+z.val
  have offFit : off < 2^w := by change base+off < 2^w at fit; omega
  have rowFit : x < 2^w :=
    ((Nat.le_mul_of_pos_right x (Nat.zero_lt_of_lt z.isLt)).trans
      (Nat.le_add_right (x*c) z.val)).trans_lt offFit
  have sub : ((index base b c i j.val z.val:ℕ):Word w) - (base:Word w) = (off:Word w) := by
    simp [index,off,x]
  have dvc : BinaryOp.eval .div (off:Word w) (c:Word w)=(x:Word w) := by
    change Fin.ofNat (2^w) ((off:Word w).val/(c:Word w).val) = _
    rw [Fin.val_cast_of_lt offFit,Fin.val_cast_of_lt cf,show off/c=x from split_div _ _ _ z.isLt]; rfl
  have md : BinaryOp.eval .mod (off:Word w) (c:Word w)=(z.val:Word w) := by
    change Fin.ofNat (2^w) ((off:Word w).val%(c:Word w).val) = _
    rw [Fin.val_cast_of_lt offFit,Fin.val_cast_of_lt cf,show off%c=z.val from split_mod _ _ _ z.isLt]; rfl
  have dvb : BinaryOp.eval .div (x:Word w) (b:Word w)=(i:Word w) := by
    change Fin.ofNat (2^w) ((x:Word w).val/(b:Word w).val) = _
    rw [Fin.val_cast_of_lt rowFit,Fin.val_cast_of_lt bf,show x/b=i from split_div _ _ _ j.isLt]; rfl
  have mb : BinaryOp.eval .mod (x:Word w) (b:Word w)=(j.val:Word w) := by
    change Fin.ofNat (2^w) ((x:Word w).val%(b:Word w).val) = _
    rw [Fin.val_cast_of_lt rowFit,Fin.val_cast_of_lt bf,show x%b=j.val from split_mod _ _ _ j.isLt]; rfl
  unfold decoded
  rw [Term.eval_instantiate]
  apply congrArg (e.eval data m)
  funext s
  fin_cases s
  · change BinaryOp.eval .div (BinaryOp.eval .div ((index base b c i j.val z.val:Word w) - (base:Word w))
      (c:Word w)) (b:Word w)=(i:Word w)
    rw [sub,dvc,dvb]
  · change BinaryOp.eval .mod (BinaryOp.eval .div ((index base b c i j.val z.val:Word w) - (base:Word w))
      (c:Word w)) (b:Word w)=(j.val:Word w)
    rw [sub,dvc,mb]
  · change BinaryOp.eval .mod ((index base b c i j.val z.val:Word w) - (base:Word w)) (c:Word w)=(z.val:Word w)
    rw [sub,md]

theorem binds_decoded (e : Term3 w K) (base b c : ℕ) :
    (decoded e base b c).binds = e.binds+16 := by
  simp [decoded,digits,Fin.sum_univ_succ,Term.literal,Term.binary,Term.binds]

def scan (e : Term3 w K) (data : Fin K → Word w) (base a b c : ℕ) : Procedure w :=
  PhysicalInputPhases.writing (decoded e base b c) data base (a*b*c)

/-- Specs for source generators may establish an output word by looking only
at the three bounded coordinates, while the native loop holds a single ordinal. -/
theorem scan_spec (e : Term3 w K) (data : Fin K → Word w) (base a b c : ℕ)
    (fit : base+a*b*c < 2^w) (bf : b < 2^w) (cf : c < 2^w)
    (pre : Memory w → Prop) (word : ℕ → Word w)
    (localValue : ∀ init, pre init → ∀ m, DescriptorScan.agreesOutside base (base+a*b*c) m init →
      ∀ (i : Fin a) (j : Fin b) (z : Fin c),
        e.eval data m ![(i.val:Word w),(j.val:Word w),(z.val:Word w)] =
          word (index base b c i.val j.val z.val)) :
    (scan e data base a b c).Spec pre (fun m o => o=fillSegment base (a*b*c) word m)
      (4+a*b*c*(2*(e.binds+16)+4)) := by
  unfold scan
  rw [← binds_decoded e base b c]
  apply PhysicalInputPhases.writing_spec _ _ _ _ fit pre word
  intro init yes dest m lo hi frame
  have dx : dest.val-base < a*b*c := by omega
  have cp : 0 < c := by by_contra! eq; simp [show c=0 by omega] at dx
  have bp : 0 < b := by by_contra! eq; simp [show b=0 by omega] at dx
  let row := (dest.val-base)/c
  have rs : row < a*b := (Nat.div_lt_iff_lt_mul cp).mpr dx
  let j : Fin b := ⟨row%b,Nat.mod_lt _ bp⟩
  let i : Fin a := ⟨row/b,(Nat.div_lt_iff_lt_mul bp).mpr rs⟩
  let z : Fin c := ⟨(dest.val-base)%c,Nat.mod_lt _ cp⟩
  have re : i.val*b+j.val=row := by simpa [i,j,Nat.mul_comm] using Nat.div_add_mod row b
  have loc : index base b c i.val j.val z.val=dest.val := by
    rw [index,re]
    have eq := Nat.div_add_mod (dest.val-base) c
    rw [Nat.mul_comm row c]
    dsimp [z,row]
    omega
  have equiv := at_index e base b c i.val j z m data (loc ▸ dest.isLt) bf cf
  rw [loc] at equiv
  simpa [loc] using equiv.trans (localValue init yes m frame i j z)

end Hierarchy.GridTopologyRAM

end OAI
