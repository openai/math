import OAI.ThreeFlat.RAM.PhysicalPinsExpr
import Mathlib.Tactic.FinCases
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Physical addressing for packed stage histogram rows -/

namespace ThreeFlat.RAM.AdmissionBank

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr
open scoped Classical Fin.CommRing

variable {w k n P R U : ℕ}

/-- Compile a formula whose public shape has been specialized to zero. -/
def closed : Formula n → Term w k n
  | .reg i => .result i
  | .lit a => .literal (Fin.ofNat _ a)
  | .param _ => .literal 0
  | .op b x y => .binary b (closed x) (closed y)
  | .cut x y => .select .lt (closed x) (closed y) (.literal 0) (.binary .sub (closed x) (closed y))
  | .load x => .load (closed x)
  | .select q x y a b => .select q (closed x) (closed y) (closed a) (closed b)

theorem eval_closed (f : Formula n) (data : Fin k → Word w) (m : Memory w) (vs : Fin n → Word w) :
    (closed f).eval data m vs = f.value (fun _ => 0) m vs := by
  induction f <;> simp [closed,Formula.value,Term.eval, *]

theorem binds_closed (f : Formula n) : (closed f : Term w k n).binds = f.work := by
  induction f <;> simp [closed,Formula.work,Term.literal,Term.binary,Term.select,Term.load,Term.binds, *] <;> omega

/-- The three inputs to the admission predicate are active width, count-array base, and copies. -/
def args (ctrl K : ℕ) : Fin 3 → Formula 1 :=
  let info : Formula 1 := .load (.lit ctrl)
  let dense := Formula.load (add info (.lit 1))
  let desc := Formula.load (add info (.lit 2))
  let row := add desc (mul (.lit 3) (.reg 0))
  ![.load (add row (.lit 2)),add dense (mul (.lit K) (.reg 0)),.load row]

def rowCount (ctrl : ℕ) (m : Memory w) := (m (m ctrl).val).val

def denseBase (ctrl : ℕ) (m : Memory w) := (m ((m ctrl).val+1)).val

def descBase (ctrl : ℕ) (m : Memory w) := (m ((m ctrl).val+2)).val

/-- Physical arrays for a complete stage. Counts and descriptor values may be arbitrary words. -/
structure Fits (ctrl K : ℕ) (m : Memory w) : Prop where
  ctrl_lt : ctrl<2^w
  info_lt : (m ctrl).val+2<2^w
  dense_le : denseBase ctrl m + K*rowCount ctrl m ≤ 2^w
  desc_le : descBase ctrl m + 3*rowCount ctrl m ≤ 2^w

private theorem cast_sum {a b : ℕ} (h : a+b<2^w) :
    ((a:Word w)+(b:Word w)).val=a+b := by
  rw [← Nat.cast_add,Fin.val_cast_of_lt h]

theorem arg_value (ctrl K i : ℕ) (m : Memory w) (h : Fits ctrl K m) (hi : i<rowCount ctrl m) :
    (fun j => (args ctrl K j).value (fun _ => 0) m (fun _ => (i:Word w))) =
      ![m (descBase ctrl m + 3*i+2),((denseBase ctrl m+K*i:ℕ):Word w),m (descBase ctrl m+3*i)] := by
  have info := h.info_lt
  have one : ((m ctrl)+(1:Word w)).val=(m ctrl).val+1 := by
    simpa only [Nat.cast_one,Fin.cast_val_eq_self] using cast_sum (w:=w) (a:=(m ctrl).val) (b:=1) (by omega)
  have two : ((m ctrl)+(2:Word w)).val=(m ctrl).val+2 := by
    simpa only [Nat.cast_ofNat,Fin.cast_val_eq_self] using cast_sum (w:=w) (a:=(m ctrl).val) (b:=2) info
  have dh := h.desc_le
  have d2 : descBase ctrl m + 3*i+2<2^w := by omega
  have d0 : descBase ctrl m + 3*i<2^w := by omega
  have desc : m ((m ctrl).val+2)=((descBase ctrl m : ℕ):Word w) := (Fin.cast_val_eq_self _).symm
  have dense : m ((m ctrl).val+1)=((denseBase ctrl m : ℕ):Word w) := (Fin.cast_val_eq_self _).symm
  have ctrlNat : (Fin.ofNat (2^w) ctrl).val=ctrl := Nat.mod_eq_of_lt h.ctrl_lt
  have wd : ((m ((m ctrl).val+2)) + (3:Word w)*(i:Word w)) = ((descBase ctrl m+3*i:ℕ):Word w) := by
    rw [desc,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have wb : ((m ((m ctrl).val+1))+(K:Word w)*(i:Word w)) = ((denseBase ctrl m+K*i:ℕ):Word w) := by
    rw [dense,Nat.cast_add,Nat.cast_mul]
  have w2 : (((descBase ctrl m+3*i:ℕ):Word w)+(2:Word w)).val = descBase ctrl m+3*i+2 := by
    simpa only [Nat.cast_ofNat] using cast_sum (w:=w) (b:=2) d2
  funext j
  fin_cases j
  · change m ((m ((m (Fin.ofNat _ ctrl).val + (2:Word w)).val) + (3:Word w)*(i:Word w) + (2:Word w)).val) = _
    rw [ctrlNat,two,wd,w2]; rfl
  · change m ((m (Fin.ofNat _ ctrl).val + (1:Word w)).val) + (K:Word w)*(i:Word w) = _
    rw [ctrlNat,one,wb]; rfl
  · change m ((m ((m (Fin.ofNat _ ctrl).val + (2:Word w)).val) + (3:Word w)*(i:Word w)).val) = _
    rw [ctrlNat,two,wd,Fin.val_cast_of_lt d0]; rfl

end ThreeFlat.RAM.AdmissionBank

end OAI
