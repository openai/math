import OAI.ThreeFlat.Diagonal.CompressorRefreshROM
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Evaluation of the outgoing and incoming refresh adjacency rows -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Refresh

open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM.DescriptorExpr
open Placement
open scoped Fin.CommRing

variable {w k D a : ℕ}

/-- Integer data carried by a six-column refresh row. On an external slot its
three fields come from that orientation's old slot, while the sparse internal
and padding slots have zero displacement. -/
def fieldWord (E : SlotGraph (Fin D) a) (reverse : Bool) (which : Field) (v : ℕ) (j : Fin D)
    (slot : ℕ) (next mate shift : Word w) : Word w :=
  if slot=0 then
    match which with
    | .neighbor => next*(D:Word w)+mate
    | .matePort => 0
    | .delta => shift
  else if hi : slot-1<a then
    let p := (if reverse then E.target.symm else E.target) (j,⟨slot-1,hi⟩)
    match which with
    | .neighbor => ((v*D+p.1.val:ℕ):Word w)
    | .matePort => ((1+p.2.val:ℕ):Word w)
    | .delta => 0
  else
    match which with
    | .neighbor => ((v*D+(j.val+(if reverse then D-1 else 1))%D:ℕ):Word w)
    | .matePort => (slot:Word w)
    | .delta => 0

private theorem div_cast {x y : ℕ} (hx : x<2^w) (hy : y<2^w) :
    BinaryOp.div.eval (x:Word w) (y:Word w) = ((x/y:ℕ):Word w) := by
  simp [BinaryOp.eval,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]
private theorem word_mod {x y : ℕ} (hx : x<2^w) (hy : y<2^w) :
    BinaryOp.mod.eval (x:Word w) (y:Word w) = ((x%y:ℕ):Word w) := by
  simp [BinaryOp.eval,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

private theorem unRow (r : ℕ) {j n : ℕ} (hj : j<n) :
    (r*n+j)/n = r ∧ (r*n+j)%n = j := by
  rw [Nat.mul_comm r,Nat.mul_add_div (Nat.zero_lt_of_lt hj),Nat.div_eq_of_lt hj,Nat.add_zero,
    Nat.mul_add_mod,Nat.mod_eq_of_lt hj]
  exact ⟨rfl,rfl⟩

theorem row_read (E : SlotGraph (Fin D) a) (reverse : Bool) (pad : ℕ) (which : Field)
    (old : OldColumns (Term w k 1)) (out : Term w k 1) (pub : Fin k → Word w)
    (mem : Memory w) (vs : Fin 1 → Word w) (v : ℕ) (j : Fin D) (s : Fin (1+a+pad))
    (idx : vs 0 = out.eval pub mem vs + ((((v*D+j.val)*(1+a+pad)+s.val):ℕ):Word w))
    (hrow : (v*D+j.val)*(1+a+pad)+s.val < 2^w) (hdeg : 1+a+pad < 2^w)
    (hD : D<2^w) (hptr : D*a ≤ 2^w) (hrot : j.val+(if reverse then D-1 else 1)<2^w) :
    let p := ((v*D+j.val:ℕ):Word w)
    (row E reverse pad which old out).eval pub mem vs =
      fieldWord E reverse which v j s.val
        (mem (old.neighbor.eval pub mem vs+p).val)
        (mem (old.mate.eval pub mem vs+p).val)
        (mem (old.remainingShift.eval pub mem vs+p).val) := by
  let deg := 1+a+pad
  let site := v*D+j.val
  let key := site*deg+s.val
  let z : Term w k 1 := .binary .sub (.result 0) out
  let atSite : Term w k 1 := .binary .div z (.literal (deg:Word w))
  let atBase : Term w k 1 := .binary .div atSite (.literal (D:Word w))
  let atPort : Term w k 1 := .binary .mod atSite (.literal (D:Word w))
  let atSlot : Term w k 1 := .binary .mod z (.literal (deg:Word w))
  let lookup : Term w k 1 := .binary .add (.binary .mul atPort (.literal (a:Word w)))
    (.binary .sub atSlot (.literal 1))
  let ev := fun (e : Term w k 1) => e.eval pub mem vs
  have hz : ev z=(key:Word w) := by
    dsimp only [ev,z]
    rw [Term.eval_binary]
    change vs 0-out.eval pub mem vs=_
    rw [idx]; abel
  have hs : ev atSite=(site:Word w) := by
    dsimp only [ev,atSite]
    rw [Term.eval_binary,Term.eval_literal]
    change BinaryOp.div.eval (ev z) _=_
    rw [hz,div_cast hrow hdeg,(unRow site s.isLt).1]
  have he : ev atSlot=(s.val:Word w) := by
    dsimp only [ev,atSlot]
    rw [Term.eval_binary,Term.eval_literal]
    change BinaryOp.mod.eval (ev z) _=_
    rw [hz,word_mod hrow hdeg,(unRow site s.isLt).2]
  have small : site < 2^w := by
    have dvd := (unRow site s.isLt).1
    rw [←dvd]
    exact (Nat.div_le_self _ _).trans_lt hrow
  have hv : ev atBase=(v:Word w) := by
    dsimp only [ev,atBase]
    rw [Term.eval_binary,Term.eval_literal]
    change BinaryOp.div.eval (ev atSite) _=_
    rw [hs,div_cast small hD,(unRow v j.isLt).1]
  have hj : ev atPort=(j.val:Word w) := by
    dsimp only [ev,atPort]
    rw [Term.eval_binary,Term.eval_literal]
    change BinaryOp.mod.eval (ev atSite) _=_
    rw [hs,word_mod small hD,(unRow v j.isLt).2]
  have hslot : s.val < 2^w := s.isLt.trans hdeg
  have ha : 1+a < 2^w := by omega
  have rotate :
      BinaryOp.mod.eval ((j.val:Word w)+((if reverse then D-1 else 1:ℕ):Word w)) (D:Word w) =
        (((j.val+(if reverse then D-1 else 1:ℕ))%D:ℕ):Word w) := by
    rw [← Nat.cast_add,word_mod hrot hD]
  have binary (op : BinaryOp) {x y : Term w k 1} {u v' : Word w} (ex : ev x=u) (ey : ev y=v') :
      ev (.binary op x y)=op.eval u v' :=
    (Term.eval_binary ..).trans (congrArg₂ op.eval ex ey)
  have lit (i : ℕ) : ev (.literal (i:Word w))=(i:Word w) := Term.eval_literal ..
  have yes (c : Comparison) (x y : Term w k 1) (hit : c.test (ev x) (ev y)=true) (u v' : Term w k 1) :
      ev (.select c x y u v')=ev u := by rw [show ev (.select c x y u v') = _ from Term.eval_select ..,hit]; rfl
  have no (c : Comparison) (x y : Term w k 1) (miss : c.test (ev x) (ev y)=false) (u v' : Term w k 1) :
      ev (.select c x y u v')=ev v' := by rw [show ev (.select c x y u v') = _ from Term.eval_select ..,miss]; rfl
  have hinternal {hi : s.val-1<a} (hs₀ : s.val≠0) (f : Fin D × Fin a → ℕ) :
      ev (findWord lookup (portROM E reverse f)) =
        ((f ((if reverse then E.target.symm else E.target) (j,⟨s.val-1,hi⟩))):Word w) := by
    apply eval_port E reverse f hptr (j,⟨s.val-1,hi⟩)
    have e := binary .add (binary .mul hj (lit a)) (binary .sub he (lit 1))
    refine e.trans ?_
    change (j.val:Word w)*(a:Word w)+((s.val:Word w)-1)=((j.val*a+(s.val-1):ℕ):Word w)
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1≤ s.val),Nat.cast_one]
  have proj (base : Term w k 1) :
      ev (Placement.row (terms w k 1) base atSite) = mem (ev base+(site:Word w)).val := by
    change (Term.load (.binary .add base atSite)).eval pub mem vs = _
    rw [Term.eval_load]
    exact congrArg (fun w : Word w => mem w.val) (binary .add (rfl : ev base=ev base) hs)
  have zCmp : Comparison.eq.test (ev atSlot) (ev (.literal ((0:ℕ):Word w))) = decide (s.val=0) := by
    rw [he,lit,Nat.cast_zero]
    change ((s.val:Word w)==0) = _
    by_cases equal : s.val=0
    · simp [equal]
    · have diff : (s.val:Word w)≠0 := fun h => equal ((Fin.val_cast_of_lt hslot).symm.trans (congrArg Fin.val h))
      simp [equal,diff]
  have lCmp : Comparison.lt.test (ev atSlot) (ev (.literal ((1+a:ℕ):Word w))) = decide (s.val<1+a) := by
    rw [he,lit]
    change decide ((s.val:Word w).val<((1+a:ℕ):Word w).val)=_
    rw [Fin.val_cast_of_lt hslot,Fin.val_cast_of_lt ha]
  dsimp only
  by_cases s₀ : s.val=0
  · have keep := yes .eq atSlot (.literal ((0:ℕ):Word w)) (zCmp.trans (decide_eq_true s₀))
    simp only [fieldWord,ite_eq_left s₀]
    cases which with
    | neighbor => exact (keep _ _).trans (binary .add (binary .mul (proj old.neighbor) (lit D)) (proj old.mate))
    | matePort => exact (keep _ _).trans (lit 0)
    | delta => exact (keep _ _).trans (proj old.remainingShift)
  · have skip := no .eq atSlot (.literal ((0:ℕ):Word w)) (zCmp.trans (decide_eq_false s₀))
    by_cases inner : s.val-1<a
    · have use := yes .lt atSlot (.literal ((1+a:ℕ):Word w)) (lCmp.trans (decide_eq_true (by omega)))
      simp only [fieldWord,ite_eq_right s₀,dite_eq_left inner]
      cases which with
      | neighbor =>
        refine (skip _ _).trans ((use _ _).trans ((binary .add (binary .mul hv (lit D)) (hinternal (hi:=inner) s₀ (fun p => p.1.val))).trans ?_))
        simp [BinaryOp.eval]
      | matePort =>
        refine (skip _ _).trans ((use _ _).trans ((binary .add (lit 1) (hinternal (hi:=inner) s₀ (fun p => p.2.val))).trans ?_))
        simp [BinaryOp.eval]
      | delta => exact (skip _ _).trans ((use _ _).trans (lit 0))
    · have use := no .lt atSlot (.literal ((1+a:ℕ):Word w)) (lCmp.trans (decide_eq_false (by omega)))
      simp only [fieldWord,ite_eq_right s₀,dite_eq_right inner]
      cases which with
      | neighbor =>
        have rot := (binary .mod (binary .add hj (lit (if reverse then D-1 else 1))) (lit D)).trans rotate
        refine (skip _ _).trans ((use _ _).trans ((binary .add (binary .mul hv (lit D)) rot).trans ?_))
        simp [BinaryOp.eval]
      | matePort => exact (skip _ _).trans ((use _ _).trans he)
      | delta => exact (skip _ _).trans ((use _ _).trans (lit 0))

end ThreeFlat.Diagonal.CompressorPacking.Native.Refresh

end OAI
