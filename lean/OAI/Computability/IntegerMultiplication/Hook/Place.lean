import OAI.Computability.IntegerMultiplication.Axon.Tuple
import OAI.Computability.IntegerMultiplication.Staff.Tabs
import OAI.Computability.IntegerMultiplication.Curtain.Reduce

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Code Adic Packed Net Net.Walsh Earth IntegerMultiplication.Fourier Curtain Staff Loom
open Finset
variable (f g k m : ℕ)
abbrev Ht := g*k+m
abbrev Len := f* Ht g k m
abbrev Pkg := Fin g × Fin k ⊕ Fin m
abbrev Grind := Fin f × Pkg g k m
abbrev knot : Pkg g k m ≃ Fin (Ht g k m) :=
  (finProdFinEquiv.sumCongr (.refl _)).trans finSumFinEquiv
def packR : Grind f g k m ≃ Fin (Len f g k m) :=
  ((Equiv.refl _).prodCongr (knot ..)).trans finProdFinEquiv

theorem len_alt : g*(f*k)+f*m=Len f g k m := by unfold Len Ht; ring
abbrev swapXY : Fin f × Fin g × Fin k ≃ Fin g × Fin f × Fin k :=
  (((Equiv.prodAssoc _ _ _).symm.trans ((Equiv.prodComm _ _).prodCongr (Equiv.refl _))).trans (Equiv.prodAssoc ..))
abbrev tok : Fin f × Fin g × Fin k ≃ Fin (g*(f*k)) :=
  ((swapXY ..).trans ((Equiv.refl _).prodCongr finProdFinEquiv)).trans finProdFinEquiv
def packC : Grind f g k m ≃ Fin (Len f g k m) :=
  (((Equiv.prodSumDistrib ..).trans ((tok ..).sumCongr finProdFinEquiv)).trans finSumFinEquiv).trans
    (finCongr (len_alt ..))

def gather : Equiv.Perm (Fin (Len f g k m)) :=
  (packR ..).symm.trans (packC ..)
variable {f g k m}
private theorem a (i : Fin f) (j : Fin g) (u:Fin k) :
    (packR f g k m (i,.inl (j,u))).val=i.val*Ht g k m+j.val*k+u.val := by
  change u.val+k*j.val+Ht g k m*i.val=_
  ring
private theorem b (i : Fin f) (j : Fin g) (u:Fin k) :
    (packC f g k m (i,.inl (j,u))).val=j.val*(f*k)+i.val*k+u.val := by
  change u.val+k*i.val+(f*k)*j.val=_
  ring
private theorem c (i : Fin f) (u:Fin m) :
    (packR f g k m (i,.inr u)).val=i.val*Ht g k m+g*k+u.val := by
  change g*k+u.val+Ht g k m*i.val=_
  ring
private theorem d (i : Fin f) (u:Fin m) :
    (packC f g k m (i,.inr u)).val=g*(f*k)+i.val*m+u.val := by
  change g*(f*k)+(u.val+m*i.val)=_
  ring

variable (f g k m)
def lR (n : ℕ) :=
  let c := n/Ht g k m
  let s := n%Ht g k m
  if s<  g*k then s/k*(f*k)+c*k+s%k else g*(f*k)+c*m+(s-g*k)
def βR (n : ℕ) :=
  let s := n%(f*k)
  let c := n/(f*k)
  let y := n-g*(f*k)
  if n<  g*(f*k) then s/k*Ht g k m+c*k+s%k else y/m*Ht g k m+g*k+y%m
-- natural div mod
private theorem euclid {a b c:ℕ} (h:b< c) :
    (a*c+b)/c=a ∧ (a*c+b)%c=b := by
  have u : c>0 := by omega
  rw [Nat.add_comm (a*_)]
  rw [Nat.mul_comm a]
  simp [Nat.add_mul_div_left .., Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h, u]

theorem am_ (i:Grind f g k m) :
    let R := packR f g k m
    let C := packC f g k m
    lR f g k m (R i).val = (C i).val := by
  rcases i with ⟨i,⟨j,u⟩|u⟩
  · dsimp only
    rw [a,b]
    have h := u.isLt
    have y : j.val*k+u.val <  g*k := by have e:= j.isLt; nlinarith
    unfold lR; rw [Nat.add_assoc (i.val*_)]
    have D := euclid (a:=i.val) (lt_of_lt_of_le y (Nat.le_add_right ..) : j.val*k+u.val <  Ht g k m)
    rw [D.1,D.2, ite_eq_left y,(euclid (a:=j.val) h).1,(euclid (a:=j.val) h).2]
  dsimp only
  rw [c,d]
  unfold lR; rw [Nat.add_assoc (i.val*_)]
  have h : g*k+u.val <  Ht g k m := by unfold Ht; have := u.isLt; omega
  rw [(euclid (a:=i.val) h).1]; dsimp only; rw [(euclid (a:=i.val) h).2,ite_eq_right (by omega),Nat.add_sub_cancel_left]
theorem bm_ (i:Grind f g k m) :
    let R := packR f g k m
    let C := packC f g k m
    βR f g k m (C i).val=(R i).val := by
  rcases i with ⟨i,⟨j,u⟩|u⟩
  · dsimp only
    rw [a,b,Nat.add_assoc (j.val*_)]
    unfold βR
    have e := u.isLt; have t := i.isLt
    have h : i.val*k+u.val< f*k := by nlinarith
    have z : j.val*(f*k)+(i.val*k+u.val)< g*(f*k) := by have z := Nat.mul_le_mul_right (f*k) j.isLt; nlinarith
    rw [(euclid (a:=j.val) h).2,(euclid (a:=j.val) h).1]; dsimp only; rw [(euclid (a:=i.val) e).1,(euclid (a:=i.val) e).2,ite_eq_left z]
  dsimp only; rw [c,d,Nat.add_assoc (g*_)]
  unfold βR
  rw [Nat.add_sub_cancel_left,ite_eq_right (by omega),(euclid (a:=i.val) u.isLt).1,(euclid (a:=i.val) u.isLt).2]

-- uniform selector π
private theorem formula (i : Fin (Len f g k m)) :
    (gather _ _ _ _ i).val =
      lR f g k m i.val := by
  obtain ⟨j,rfl⟩ := (packR f g k m).surjective i
  have e := am_ f g k m j
  unfold gather; rw [Equiv.trans_apply,Equiv.symm_apply_apply]; exact e.symm
private theorem formula' (i : Fin (Len f g k m)) :
    ((gather _ _ _ _).symm i).val=βR f g k m i.val := by
  obtain ⟨j,rfl⟩ := (packC f g k m).surjective i
  exact (show _= _ by unfold gather; rw [Equiv.symm_trans_apply,Equiv.symm_apply_apply]; exact (bm_ ..).symm)

-- lift to Regime.Has
variable {I:Type} {r : Strip.Regime I} {x y l t : I→ℕ}
variable (h : Realizes r x) (q : Realizes r y) (v : Realizes r l) (s : Realizes r t)
include h q v s

theorem realizes_n :
    Realizes r (fun i=>Len (x i) (y i) (l i) (t i)) := h.times ((q.times v).plus s)
theorem gatherMask :
    r.Has fun i=> Curtain.paint (gather (x i) (y i) (l i) (t i)) := by
  let Q i := Len (x i) (y i) (l i) (t i)
  let A := Across Q
  have R := realizes_n h q v s
  let w (i:A) := i.1
  have D := floor_ Q R
  apply harvest Q R
  have u (p:I→ℕ) (e : Realizes r p) := landing Q R p e
  simp_rw [formula]
  have X := u _ h
  have Y := u _ q
  have L := u _ v
  have T := u _ s
  -- use select
  have H := (Y.times L).plus T
  have C := D.dividing H
  have J := D.rem H
  exact Realizes.select (((J.dividing L).times (X.times L)|>.plus (C.times L)).plus (J.rem L))
    (((Y.times (X.times L)).plus (C.times T)).plus (J.minused (Y.times L))) (J.below (Y.times L))

theorem ungather :
    r.Has fun i=> Curtain.paint (gather (x i) (y i) (l i) (t i)).symm := by
  let Q i := Len (x i) (y i) (l i) (t i)
  have R := realizes_n h q v s
  have D := floor_ Q R
  apply harvest Q R
  have u (p:I→ℕ) (e : Realizes r p) := landing Q R p e
  simp_rw [formula']
  have X := u _ h
  have Y := u _ q
  have L := u _ v
  have T := u _ s
  have H := X.times L
  have C := D.dividing H
  have J := D.rem H
  have Q := D.minused (Y.times H)
  exact Realizes.select ((((J.dividing L).times ((Y.times L).plus T)).plus (C.times L)).plus (J.rem L))
    ((((Q.dividing T).times ((Y.times L).plus T)).plus (Y.times L)).plus (Q.rem T))
    (D.below (Y.times H))
end Hook

end IntegerMultiplication
end Computability
end OAI
