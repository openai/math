import OAI.Hierarchy.DescentRootPageCode
import OAI.Hierarchy.DescentFineTerminals
import OAI.Hierarchy.DescentBadVolume

namespace OAI
/-! # Group-independent addresses for the intervals of the physical reset bank -/

namespace Hierarchy.DescentResetHostSize
open DescentGL DescentColonies DescentContacts DescentHostDirectory DescentFineTerminals
open scoped Classical BigOperators
noncomputable section

/-- A legal reset interval lies wholly inside one of the new coarse blocks. -/
abbrev Interval (k r : ℕ) := {p : ℕ×ℕ // k-r≤p.1 ∧ p.1≤k ∧ p.2<2^p.1}

def split (k r : ℕ) : Interval k r ↪ Block (k-r)×Code r where
  toFun p :=
    let d := p.val.1-(k-r)
    (⟨p.val.2/2^d,(Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by
      rw [←Nat.pow_add,show (k-r)+d=p.val.1 by dsimp [d];have := p.property.1;omega]
      exact p.property.2.2)⟩,
     ⟨(d,p.val.2%2^d),mem_codes (by dsimp [d];have := p.property.2.1;omega) (Nat.mod_lt _ (Nat.two_pow_pos _))⟩)
  inj' := by
    rintro ⟨⟨i,x⟩,hx⟩ ⟨⟨j,y⟩,hy⟩ eqn
    have groupEq := congrArg (fun z : Block (k-r)×Code r=>z.1.val) eqn
    have levelEq := congrArg (fun z : Block (k-r)×Code r=>z.2.val.1) eqn
    have localEq := congrArg (fun z : Block (k-r)×Code r=>z.2.val.2) eqn
    change i-(k-r)=j-(k-r) at levelEq
    have hi : k-r≤ i := hx.1
    have hj : k-r≤j := hy.1
    have same : i=j := by omega
    subst j
    let h := 2^(i-(k-r))
    change x/h=y/h at groupEq
    change x%h=y%h at localEq
    have values : x=y := calc
      x=x%h+h*(x/h) := (Nat.mod_add_div ..).symm
      _=y := by rw [groupEq,localEq,Nat.mod_add_div]
    exact Subtype.ext (congrArg (fun z : ℕ => (i,z)) values)

/-- Realizing an interval from an old position recovers its coarse block. -/
theorem coarse_block {k r d : ℕ} (low : k-r≤d) (high : d≤k) (x : Block k) :
    ((split k r) ⟨(d,group d x),low,high,group_lt high x⟩).1.val=group (k-r) x := by
  change x.val/width k d/2^(d-(k-r))=x.val/width k (k-r)
  rw [Nat.div_div_eq_div_mul,width,width,←Nat.pow_add]
  rw [show k-d+(d-(k-r))=k-(k-r) by omega]

variable {V : Type} [Fintype V] [DecidableEq V] {k r D f g B Y : ℕ}
variable (near : V→Finset V) (wt : V→Block k→ℕ) (room : ∀v x,wt v x≤B)
variable (b : V→ℕ) (hub : V→Bool) (L : Layout k) (row : Bool→V×Block k→Fin Y)
variable (lo : ∀v,k-r≤b v) (hi : ∀v,b v≤k-f) (gr : g≤r)
local notation "H" => Directory (D:=D) (f:=f) (g:=g) near wt room b hub L row

include lo hi gr in
/-- The input names range only over actual old intervals, so even at a merged
hub their dyadic coordinates give a valid label in one coarse group. -/
theorem fallback_valid (t : ↥H) :
    k-r≤t.val.2.1.1 ∧ t.val.2.1.1≤k ∧ t.val.2.1.2<2^t.val.2.1.1 := by
  obtain ⟨⟨s,⟨v,x⟩⟩,_,eqn⟩ := Finset.mem_image.mp t.property
  rw [←eqn]
  cases h : hub v
  · let d := leaf (D:=D) (f:=f) near wt room b v (rearrange L x)
    have low : k-r≤d := (lo v).trans (le_max_left ..)
    have high : d≤k := (leaf_le (D:=D) near wt room b hi v _).trans (Nat.sub_le ..)
    simpa only [name,h,Bool.false_eq_true,ite_false,Prod.fst,Prod.snd] using
      And.intro low (And.intro high (group_lt high (rearrange L x)))
  · have low : k-r≤k-g := by omega
    have high : k-g≤k := Nat.sub_le ..
    simpa only [name,h,ite_true,Prod.fst,Prod.snd] using
      And.intro low (And.intro high (group_lt high (rearrange L x)))

/-- Sites of either species share the same dictionary of relative intervals.
The tag distinguishes a rotor base from a hub or a named nonhub input row. -/
abbrev Tag (Y : ℕ) := Unit ⊕ Option (Fin Y)
abbrev Position (V : Type) (r Y : ℕ) := V×Code r×Tag Y

/-- Split any injective vertex/interval/row label into coarse group and common
position. Its codomain has no dependence on the number of coarse groups. -/
def address {S : Type*} (describe : S ↪ V×Interval k r×Tag Y) :
    S ↪ Block (k-r)×Position V r Y where
  toFun s :=
    let (v,a,t) := describe s
    let (g,c) := split k r a
    (g,v,c,t)
  inj' := by
    intro a b eqn
    apply describe.injective
    have v := congrArg (fun z : Block (k-r)×Position V r Y=>z.2.1) eqn
    have t := congrArg (fun z : Block (k-r)×Position V r Y=>z.2.2.2) eqn
    have e := congrArg (fun z : Block (k-r)×Position V r Y=>(z.1,z.2.2.1)) eqn
    exact Prod.ext v (Prod.ext ((split k r).injective e) t)

end
end Hierarchy.DescentResetHostSize

end OAI
