import OAI.Hierarchy.DescentResetSuffixSplit
import OAI.Hierarchy.DescentFallbackLocalPrefix
import OAI.Hierarchy.DescentRelativeContacts

namespace OAI
/-! # Balanced reset rows from one measured suffix of the selected basis -/

namespace Hierarchy.DescentPlainTerminal.Suffix
open DescentColonies DescentGL DescentFineTerminals DescentIssuedFallbackPanel
open scoped BigOperators Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {m c r : ℕ}

def key (b : ℕ) (splitDepth : Block r→ℕ) (x : Block r) : ℕ×ℕ :=
  let d:=max b (splitDepth x)
  (d,group d x)

def prefixBase (b : ℕ) (before : Block r→Block r→Bool) (wt : Block r→ℕ) (x : Block r) :=
  ∑j : Block r,if before j x=true ∧ group b j=group b x then wt j else 0

def prefixLeaf (b : ℕ) (splitDepth : Block r→ℕ) (wt : Block r→ℕ) (x : Block r) :=
  ∑j : Block r,if j<x ∧ key b splitDepth j=key b splitDepth x then wt j else 0

/-- The compact pair and row, including the single-stack case at a hub. -/
def row (b hubDepth f B Y : ℕ) (isHub failed : Bool) (before : Block r→Block r→Bool)
    (splitDepth wt : Block r→ℕ) (x : Block r) : (ℕ×ℕ)×Option ℕ :=
  if isHub then ((hubDepth,group hubDepth x),none) else
    let «prefix»:=if failed then prefixLeaf b splitDepth wt x else prefixBase b before wt x
    (key b splitDepth x,some (min (Y*«prefix»/(2*(2^f*B))) (Y-1)))

def fieldsRelative (c : ℕ) (v : (ℕ×ℕ)×Option ℕ) : (ℕ×ℕ)×Option ℕ :=
  ((v.1.1-c,v.1.2%2^(v.1.1-c)),v.2)

theorem fields_relative {V : Type} {Y : ℕ} (c : ℕ) (z : V×DescentContacts.Endpoint Y) :
    fields ((DescentRelativeContacts.shortName c z).2)=fieldsRelative c (fields z.2) := rfl

variable (small : c≤m)
theorem group_short (hi : Block c) (d : ℕ) (lo : c≤d) (up : d≤m) (x : Block (m-c)) :
    group d (join small hi x)%2^(d-c)=group (d-c) x := by
  have add := join_group small hi x (d-c)
  rw [Nat.add_sub_of_le lo,show m-c-(m-c-(d-c))=d-c by omega] at add
  rw [add,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt]
  exact DescentHostDirectory.group_lt (by omega) x

theorem group_same (hi : Block c) (d : ℕ) (lo : c≤d) (x y : Block (m-c)) :
    group d (join small hi x)=group d (join small hi y) ↔ group (d-c) x=group (d-c) y := by
  have a:=join_group small hi x (d-c);have b:=join_group small hi y (d-c)
  rw [Nat.add_sub_of_le lo] at a b
  rw [a,b,Nat.add_right_inj]

omit [Fintype V] [DecidableEq V] in
theorem base_prefix (b : V→ℕ) (L : Layout m) (wt : V→Block m→ℕ) (v : V)
    (u : Block m) (lo : c≤b v) :
    let hi:=high small (rearrange L u)
    let x:=low (c:=c) (rearrange L u)
    baseSum b L wt v u=prefixBase (b v-c)
      (fun j i=>decide ((rearrange L).symm (join small hi j)<(rearrange L).symm (join small hi i)))
      (fun j=>wt v ((rearrange L).symm (join small hi j))) x := by
  dsimp only
  rw [baseSum_local small b L wt v u lo,prefixBase]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Equiv.apply_symm_apply,decide_eq_true_eq,join_high_low,Equiv.symm_apply_apply]
  have same:=group_same small (high small (rearrange L u)) (b v) lo j (low (c:=c) (rearrange L u))
  rw [join_high_low] at same
  simp only [same]

omit [Fintype V] [DecidableEq V] in
theorem leaf_relative (near : V→Finset V) (b : V→ℕ) (wt : V→Block m→ℕ)
    (f D B : ℕ) (safe : ∀v x,wt v x≤B) (v : V) (hi : Block c) (x : Block (m-c)) :
    leaf (D:=D) (f:=f) near wt safe b v (join small hi x)-c=
      (key (b v-c) (fun q=>depth (fun t j=>wt t (join small hi j)) (fun t z=>z∈near t) D (f+1) B
        (fun t _j=>safe t _) v q) x).1 := by
  have d:=depth_at small wt (fun t z=>z∈near t) D (f+1) B safe v hi x
  dsimp only [leaf,key]
  omega

omit [Fintype V] [DecidableEq V] in
theorem leaf_prefix (near : V→Finset V) (b : V→ℕ) (wt : V→Block m→ℕ)
    (f D B : ℕ) (safe : ∀v x,wt v x≤B) (v : V) (lo : c≤b v)
    (hi : Block c) (x : Block (m-c)) :
    leafSum b near wt f D B safe v (join small hi x)=
      prefixLeaf (b v-c) (fun q=>depth (fun t j=>wt t (join small hi j)) (fun t z=>z∈near t)
        D (f+1) B (fun t _j=>safe t _) v q) (fun j=>wt v (join small hi j)) x := by
  let depthAt:=leaf (D:=D) (f:=f) near wt safe b v
  let rel:=key (b v-c) (fun q=>depth (fun t j=>wt t (join small hi j)) (fun t z=>z∈near t)
    D (f+1) B (fun t j=>safe t _) v q)
  have lo' (j) : c≤depthAt (join small hi j) := lo.trans (le_max_left ..)
  have rel_d (j) : depthAt (join small hi j)-c=(rel j).1:=leaf_relative small near b wt f D B safe v hi j
  have keys (j) : leafKey (D:=D) (f:=f) near wt safe b v (join small hi j)=
      leafKey (D:=D) (f:=f) near wt safe b v (join small hi x) ↔ rel j=rel x := by
    constructor
    · intro eqn
      have sameD : depthAt (join small hi j)=depthAt (join small hi x):=congrArg Prod.fst eqn
      have sameId := congrArg Prod.snd eqn
      change group (depthAt _) (join small hi j)=group (depthAt _) (join small hi x) at sameId
      rw [sameD] at sameId
      apply Prod.ext
      · rw [←rel_d,←rel_d,sameD]
      · have both:=(group_same small hi _ (lo' x) j x).mp sameId
        change group (rel j).1 j=group (rel x).1 x
        rwa [←rel_d,←rel_d,sameD]
    · intro eqn
      have d₀:=congrArg Prod.fst eqn
      have dj:=rel_d j;have dx:=rel_d x;have lj:=lo' j;have lx:=lo' x
      have sameD : depthAt (join small hi j)=depthAt (join small hi x):=by omega
      apply Prod.ext sameD
      change group (depthAt _) (join small hi j)=group (depthAt _) (join small hi x)
      rw [sameD]
      apply (group_same small hi _ (lo' x) j x).mpr
      have snd:=congrArg Prod.snd eqn
      change group (rel j).1 j=group (rel x).1 x at snd
      rwa [←dj,←dx,sameD] at snd
  rw [leafSum_local small near b wt f D B safe v _ lo,high_join,prefixLeaf]
  apply Finset.sum_congr rfl
  intro j _
  have order : join small hi j<join small hi x ↔ j<x := by
    change hi.val*2^(m-c)+j.val<hi.val*2^(m-c)+x.val ↔ j.val<x.val
    omega
  simp only [order,keys]
  by_cases keep : j<x ∧ rel j=rel x <;>
    dsimp only [rel] at keep ⊢

omit [Fintype V] [DecidableEq V] in
/-- The original terminal formula after removing its common high block. -/
theorem row_at (near : V→Finset V) (b : V→ℕ) (L : Layout m) (wt : V→Block m→ℕ)
    (f D B g Y : ℕ) (safe : ∀v x,wt v x≤B) (bad : V→ℕ→Prop) (hub : V→Bool)
    (v : V) (hi : Block c) (x : Block (m-c)) (baseLow : c≤b v) (baseHigh : ∀t,b t≤m)
    (hubLow : c≤m-g) :
    let raw:=rearrangedLoad wt L
    let safe' (t j) : raw t j≤B:=safe t _
    let localWt:=fun t j=>raw t (join small hi j)
    let cut:=fun j=>depth localWt (fun t z=>z∈near t) D (f+1) B (fun t _j=>safe' t _) v j
    let before:=fun j i=>decide ((rearrange L).symm (join small hi j)<(rearrange L).symm (join small hi i))
    fieldsRelative c (endpoint near b L wt f D B g Y safe bad hub v ((rearrange L).symm (join small hi x)))=
      row (b v-c) (m-g-c) f B Y (hub v) (decide (bad v (group (b v) (join small hi x))))
        before cut (localWt v) x := by
  intro raw safe' localWt cut before
  cases hubMode : hub v with
  | true=>simp only [endpoint,row,hubMode,ite_true,Equiv.apply_symm_apply,fieldsRelative,
      group_short small hi _ hubLow (Nat.sub_le _ _) x]
  | false=>
    let jr:=join small hi x
    let d:=leaf (D:=D) (f:=f) near raw safe' b v jr
    have rel : d-c=(key (b v-c) cut x).1:=leaf_relative small near b raw f D B safe' v hi x
    have dl : c≤d:=baseLow.trans (le_max_left ..)
    have dh : d≤m:=max_le (baseHigh v) ((depth_le raw _ D (f+1) B safe' v jr).trans (Nat.sub_le _ _))
    have relId:=group_short small hi d dl dh x
    have bsum:= base_prefix small b L wt v ((rearrange L).symm jr) baseLow
    simp only [Equiv.apply_symm_apply,jr,high_join,low_join] at bsum
    have lsum:=leaf_prefix small near b raw f D B safe' v baseLow hi x
    simp only [endpoint,row,hubMode,Bool.false_eq_true,ite_false,Equiv.apply_symm_apply,fieldsRelative,
      decide_eq_true_eq,leafKey]
    change ((d-c,group d jr%2^(d-c)),some (min (Y*
      (if bad v (group (b v) jr) then leafSum b near raw f D B safe' v jr else
        baseSum b L wt v ((rearrange L).symm jr))/(2*(2^f*B))) (Y-1)))=_
    rw [show group d jr%2^(d-c)=group (d-c) x from relId,rel,lsum,bsum]
    by_cases failed : bad v (group (b v) (join small hi x)) <;>
      simp only [jr,failed,ite_true,ite_false,key,cut,localWt,before,raw,rearrangedLoad]

end
end Hierarchy.DescentPlainTerminal.Suffix

end OAI
