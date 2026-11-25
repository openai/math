import OAI.Hierarchy.DescentResetIntervalAddress
import OAI.Hierarchy.DescentContactCodes

namespace OAI
/-! # The full fallback contact roster in a coarse block's own coordinates -/

namespace Hierarchy.DescentRelativeContacts
open DescentGL DescentColonies DescentContacts DescentFineTerminals DescentHostDirectory DescentResetHostSize
open scoped Classical BigOperators
noncomputable section

def residue (r : ℕ) {k : ℕ} (x : Block k) : Block r := ⟨x.val%2^r,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
def coarse {V : Type} {Y : ℕ} (k r : ℕ) (z : V×Endpoint Y) : ℕ :=
  z.2.1.2/2^(z.2.1.1-(k-r))

def shortName {V : Type} {Y : ℕ} (m : ℕ) (z : V×Endpoint Y) : V×Endpoint Y :=
  let d := z.2.1.1-m
  (z.1,((d,z.2.1.2%2^d),z.2.2))

abbrev relative {V : Type} {Y : ℕ} (k r : ℕ) (z : V×Endpoint Y) := shortName (k-r) z

theorem id_relative {k r d : ℕ} (rk : r≤k) (lo : k-r≤d) (hi : d≤k) (x : Block k) :
    group d x%2^(d-(k-r))=group (d-(k-r)) (residue r x) := by
  let e := d-(k-r)
  have factor : 2^r=2^(k-d)*2^e := by rw [←Nat.pow_add]; congr 1; dsimp [e]; omega
  change x.val/2^(k-d)%2^e=x.val%2^r/2^(r-e)
  rw [show r-e=k-d by dsimp [e];omega,factor,Nat.mod_mul_right_div_self]

/-- A normalized name and a coarse block determine the original interval;
this permits any full local catalogue to name the actual observed links. -/
theorem relative_injective {V : Type} {Y k r : ℕ} {a b : V×Endpoint Y}
    (aok : k-r≤a.2.1.1) (bok : k-r≤b.2.1.1)
    (same : coarse k r a=coarse k r b) (loc : relative k r a=relative k r b) : a=b := by
  obtain ⟨v,⟨d,id⟩,tag⟩ := a
  obtain ⟨w,⟨e,j⟩,other⟩ := b
  have vEq : v=w := congrArg Prod.fst loc
  have tEq : tag=other := congrArg (fun s : V×Endpoint Y=>s.2.2) loc
  have lEq : d-(k-r)=e-(k-r) := congrArg (fun s : V×Endpoint Y=>s.2.1.1) loc
  have sd : d=e := by change k-r≤d at aok;change k-r≤e at bok;omega
  subst e
  let M := 2^(d-(k-r))
  have rem : id%M=j%M := congrArg (fun s : V×Endpoint Y=>s.2.1.2) loc
  change id/M=j/M at same
  have ij : id=j := calc id=id%M+M*(id/M) := (Nat.mod_add_div ..).symm
                         _=j := by rw [same,rem,Nat.mod_add_div]
  subst w
  subst j
  subst other
  rfl

variable {V : Type} [Fintype V] [DecidableEq V] {k r g D f B Y : ℕ}
variable (near : V→Finset V) (mass : V→Block k→ℕ) (room : ∀v i,mass v i≤B)
variable (b : V→ℕ) (hub : V→Bool) (L : Layout k) (row : Bool→V×Block k→Fin Y)
local notation "d" => leaf (D:=D) (f:=f) near mass room b
local notation "N" => name (D:=D) (f:=f) (g:=g) near mass room b hub L row

omit [Fintype V] [DecidableEq V] in
theorem coarse_name (base : ∀v,k-r≤b v) (fit : ∀v,b v≤k-f) (gr : g≤r)
    (s : Bool) (o : V×Block k) : coarse k r (N s o)=group (k-r) (rearrange L o.2) := by
  let x := rearrange L o.2
  have low : k-r≤d o.1 x := (base _).trans (le_max_left ..)
  have high : d o.1 x≤k := (leaf_le (D:=D) near mass room b fit _ x).trans (Nat.sub_le ..)
  have atDepth (a : ℕ) (lower : k-r≤a) (upper : a≤k) :
      group a x/2^(a-(k-r))=group (k-r) x := by
    change x.val/2^(k-a)/2^(a-(k-r))=x.val/2^(k-(k-r))
    rw [Nat.div_div_eq_div_mul,←Nat.pow_add,show k-a+(a-(k-r))=k-(k-r) by omega]
  cases h : hub o.1
  · exact (by simpa [name,coarse,h,x] using
      (atDepth _ low high))
  · exact (by simpa [name,coarse,h,x] using
      (atDepth _ (by omega : k-r≤k-g) (Nat.sub_le ..)))

private def port {Z : ℕ} (isHub : Bool) (mer depth : ℕ) (x : Block Z) (r : Fin Y) : Endpoint Y :=
  if isHub then ((mer,group mer x),none) else ((depth,group depth x),some r)

omit [Fintype V] [DecidableEq V] in
/-- Rebase each physical terminal without retaining its old coarse index. -/
theorem relative_name (rk : r≤k) (base : ∀v,k-r≤b v) (fit : ∀v,b v≤k-f) (gr : g≤r)
    (s : Bool) (o : V×Block k) :
    relative k r (N s o)=(o.1,port (hub o.1) (r-g) (d o.1 (rearrange L o.2)-(k-r))
      (residue r (rearrange L o.2)) (row s o)) := by
  let x := rearrange L o.2
  have low : k-r≤d o.1 x := (base _).trans (le_max_left ..)
  have high : d o.1 x≤k := (leaf_le (D:=D) near mass room b fit _ x).trans (Nat.sub_le ..)
  cases z : hub o.1
  · simp [name,relative,shortName,port,z,id_relative rk low high, x]
  · have level : k-g-(k-r)=r-g := by omega
    have rebased := id_relative rk (show k-r≤k-g by omega) (Nat.sub_le k g) x
    rw [level] at rebased
    simpa [name,relative,shortName,port,z,level,x] using rebased

omit [Fintype V] in
theorem normalized_neighbor (rk : r≤k) (base : ∀v,k-r≤b v) (fit : ∀v,b v≤k-f)
    (smooth : ∀v w,w∈near v→b v≤b w+D) (full : ∀v,hub v=true→b v=k-f)
    (fg : f≤g) (gr : g≤r) {v w : V} (vw : w∈near v) (wv : v∈near w)
    (one : ¬(hub v=true ∧ hub w=true)) (s t : Bool) (i : Block k) :
    relative k r (N t (w,i)) ∈ window (k:=r) (g:=g) (f:=f) (D:=D) near hub (relative k r (N s (v,i))) := by
  rw [relative_name near mass room b hub L row rk base fit gr,relative_name near mass room b hub L row rk base fit gr]
  let x := rearrange L i
  let y := residue r x
  let dv := d v x-(k-r)
  let dw := d w x-(k-r)
  have dl := leaf_le (D:=D) near mass room b fit v x
  have el := leaf_le (D:=D) near mass room b fit w x
  have ds : k-r≤d v x := (base v).trans (le_max_left ..)
  have es : k-r≤d w x := (base w).trans (le_max_left ..)
  have vup := leaf_near (f:=f) near mass room b smooth vw x
  have wup := leaf_near (f:=f) near mass room b smooth wv x
  have up : dv≤dw+D := by dsimp [dv,dw];omega
  have down : dw≤dv+D := by dsimp [dv,dw];omega
  have vr : dv≤r-f := by dsimp [dv]; omega
  have wr : dw≤r-f := by dsimp [dw]; omega
  have size {a : ℕ} (depthBound : r-f≤a+D) : width r a≤2^D*2^f := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  cases vh : hub v <;> cases wh : hub w
  · simpa only [port,window,vh,wh,Bool.false_eq_true,ite_false,Option.isSome_some,
      Bool.true_eq,ite_true,dv,dw,y,x] using
      (names_mem (near:=near v) (f:=fun z=>fromNonhub Y dv (group dv y) D (r-g) (hub z))
        vw (by
          simpa only [wh] using (nonhub_nonhub_mem (h:=r-g) (vr.trans (Nat.sub_le ..))
            (wr.trans (Nat.sub_le ..)) up down y (row t (w,i)))))
  · have hv := hub_leaf (D:=D) near mass room b hub fit full wh x
    have large : width r dv≤2^D*2^f := size (by dsimp [dv];omega)
    simpa only [port,window,vh,wh,Bool.false_eq_true,ite_false,Option.isSome_some,
      Bool.true_eq,ite_true,dv,y,x] using
      (names_mem (near:=near v) (f:=fun z=>fromNonhub Y dv (group dv y) D (r-g) (hub z))
        vw (by simpa only [wh] using nonhub_hub_mem (Y:=Y) fg (vr.trans (Nat.sub_le ..)) large y))
  · have hv := hub_leaf (D:=D) near mass room b hub fit full vh x
    have large : width r dw≤2^D*2^f := size (by dsimp [dw];omega)
    have small : 2^f≤width r dw := Nat.pow_le_pow_right (by decide) (by omega)
    simpa only [port,window,vh,wh,Bool.false_eq_true,ite_false,Option.isSome_none,
      Bool.true_eq,ite_true,dw,y,x] using
      (names_mem (near:=near v) (f:=fun _=>terminals Y (possible (r-g) (group (r-g) y) D (g-f)))
        vw (terminal_mem (hub_meeting fg gr (wr.trans (Nat.sub_le ..)) small large y) (row t (w,i))))
  · exact (one ⟨vh,wh⟩).elim

end
end Hierarchy.DescentRelativeContacts

end OAI
