import OAI.Hierarchy.DescentContactNumbers
import OAI.Hierarchy.DescentColonyLayout

namespace OAI
/-! # The actual dyadic terminal directory after refinement and hub merging -/

namespace Hierarchy.DescentFineTerminals
open DescentColonies DescentContacts DescentGL
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k f B D Y g : ℕ}

/-- Stop at the first unsplit interval below the given base. The load threshold
for another split is twice the grouping amount times the maximum old load. -/
def leaf (near : V→Finset V) (mass : V→Block k→ℕ) (room : ∀v i,mass v i≤B)
    (b : V→ℕ) (v : V) (x : Block k) : ℕ :=
  max (b v) (depth mass (fun z w=>w∈near z) D (f+1) B room v x)

variable (near : V→Finset V) (mass : V→Block k→ℕ) (room : ∀v i,mass v i≤B)
variable (b : V→ℕ) (hub : V→Bool) (L : Layout k) (row : Bool→V×Block k→Fin Y)
local notation "d" => leaf (D:=D) (f:=f) near mass room b

omit [Fintype V] [DecidableEq V] in
theorem leaf_le (fit : ∀v,b v≤k-f) (v : V) (x : Block k) : d v x≤k-f := by
  exact max_le (fit v) ((depth_le mass _ D (f+1) B room v x).trans (by omega))

omit [Fintype V] [DecidableEq V] in
theorem leaf_near (smooth : ∀v w,w∈near v→b v≤b w+D)
    {v w : V} (edge : w∈near v) (x : Block k) : d v x≤d w x+D := by
  have h₁ := smooth v w edge
  have h₂ := neighbor_depth mass (fun z q=>q∈near z) D (f+1) B room edge x
  unfold leaf
  omega

omit [Fintype V] [DecidableEq V] in
theorem hub_leaf (fit : ∀v,b v≤k-f) (full : ∀v,hub v=true→b v=k-f)
    {v : V} (atHub : hub v=true) (x : Block k) : d v x=k-f :=
  le_antisymm (leaf_le near mass room b fit v x) (by rw [←full v atHub]; exact le_max_left ..)

/-- The row is part of a nonhub terminal name. At a hub there is a single
stack for its merged interval. Both cases use the shared physical remix. -/
def name (s : Bool) (o : V×Block k) : V×Endpoint Y :=
  let x := rearrange L o.2
  if hub o.1 then (o.1,((k-g,group (k-g) x),none))
  else (o.1,((d o.1 x,group (d o.1 x) x),some (row s o)))

local notation "N" => name (D:=D) (f:=f) (g:=g) near mass room b hub L row

/-- Only realized old terminal names occur. In particular, the two natural
number coordinates of the public name do not require an infinite carrier. -/
abbrev Directory := Finset.univ.image (fun p : Bool×(V×Block k)=>N p.1 p.2)

def terminal (s : Bool) (o : V×Block k) :
    ↥(Directory (D:=D) (f:=f) (g:=g) near mass room b hub L row) :=
  ⟨N s o,Finset.mem_image.mpr ⟨(s,o),Finset.mem_univ _,rfl⟩⟩

/-- The candidate list depends only on the public name of the source. -/
def window (near : V→Finset V) (hub : V→Bool) (z : V×Endpoint Y) : Finset (V×Endpoint Y) :=
  if z.2.2.isSome then names (near z.1)
    (fun w=>fromNonhub Y z.2.1.1 z.2.1.2 D (k-g) (hub w))
  else names (near z.1) (fun _=>terminals Y (possible (k-g) z.2.1.2 D (g-f)))

omit [Fintype V] in
/-- Neighboring old endpoints at the same block land in the candidate list
for the actual chosen terminal. The two estimates use the true propagated
depths and the saturated-hub depth, all in the common remixed coordinates. -/
theorem neighbor_mem (fit : ∀v,b v≤k-f) (smooth : ∀v w,w∈near v→b v≤b w+D)
    (full : ∀v,hub v=true→b v=k-f) (fg : f≤g) (gk : g≤k)
    {v w : V} (vw : w∈near v) (wv : v∈near w) (single : ¬(hub v=true ∧ hub w=true))
    (s t : Bool) (i : Block k) :
    N t (w,i) ∈ window (k:=k) (g:=g) (f:=f) (D:=D) near hub (N s (v,i)) := by
  let x := rearrange L i
  have vd := leaf_le (D:=D) near mass room b fit v x
  have wd := leaf_le (D:=D) near mass room b fit w x
  have up := leaf_near (f:=f) near mass room b smooth vw x
  have down := leaf_near (f:=f) near mass room b smooth wv x
  have vk : d v x≤k := by omega
  have wk : d w x≤k := by omega
  have size {e : ℕ} (he : k-f≤e+D) : width k e≤2^D*2^f := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  cases hv : hub v <;> cases hw : hub w
  · simpa only [name,window,hv,hw,Bool.false_eq_true,ite_false,Option.isSome_some,Bool.true_eq,ite_true,x] using
      (names_mem (f:=fun z=>fromNonhub Y (d v x) (group (d v x) x) D (k-g) (hub z))
        (near:=near v) vw (by simpa only [hw] using nonhub_nonhub_mem (h:=k-g) vk wk up down x (row t (w,i))))
  · have WH := hub_leaf (D:=D) near mass room b hub fit full hw x
    have bound := size (e:=d v x) (by omega)
    simpa only [name,window,hv,hw,Bool.false_eq_true,ite_false,Option.isSome_some,Bool.true_eq,ite_true,x] using
      (names_mem (f:=fun z=>fromNonhub Y (d v x) (group (d v x) x) D (k-g) (hub z))
        (near:=near v) vw (by simpa only [hw] using nonhub_hub_mem (Y:=Y) fg vk bound x))
  · have VH := hub_leaf (D:=D) near mass room b hub fit full hv x
    have bound := size (e:=d w x) (by omega)
    have lower : 2^f≤width k (d w x) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa only [name,window,hv,hw,Bool.false_eq_true,ite_false,Option.isSome_none,Bool.true_eq,ite_true,x] using
      (names_mem (near:=near v) (f:=fun _=>terminals Y (possible (k-g) (group (k-g) x) D (g-f))) vw
        (terminal_mem (hub_meeting fg gk wk lower bound x) (row t (w,i))))
  · exact (single ⟨hv,hw⟩).elim

end
end Hierarchy.DescentFineTerminals

end OAI
