import OAI.Hierarchy.DescentActorMass
import OAI.Hierarchy.DescentSharedRows
import OAI.Hierarchy.DescentSaturatedHubLedger
import OAI.Hierarchy.DescentColonyLoads

namespace OAI
/-! # Remixed host occurrences under the actual old terminal, at hubs and ordinary rows -/

namespace Hierarchy.DescentFineTerminals
open DescentSixParty DescentSixParty.StarKeys DescentResetTrunks DescentContacts DescentColonies DescentGL DescentBaseProfile
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {k Y f g D B : ℕ}
variable (near : V→Finset V) (wt : V→Block k→ℕ) (room : ∀v i,wt v i≤B) (b : V→ℕ)
variable (hub : V→Bool) (L : Layout k) (row : Bool→V×Block k→Fin Y)
variable (loc : I→V×Block k) (units : I→ℕ)
local notation "N" => name (D:=D) (f:=f) (g:=g) near wt room b hub L row
local notation "occ" => occupants (D:=D) (f:=f) near wt room b
local notation "total" => DescentResetTrunks.bin loc units

private theorem remixed_site_bin (s : Bool) (v : V) (e : Endpoint Y) :
    DescentResetTrunks.bin (N s ∘ loc) units (v,e) =
      ∑x : Block k, if N s (v,(rearrange L).symm x)=(v,e)
        then total (v,(rearrange L).symm x) else 0 := by
  classical
  let column (x : Block k) := if N s (v,x)=(v,e) then total (v,x) else 0
  calc
    _ = ∑x : Block k, column x := by
      rw [←DescentResetTrunks.bin_comp loc (N s) units]
      unfold DescentResetTrunks.bin
      rw [Fintype.sum_prod_type]
      refine (Finset.sum_eq_single_of_mem v (Finset.mem_univ _) ?_).trans ?_
      · intro w _ different
        apply Finset.sum_eq_zero
        intro x _
        apply ite_eq_right
        intro same
        have first := congrArg Prod.fst same
        apply different
        cases flag : hub w <;> simpa [name,flag] using first
      · apply Finset.sum_congr rfl
        intro x _
        by_cases same : N s (v,x)=(v,e) <;> simp [column,same,DescentResetTrunks.bin]
    _ = _ := ((rearrange L).symm.sum_comp column).symm

/-- The conditional pushforward over physical sites is exactly the load read
by the row allocator after the selected invertible remix. -/
theorem terminal_read (s : Bool) (v : V) (key : ℕ×ℕ) (j : Fin Y) (ordinary : hub v=false) :
    (bin (N s ∘ loc) units (v,key,some j):ℝ)=
      inputLoad (occ v key) (fun x=>(total (v,(rearrange L).symm x):ℝ))
        (fun x=>row s (v,(rearrange L).symm x)) j := by
  classical
  rw [remixed_site_bin near wt room b hub L row loc units s v (key,some j),Nat.cast_sum]
  unfold inputLoad occupants
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases same : leafKey (D:=D) (f:=f) near wt room b v x=key <;>
    by_cases here : row s (v,(rearrange L).symm x)=j <;>
    simp only [leafKey] at same <;> simp [name,ordinary,leafKey,same,here]

/-- A saturated hub terminal covers one entire coarse group, with no extra
dependence on the input rows or on the suffix bits removed by the reset. -/
theorem hub_read (s : Bool) (v : V) (isHub : hub v=true) (x : Block k) (hg : g≤k)
    (saturated : ∀x,total (v,x)=B) :
    bin (N s ∘ loc) units (v,(k-g,group (k-g) x),none)=2^g*B := by
  classical
  rw [remixed_site_bin near wt room b hub L row loc units s v ((k-g,group (k-g) x),none)]
  calc
    _ = ∑ _z∈interval (k-g) x, B := by
      rw [interval,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases same : group (k-g) z=group (k-g) x <;> simp [name,isHub,saturated,same]
    _ = _ := by
      simp [DescentHostDirectory.interval_card_eq (Nat.sub_le k g),DescentColonies.width,
        Nat.sub_sub_self hg]

variable {d : ℕ} {P : Type} {bits : P→ℕ} (A : Network d P bits) (pos : A.Site→V) (ix : A.Site→Block k)
omit [Fintype V] in
theorem block_bin (cost : A.Site→ℕ) (v : V) (x : Block k) :
    bin (fun u=>(pos u,ix u)) cost (v,x)=blockMass A pos ix cost v x := by
  simp [DescentResetTrunks.bin,blockMass,Prod.mk.injEq]

omit [Fintype V] [DecidableEq V] in
theorem terminal_bin {E : Type*} (code : E↪V×Endpoint Y) (name : I→E) (t : E) :
    bin name units t=bin (code ∘ name) units (code t) := by
  simp [DescentResetTrunks.bin,code.injective.eq_iff]

theorem input_div {Z : Type*} (a : Finset Z) (cost : Z→ℝ) (assign : Z→Fin Y) (j : Fin Y) (wire : ℕ) :
    inputLoad a (fun z=>cost z/wire) assign j=inputLoad a cost assign j/wire := by
  simp [inputLoad,Finset.sum_div,ite_div]

end
end Hierarchy.DescentFineTerminals

end OAI
