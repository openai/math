import OAI.Hierarchy.DescentSelectedHubs
import OAI.Hierarchy.DescentMergedHub

namespace OAI
/-! # An original hub's actual selected star has its original full dyadic interval -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentHostDirectory DescentColonies
open scoped Classical
noncomputable section
variable {V C : Type} [DecidableEq V] [Fintype C] [DecidableEq C] {d : ℕ} {P : Type} {bits : P→ℕ}
variable (N : Network d P bits) (core : Finset N.Edge) (home : N.Site→C) (color : N.Site→Bool) (B : ℕ)
variable (col : C↪V×(ℕ×ℕ)) (same : ∀e∈core,color (N.src e)=color (N.dst e)) (l : Bool)
local notation "pick" => colorPick N core home color B
local notation "pack" => coloredPack N core home color B
local notation "slot" => chosenSlot N core home color B
local notation "center" => chosenCenter N core home color B l
local notation "key" => nativeKey N core home color B col same l

omit [DecidableEq V] in
theorem untouched_hub_key (flag : V→Bool) (unpaid : ∀i,flag (col (home (N.src (pick (i,1))))).1=false)
    {u : N.Site} (isHub : flag (col (home u)).1=true) :
    let addr := key (newSite N pick l pack (.inl u))
    (addr.1,addr.2.1)=col (home u) := by
  have no_redirect : resolve slot center (pack u)=pack u := by
    cases h : pack u with
    | inl c=>rfl
    | inr t=>
      have free : ¬∃i,slot i=t := by
        rintro ⟨i,connected⟩
        have samePack : pack (N.src (pick (i,1)))=pack u := by
          exact (colorPick_thin_src N core home color B i).trans
            ((congrArg Sum.inr connected).trans h.symm)
        have own := (pack_home N B home color core _).symm.trans
          ((congrArg packColony samePack).trans (pack_home N B home color core u))
        have excluded := unpaid i
        rw [own,isHub] at excluded
        contradiction
      simp only [resolve,dite_eq_right free]
  change ((packAddress N core home color B col (resolve slot center (pack u))).1,
    (packAddress N core home color B col (resolve slot center (pack u))).2.1)=col (home u)
  rw [no_redirect]
  exact packed_home N core home color B col u

omit [DecidableEq V] in
theorem native_hub_interval (flag : V→Bool) (unpaid : ∀i,flag (col (home (N.src (pick (i,1))))).1=false)
    {k a markCap : ℕ} (near : V→Finset V) (D : ℕ) (load : V→Block k→ℕ) (room : ∀v x,load v x≤markCap)
    (positive : 0<markCap) (full : ∀v,flag v=true→∀x,load v x=markCap)
    (pos : N.Site→V) (ix : N.Site→Block k)
    (realized : ∀u,col (home u)=colonyCode N markCap near D a load room pos ix u)
    (u : N.Site) (isHub : flag (pos u)=true) :
    let address := key (newSite N pick l pack (.inl u))
    (address.1,address.2.1)=(pos u,(k-a,group (k-a) (ix u))) := by
  have h : flag (col (home u)).1=true := by rw [realized];exact isHub
  refine (untouched_hub_key N core home color B col same l flag unpaid h).trans ((realized u).trans ?_)
  exact congrArg (fun j => (pos u, (j, group j (ix u))))
    (saturated_depth (D := D) (a := a) load (fun v w => w ∈ near v)
      room (pos u) (full _ isHub) positive (ix u))

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
