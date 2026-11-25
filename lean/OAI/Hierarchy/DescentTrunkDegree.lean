import OAI.Hierarchy.DescentResetTrunks
import Mathlib.Data.Finset.Option

namespace OAI
/-! # The simple neighbor degree of the grouped old terminal and the selected routing bank -/

namespace Hierarchy.DescentResetTrunks
open Computability.BorderVNP.Crossing DescentRouterBank DescentResetAttachments
open scoped BigOperators Classical
noncomputable section
variable {P Q H : Type} [Fintype Q] [Fintype H] {d n : ℕ} {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width))
local notation "M" => network N home group R
variable (role : N.Edge→Bool)

/-- Partial address lookup is used only to list actual simple neighbors.
An unoccupied channel contributes no site. -/
def receiver (s : Bool) (q : Q) : Option H :=
  if live : ∃e,group s e=q then some (home (ends N s live.choose)) else none

def departure (s : Bool) (z : H) (c : Bool) : Option Q :=
  if live : ∃e,home (ends N s e)=z ∧ role e=c then some (group s live.choose) else none

variable (receive : ∀s e j,group s e=group s j→home (ends N s e)=home (ends N s j))
variable (send : ∀s e j,home (ends N s e)=home (ends N s j)→ role e=role j → group s e=group s j)

include receive in
omit [Fintype Q] [Fintype H] in
theorem receiver_at (s : Bool) (e : N.Edge) : receiver N home group s (group s e)=some (home (ends N s e)) := by
  have live : ∃j,group s j=group s e := ⟨e,rfl⟩
  rw [receiver,dite_eq_left live]
  exact congrArg some (receive s _ e live.choose_spec)

include send in
omit [Fintype Q] [Fintype H] in
theorem departure_at (s : Bool) (e : N.Edge) :
    departure N home group role s (home (ends N s e)) (role e)=some (group s e) := by
  have live : ∃j,home (ends N s j)=home (ends N s e) ∧ role j=role e := ⟨e,rfl,rfl⟩
  rw [departure,dite_eq_left live]
  exact congrArg some (send s _ e live.choose_spec.1 live.choose_spec.2)

abbrev HardwarePin := (Bool×Q) ⊕ (R.Edge×Bool)
def atPin : HardwarePin N group R→R.Site :=
  Sum.elim R.attach (fun eb=>if eb.2 then R.dst eb.1 else R.src eb.1)
def peer : HardwarePin N group R → Option (M).Site
  | .inl (s,q) => (receiver N home group s q).map (fun z=>.inl (s,z))
  | .inr (e,b) => some (.inr (if b then R.src e else R.dst e))

def near : (M).Site→Finset (M).Site
  | .inl (s,z) => insert (.inl (!s,z))
      ((Finset.univ.image (fun c=>(departure N home group role s z c).map
        (fun (q : Q)=>(.inr (R.attach (s,q)) : (M).Site)))).eraseNone)
  | .inr v => ((Finset.univ.filter (fun p=>atPin N group R p=v)).image (peer N home group R)).eraseNone

include receive send in
theorem adjacent (e : (M).Edge) :
    (M).dst e∈near N home group R role ((M).src e) ∧ (M).src e∈near N home group R role ((M).dst e) := by
  rcases e with ⟨s,e⟩|z|e
  · constructor
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_eraseNone.mpr
      exact Finset.mem_image.mpr ⟨role e,Finset.mem_univ _,by simp [departure_at N home group role send]⟩
    · apply Finset.mem_eraseNone.mpr
      exact Finset.mem_image.mpr ⟨.inl (s,group s e),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,
        by simp [peer,receiver_at N home group receive]⟩
  · exact ⟨Finset.mem_insert_self ..,Finset.mem_insert_self ..⟩
  · constructor
    · exact Finset.mem_eraseNone.mpr (Finset.mem_image.mpr ⟨.inr (e,false),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩)
    · exact Finset.mem_eraseNone.mpr (Finset.mem_image.mpr ⟨.inr (e,true),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩)

theorem degree (bound : ∀v,R.bitDegree v≤3) (v : (M).Site) :
    (near N home group R role v).card≤3 := by
  rcases v with ⟨s,z⟩|v
  · apply (Finset.card_insert_le _ _).trans
    have b := (Finset.card_eraseNone_le _).trans (Finset.card_image_le (s:=Finset.univ (α:=Bool)) (f:=fun c=>
      (departure N home group role s z c).map (fun q=>(.inr (R.attach (s,q)) : (M).Site))))
    simpa using Nat.succ_le_succ b
  · exact (Finset.card_eraseNone_le _).trans (Finset.card_image_le.trans (bound v))

end
end Hierarchy.DescentResetTrunks

end OAI
