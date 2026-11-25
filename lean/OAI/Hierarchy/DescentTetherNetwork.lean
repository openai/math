import OAI.Hierarchy.DescentTetherPorts

namespace OAI
/-! # The actual first physical cable after each merged hub -/

namespace Hierarchy.DescentTetherPorts
open Computability.BorderVNP.Crossing DescentRouterSlots DescentMixedRouter
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits D : ℕ} (G : NonlinearExpanders.Graph n h) (hw : 0<bits)
variable (u : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i))
local notation "wt" => fun _ : I=>u
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "Device" => device G hw u contact input site owner align (D:=D)
local notation "root" => isRoot G hw u contact input site owner align (D:=D)
local notation "raw" => mass u contact owner
local notation "bridge" => direct G hw u contact input site owner align
local notation "tree" => hasTree G hw u contact input site owner align
variable (select : ∀s w, Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align s w)
variable (hub : Bool→W→Prop)
local notation "Q" => network G hw u contact input site owner align select D

def rootSite (v : (Q).Site) : Prop := hub v.1.1 v.1.2 ∧ root (select v.1.1 v.1.2) v.2

def tether (e : (Q).Edge) : Prop :=
  rootSite G hw u contact input site owner align select hub ((Q).src e) ∨
    rootSite G hw u contact input site owner align select hub ((Q).dst e)

omit [Fintype R] in
private theorem on_bridge (c : C) :
    tether G hw u contact input site owner align select hub (D:=D) (.inl c) ↔
      (hub false (owner false c) ∧ bridge (select false (owner false c))) ∨
      (hub true (owner true c) ∧ bridge (select true (owner true c))) := by
  apply or_congr
  · exact and_congr_right' (direct_root G hw u contact input site owner align
      (select false (owner false c)) (⟨c,rfl⟩ : LinkId owner false (owner false c)))
  · exact and_congr_right' (direct_root G hw u contact input site owner align
      (select true (owner true c)) (⟨c,rfl⟩ : LinkId owner true (owner true c)))

omit [Fintype R] in
private theorem on_private (v : Bool×W) :
    (∑e : (Device (select v.1 v.2)).Edge, if tether G hw u contact input site owner align select hub
      (.inr ⟨v,e⟩) then (Device (select v.1 v.2)).width e else 0)=
    if hub v.1 v.2 ∧ tree (select v.1 v.2) ∧ ¬ bridge (select v.1 v.2) then raw v.1 v.2 else 0 := by
  by_cases tagged : hub v.1 v.2
  · simpa [tether,rootSite,tagged,network,DescentNetworkSubstitution.network] using
      private_first (D:=D) G hw u contact input site owner align (select v.1 v.2)
  · simp [tether,rootSite,network,DescentNetworkSubstitution.network,tagged]

omit [Fintype R] in
/-- The amount carried as a tether on actual edges is at most the input
bundle amount originally touching merged hubs. A contact with two marked
ends is charged at most once on a shared direct edge. -/
theorem first_segments :
    (∑e : (Q).Edge,if tether G hw u contact input site owner align select hub e then (Q).width e else 0)≤
      ∑v : Bool×W,if hub v.1 v.2 ∧ tree (select v.1 v.2) then raw v.1 v.2 else 0 := by
  let active (s : Bool) (w : W) := hub s w ∧ bridge (select s w)
  let contactFee (keep : W→Prop) (s : Bool) (c : C) :=
    if keep (owner s c) then DescentNamedContact.width contact wt c else 0
  let hubFee (keep : W→Prop) (s : Bool) (w : W) := if keep w then raw s w else 0
  have regroup (keep : W→Prop) (s : Bool) :
      (∑ c,contactFee keep s c) = ∑ w,hubFee keep s w :=
    owner_mass u contact owner keep s
  let billed (e : (Q).Edge) :=
    if tether G hw u contact input site owner align select hub e then (Q).width e else 0
  let internal (v : Bool×W) :=
    if hub v.1 v.2 ∧ tree (select v.1 v.2) ∧ ¬bridge (select v.1 v.2) then raw v.1 v.2 else 0
  have roots : (∑ c : C,billed (.inl c)) ≤ ∑ v : Bool×W,hubFee (active v.1) v.1 v.2 := by
    calc
      _ ≤ ∑ c : C, (contactFee (active true) true c + contactFee (active false) false c) := by
        apply Finset.sum_le_sum
        intro c _
        have bridgeAt := on_bridge (D:=D) G hw u contact input site owner align select hub c
        change (if tether G hw u contact input site owner align select hub (D:=D) (.inl c)
            then DescentNamedContact.width contact wt c else 0) ≤ _
        by_cases chosen : active false (owner false c) ∨ active true (owner true c)
        · rw [ite_eq_left (bridgeAt.mpr chosen)]
          rcases chosen with left|right
          · simp [contactFee,left]
          · simp [contactFee,right]
        · rw [ite_eq_right (fun attached => chosen (bridgeAt.mp attached))]
          exact Nat.zero_le _
      _ = (∑ w,hubFee (active true) true w) + ∑ w,hubFee (active false) false w := by
        rw [Finset.sum_add_distrib]
        exact congrArg₂ (·+·) (regroup (active true) true) (regroup (active false) false)
      _ = _ := by rw [Fintype.sum_prod_type,Fintype.sum_bool]
  have priv (v : Bool×W) :
      (∑ e : (Device (select v.1 v.2)).Edge,billed (.inr ⟨v,e⟩))=internal v :=
    on_private (D:=D) G hw u contact input site owner align select hub v
  have bridge_tree (s : Bool) (w : W) : bridge (select s w) → tree (select s w) := by
    cases select s w <;> simp [direct,hasTree]
  change (∑ e : C ⊕ (Σ v : Bool×W,(Device (select v.1 v.2)).Edge),billed e) ≤ _
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  refine (Nat.add_le_add roots (Finset.sum_le_sum (fun v _ => (priv v).le))).trans ?_
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  rintro ⟨s,w⟩ _
  by_cases directAt : bridge (select s w)
  · simp [hubFee,active,internal,directAt,bridge_tree s w directAt]
  · simp [hubFee,active,internal,directAt]

omit [Fintype R] in
theorem original_hub_mass (clear : ∀i,¬ (hub false (owner false (contact i)) ∧ hub true (owner true (contact i)))) :
    (∑e : (Q).Edge,if tether G hw u contact input site owner align select hub e then (Q).width e else 0)≤
      ∑i,if hub false (owner false (contact i)) ∨ hub true (owner true (contact i)) then u else 0 := by
  have each (s : Bool) : (∑w,if hub s w ∧ tree (select s w) then raw s w else 0)≤
      ∑i,if hub s (owner s (contact i)) then u else 0 := by
    rw [←(Equiv.sigmaFiberEquiv (fun i=>owner s (contact i))).sum_comp
      (fun i=>if hub s (owner s (contact i)) then u else 0),Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro w _
    change (if hub s w ∧ tree (select s w) then raw s w else 0) ≤
      ∑ t : Item contact owner s w,if hub s (owner s (contact t.val)) then u else 0
    have same : (∑ t : Item contact owner s w,if hub s (owner s (contact t.val)) then u else 0) =
        ∑ _t : Item contact owner s w,if hub s w then u else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [t.property]
    rw [same]
    by_cases p : hub s w <;> by_cases q : tree (select s w) <;> simp [mass,p,q]
  apply (first_segments G hw u contact input site owner align select hub).trans
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  apply (Nat.add_le_add (each true) (each false)).trans_eq
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := clear i
  by_cases a : hub false (owner false (contact i)) <;>
    by_cases b : hub true (owner true (contact i)) <;> simp_all

end
end Hierarchy.DescentTetherPorts

end OAI
