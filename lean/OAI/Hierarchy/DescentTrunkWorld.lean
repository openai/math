import OAI.Hierarchy.DescentTrunkDegree
import OAI.Hierarchy.DescentNetworkWorld

namespace OAI
/-! # Reset re-entry retains all exterior bits while charging one additional original width -/

namespace Hierarchy.DescentResetTrunks
open DescentSixParty DescentRouterBank DescentNamedContact DescentResetAttachments Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {F H P Q : Type} [Field F] [Fintype H] [Fintype Q] {d n : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (group : Bool→A.graph.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group A.graph.width)) (S : R.Tables F) (hub : H→Bool)
local notation "M" => network A.graph home group R

def hubAt : (M).Site→Bool
  | .inl (false,z) => hub z
  | _ => false

def marked : (M).Edge→Bool
  | .inl (false,e) => !(hub (home (A.graph.src e)))
  | .inl (true,_) => true
  | .inr (.inl z) => !(hub z)
  | .inr (.inr _) => true

def world : MarkedWorld F d P bits :=
  ⟨⟨M,tables A.graph home group R A.tables S⟩,Finset.univ.filter (fun e=>marked A home group R hub e=true)⟩

local notation "W" => world A home group R S hub

omit [Fintype Q] in
theorem world_value (rhs : ∀p,R.value S p=if publicRows group A.graph.width p false=
    publicRows group A.graph.width p true then 1 else 0) (x : Ports bits) : (W).value x=A.value x :=
  (value A.graph home group R A.tables S x).trans (DescentResetAttachments.value_eq A.graph group R A.tables S rhs x)

omit [Fintype Q] in
private theorem mem_marked_core (e : (W).graph.Edge) :
    e ∈ (W).core ↔ marked A home group R hub e = true := by
  let mark := marked A home group R hub
  have select := @Finset.mem_filter (M).Edge (fun a => mark a = true)
    (fun a => instDecidableEqBool (mark a) true) Finset.univ e
  exact select.trans ⟨And.right, fun h => ⟨Finset.mem_univ _,h⟩⟩

omit [Fintype Q] in
theorem endpoints (e : (W).graph.Edge) :
    (e∈(W).core → hubAt A home group R hub ((W).graph.src e)=false ∧ hubAt A home group R hub ((W).graph.dst e)=false) ∧
    (e∉(W).core → hubAt A home group R hub ((W).graph.src e)≠hubAt A home group R hub ((W).graph.dst e)) := by
  simp only [mem_marked_core A home group R S hub]
  rcases e with ⟨s,e⟩|z|e
  · cases s <;> simp [world,hubAt,marked,network,ends]
  · simp [world,hubAt,marked,network]
  · simp [world,hubAt,marked,network]

omit [Field F] in
private theorem trunk_mass :
    (∑z,if hub z then trunkWidth A.graph home z else 0)=
      ∑e,if hub (home (A.graph.dst e)) then A.graph.width e else 0 := by
  let weight (e : A.graph.Edge) := if hub (home (A.graph.dst e)) then A.graph.width e else 0
  rw [←(Equiv.sigmaFiberEquiv (moved A.graph home)).sum_comp weight,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  have fibre (i : Fibre (moved A.graph home) z) : home (A.graph.dst i.val) = z := i.property
  cases eq : hub z <;>
    simp [weight,trunkWidth,DescentNamedContact.width,Equiv.sigmaFiberEquiv,fibre,eq]

omit [Fintype Q] in
theorem tether
    (ordinary : ∀e∈A.core,hub (home (A.graph.src e))=false ∧ hub (home (A.graph.dst e))=false)
    (outside : ∀e∉A.core,hub (home (A.graph.src e))≠hub (home (A.graph.dst e))) :
    (W).tetherWidth=A.tetherWidth := by
  have outside_mass {E : Type} [Fintype E] (s : Finset E) (w : E → ℕ) (mark : E → Bool)
      (classify : ∀e, e ∈ s ↔ mark e = true) :
      (∑e∈sᶜ,w e) = ∑e, if ¬ mark e = true then w e else 0 := by
    have choose : sᶜ = Finset.univ.filter (fun e => e ∉ s) := by ext e; simp
    rw [choose,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : e ∈ s
    · simp [h,(classify e).mp h]
    · have off := mt (classify e).mpr h
      simp [h,off]
  have project : (W).tetherWidth = ∑e : (M).Edge,
      if ¬ marked A home group R hub e = true then (M).width e else 0 :=
    @outside_mass (W).graph.Edge (W).graph.finiteEdge (W).core (W).graph.width
      (marked A home group R hub) (mem_marked_core A home group R S hub)
  rw [project]
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
  change (∑e,if ¬true=true then A.graph.width e else 0)+
    (∑e,if ¬(!(hub (home (A.graph.src e))))=true then A.graph.width e else 0)+
    ((∑z,if ¬(!(hub z))=true then trunkWidth A.graph home z else 0)+(∑e : R.Edge,if ¬true=true then R.width e else 0))=_
  have negated (x : Bool) : (¬(!x)=true) ↔ x=true := by cases x <;> decide
  simp only [not_true_eq_false,ite_false,Finset.sum_const_zero,zero_add,add_zero,negated]
  rw [trunk_mass,←Finset.sum_add_distrib]
  unfold MarkedWorld.tetherWidth
  have repr : A.coreᶜ = Finset.univ.filter (fun e => e ∉ A.core) := by ext e; simp
  rw [repr, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases c : e∈A.core
  · obtain ⟨l,r⟩ := ordinary e c
    simp [c,l,r]
  · have ne := outside e c
    cases src : hub (home (A.graph.src e)) <;> cases dst : hub (home (A.graph.dst e)) <;> simp_all

omit [Fintype Q] in
theorem live
    (ordinary : ∀e∈A.core,hub (home (A.graph.src e))=false ∧ hub (home (A.graph.dst e))=false)
    (outside : ∀e∉A.core,hub (home (A.graph.src e))≠hub (home (A.graph.dst e))) :
    (W).liveWidth=(∑e,R.width e)+3*A.liveWidth+2*A.tetherWidth := by
  have wt : (∑e,(W).graph.width e) = (∑e,R.width e) + 3*(∑e,A.graph.width e) :=
    width A.graph home group R
  have wsum := Finset.sum_add_sum_compl (W).core (W).graph.width
  have asum := Finset.sum_add_sum_compl A.core A.graph.width
  change (W).liveWidth+(W).tetherWidth=_ at wsum
  change A.liveWidth+A.tetherWidth=_ at asum
  rw [tether A home group R S hub ordinary outside] at wsum
  omega

omit [Fintype Q] in
theorem preserves_quantum (u : ℕ) (oldWidth : ∀e,u∣A.graph.width e) (deviceWidth : ∀e,u∣R.width e)
    (e : (W).graph.Edge) : u∣(W).graph.width e := by
  rcases e with ⟨_,e⟩|z|e
  · exact oldWidth e
  · exact Finset.dvd_sum fun i _=>oldWidth i.val
  · exact deviceWidth e

end
end Hierarchy.DescentResetTrunks

end OAI
