import OAI.Hierarchy.DescentActorBudgetReadout

namespace OAI
/-! # The measured integer site cap and exactly saturated hubs in the returned reset network -/

namespace Hierarchy.DescentResetTrunks
open DescentSixParty DescentResetAttachments DescentRouterBank DescentNetworkSubstitution Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P H Q Word : Type} [Field F] [Fintype H] [Fintype Q] {n d : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (group : Bool→A.graph.Edge→Q) (hub : H→Bool)
variable {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth group w)) (tables : R.Tables F)
local notation "M" => install A home group hub same R tables
local notation "names" => installedNames A home group hub same R tables

private def namedHub (hub : H → Bool) {S : Type} : (Bool × H) ⊕ S → Bool
  | .inl (false,t) => hub t
  | _ => false

def installedHub : (M).graph.Site→Bool := fun v => namedHub hub (names v)

omit [Fintype Q] in
private theorem installedHub_read (x : (Bool × H) ⊕ R.Site) :
    installedHub A home group hub same R tables ((names).symm x) = namedHub hub x :=
  congrArg (namedHub hub) ((names).apply_symm_apply x)

omit [Fintype Q] in
private theorem installedHub_at_width
    (bank : Network d (Bool×Q) (publicWidth group A.graph.width)) (tab : bank.Tables F) :
    installedHub A home group hub rfl bank tab = hubAt A home group bank hub := by
  funext v
  rcases v with ⟨(_|_),t⟩ | r <;> rfl

theorem read_actors (rec : (M).graph.Site→List Word) (wire β hist : ℕ) (x : (Bool×H)⊕R.Site) :
    (M).siteUnits (installedHub A home group hub same R tables) rec wire β hist ((names).symm x)=
      (match x with
        | .inl (false,t) => (bin (home ∘ A.graph.src) A.graph.width t+bin (home ∘ A.graph.dst) A.graph.width t)*
            wire*(if hub t then β else 1)
        | .inl (true,t) => 2*wire*bin (home ∘ A.graph.dst) A.graph.width t
        | .inr r => wire*portLoad R r)+hist*(rec ((names).symm x)).length := by
  subst w
  rw [installedHub_at_width]
  rcases x with ⟨s,t⟩|r
  · cases s
    · exact terminal_units A home group R tables hub rec wire β hist t
    · exact relay_units A home group R tables hub rec wire β hist t
  · exact bank_units A home group R tables hub rec wire β hist r

omit [Fintype Q] in
theorem installed_ends (e : (M).graph.Edge) :
    (e∈(M).core → installedHub A home group hub same R tables ((M).graph.src e)=false ∧
      installedHub A home group hub same R tables ((M).graph.dst e)=false) ∧
    (e∉(M).core → installedHub A home group hub same R tables ((M).graph.src e)≠
      installedHub A home group hub same R tables ((M).graph.dst e)) := by
  subst w
  rw [installedHub_at_width]
  exact endpoints A home group R tables hub e
end
end Hierarchy.DescentResetTrunks

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentMixedRouter
open scoped Classical BigOperators
noncomputable section
variable {F P H : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht)
variable (T : Terminals Z) (old : A.graph.Site→List H) (wire hist f g B : ℕ)
local notation "R" => Z.placement
local notation "new" => Z.reenter T
local notation "cap" => (2^g*B : ℕ)
local notation "base" => (2^f*B : ℕ)
local notation "whole" => bin T.home (A.siteUnits Z.hub old wire 256 hist)
local notation "eqw" => funext (fun e=>Eq.symm (Z.allWidths e))
def reentryTag := installedHub A T.home (R).input T.hub eqw Z.bank Z.tables
def measuredRecords := reentryRecords Z T old (fun _=>([] : List Empty))
local notation "cost" => MarkedWorld.siteUnits (Z.reenter T) (reentryTag Z T) (measuredRecords Z T old) wire 256 hist
variable (bill : ActorBudget Z T old wire hist f g B)
variable (rotor : 3*(2+rotorRate h C)*((2^f*B:ℕ):ℝ)+hist≤((2^g*B:ℕ):ℝ))
variable (rows : 9*((2^f*B:ℕ):ℝ)+hist≤((2^g*B:ℕ):ℝ))
variable (hubBound : 3*((2^g*B:ℕ):ℝ)/256+hist≤((2^g*B:ℕ):ℝ))

include bill rotor rows hubBound in
theorem physical_site_units (v : (new).graph.Site) :
    cost v≤cap ∧ (reentryTag Z T v=true→cost v=cap) := by
  obtain ⟨x,rfl⟩ := (resetNames Z T).symm.surjective v
  let read := read_actors A T.home (R).input T.hub eqw Z.bank Z.tables (measuredRecords Z T old) wire 256 hist x
  rcases x with ⟨s,t⟩|r
  · cases s
    · have records := reentry_primary_length Z T (Pin:=Empty) old t
      have amount := whole_fiber A T.home T.hub wire 256 hist old t
      rw [show T.hub ∘ T.home=Z.hub from funext T.tag] at amount
      have eq : cost ((resetNames Z T).symm (.inl (false,t)))=whole t := by
        have primary : cost ((resetNames Z T).symm (.inl (false,t))) =
            (bin (T.home ∘ A.graph.src) A.graph.width t + bin (T.home ∘ A.graph.dst) A.graph.width t) *
              wire * (if T.hub t then 256 else 1) +
              hist*(measuredRecords Z T old ((resetNames Z T).symm (.inl (false,t)))).length := read
        rw [primary,amount,show (measuredRecords Z T old ((resetNames Z T).symm (.inl (false,t)))).length=
            bin T.home (fun u=>(old u).length) t from records.trans (width_bin T.home (fun u=>(old u).length) t)]
      have named : reentryTag Z T ((resetNames Z T).symm (.inl (false,t)))=T.hub t :=
        installedHub_read A T.home (R).input T.hub eqw Z.bank Z.tables (.inl (false,t))
      rw [eq,named]
      cases atHub : T.hub t
      · have small := bill.ordinary t atHub
        have y : (1:ℝ)≤(2^Z.n:ℕ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.two_pow_pos _)
        have bounded := small.trans (div_le_self (by positivity) y)
        constructor
        · exact_mod_cast (show (whole t:ℝ)≤(cap:ℝ) by linarith only [bounded,rows,show (0:ℝ)≤hist from by positivity,show (0:ℝ)≤base from by positivity])
        · simp
      · have e := bill.hub t atHub
        exact ⟨e.le,fun _=>e⟩
    · have no : reentryTag Z T ((resetNames Z T).symm (.inl (true,t)))=false :=
        installedHub_read A T.home (R).input T.hub eqw Z.bank Z.tables (.inl (true,t))
      rw [no]
      refine ⟨?_,by simp⟩
      have read' : cost ((resetNames Z T).symm (.inl (true,t))) =
          2*wire*bin (T.home ∘ A.graph.dst) A.graph.width t +
            hist*(measuredRecords Z T old ((resetNames Z T).symm (.inl (true,t)))).length := read
      simp only [show (measuredRecords Z T old ((resetNames Z T).symm (.inl (true,t)))).length=0 from
        reentry_relay_length Z T (Pin:=Empty) old t,Nat.mul_zero,Nat.add_zero] at read'
      rw [show cost ((resetNames Z T).symm (.inl (true,t)))=_ from read']
      have marg := end_cap Z T old wire hist true t
      change bin (T.home ∘ A.graph.dst) A.graph.width t*wire*(if T.hub t then 256 else 1)≤whole t at marg
      cases atHub : T.hub t
      · simp only [atHub,Bool.false_eq_true,ite_false,mul_one] at marg
        have y : (1:ℝ)≤(2^Z.n:ℕ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.two_pow_pos _)
        have small := (bill.ordinary t atHub).trans (div_le_self (by positivity) y)
        have bound : (bin (T.home ∘ A.graph.dst) A.graph.width t:ℝ)*wire≤whole t := by exact_mod_cast marg
        exact_mod_cast (show 2*(wire:ℝ)*(bin (T.home ∘ A.graph.dst) A.graph.width t:ℝ)≤(cap:ℝ) by
          nlinarith only [rows,small,bound,show (0:ℝ)≤base from by positivity,show (0:ℝ)≤hist from by positivity])
      · simp only [atHub,ite_true,bill.hub t atHub] at marg
        nlinarith only [marg,Nat.zero_le (bin (T.home ∘ A.graph.dst) A.graph.width t*wire)]
  · have no : reentryTag Z T ((resetNames Z T).symm (.inr r))=false :=
      installedHub_read A T.home (R).input T.hub eqw Z.bank Z.tables (.inr r)
    rw [no]
    refine ⟨?_,by simp⟩
    have read' : cost ((resetNames Z T).symm (.inr r)) =
        wire * DescentNetworkSubstitution.portLoad Z.bank r +
          hist*(measuredRecords Z T old ((resetNames Z T).symm (.inr r))).length := read
    simp only [show (measuredRecords Z T old ((resetNames Z T).symm (.inr r))).length=1 from
      reentry_bank_length Z T (Pin:=Empty) old r,Nat.mul_one] at read'
    rw [show cost ((resetNames Z T).symm (.inr r))=_ from read']
    apply cumulative_port_cap Z T old wire hist f g B bill r
    · exact_mod_cast rotor
    · exact_mod_cast rows
    · exact_mod_cast hubBound

theorem reentry_tags (e : (new).graph.Edge) :
    (e∈(new).core→ reentryTag Z T ((new).graph.src e)=false ∧ reentryTag Z T ((new).graph.dst e)=false) ∧
    (e∉(new).core→ reentryTag Z T ((new).graph.src e)≠reentryTag Z T ((new).graph.dst e)) :=
  installed_ends A T.home (R).input T.hub eqw Z.bank Z.tables e

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
