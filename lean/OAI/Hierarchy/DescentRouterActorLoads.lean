import OAI.Hierarchy.DescentResetMixedCharge
import OAI.Hierarchy.DescentSubstitutionDegree

namespace OAI
/-! # Site load of each real router actor, including its joined direct and public cables -/

namespace Hierarchy.DescentMixedRouter
open DescentRouterSlots DescentNamedContact DescentContactTree DescentBaseProfile DescentRotor DescentNetworkSubstitution
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits D : ℕ} (G : NonlinearExpanders.Graph n h) (hw : 0<bits)
variable (u : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i))
local notation "wt" => fun _ : I=>u
local notation "B" => DescentRouterBank.network D contact input site owner wt
variable (s : Bool) (w : W)
def terminalWeight := Fintype.card (Item contact owner s w)*u
local notation "limit" => terminalWeight u contact owner s w

omit [Fintype C] [Fintype W] in
private theorem subset_width {J : Type} [Fintype J] (key : I→J) (c : J)
    (sub : ∀i,key i=c→ owner s (contact i)=w) : width key wt c≤limit := by
  let embed : Fibre key c ↪ Item contact owner s w := ⟨fun i=>⟨i.val,sub i.val i.property⟩,
    fun _ _ eq=>Subtype.ext (congrArg (fun t : Item contact owner s w => t.val) eq)⟩
  simpa [DescentNamedContact.width,terminalWeight] using Nat.mul_le_mul_right u (Fintype.card_le_of_injective embed embed.injective)

include align in
theorem slot_price (t : Slot B (s,w)) : slotWidth B (s,w) t≤limit := by
  rcases t with ⟨a,eq⟩|⟨a,eq⟩|⟨⟨side,r⟩,eq⟩
  · have hs : false=s := congrArg Prod.fst eq
    subst s
    exact subset_width u contact owner false w contact a (fun i h=>by rw [h];exact congrArg Prod.snd eq)
  · have hs : true=s := congrArg Prod.fst eq
    subst s
    exact subset_width u contact owner true w contact a (fun i h=>by rw [h];exact congrArg Prod.snd eq)
  · have hs : side=s := congrArg Prod.fst eq
    subst side
    apply subset_width u contact owner s w (input s) r
    intro i hi
    rw [←align s i,hi]
    exact congrArg Prod.snd eq

omit [Fintype R] in
private theorem cable_price {depth : ℕ} (book : LinkId owner s w ↪ Node depth)
    (e : (DescentFixedExceptionalRouter.device D contact input site owner wt s w book).Edge) :
    (DescentFixedExceptionalRouter.device D contact input site owner wt s w book).width e≤limit := by
  let dst := DescentFixedNamedContact.code book (link contact owner s w)
  let pocket := Cell dst (e.1.val+1) e.2
  change (∑_i : pocket,u)≤_
  have small := Fintype.card_le_of_injective (fun a : pocket=>a.val) Subtype.val_injective
  simpa [terminalWeight] using Nat.mul_le_mul_right u small

local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align
local notation "device₀" => device G hw u contact input site owner align (D:=D)

/-- The paid quantity here is the number of genuine old items at the site,
not the number of leaves in its complete fallback address book. -/
theorem exceptional_actor (c : Ch s w) (ex : c.isExceptional=true) (v : (device₀ c).Site) :
    portLoad (device₀ c) v≤3*limit := by
  cases c with
  | exceptional data =>
    apply (portLoad_le_of_widths _ v limit (slot_price u contact input site owner align s w)
      (cable_price u contact input site owner s w data.book.codes)).trans
    exact Nat.mul_le_mul_right _ (DescentFixedExceptionalRouter.degree D contact input site owner wt s w
      data.book.codes data.single v)
  | good _ _ _ _ => contradiction

/-- A paid base can use the whole paid rotor volume as a bound independently
of the grouping scale and of the roster of exceptional contacts. -/
theorem ordinary_actor (c : Ch s w) (paid : c.isExceptional=false) (v : (device₀ c).Site) :
    (portLoad (device₀ c) v:ℝ)≤3*((limit:ℝ)+rotorRate h C₀*c.goodBudget) := by
  let total := ∑e,(device₀ c).width e
  have edge (e : (device₀ c).Edge) : (device₀ c).width e≤limit+total :=
    (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ e)).trans (Nat.le_add_left ..)
  have pins (p : Slot B (s,w)) : slotWidth B (s,w) p≤limit+total :=
    (slot_price u contact input site owner align s w p).trans (Nat.le_add_right ..)
  have node := (portLoad_le_of_widths (device₀ c) v _ pins edge).trans
    (Nat.mul_le_mul_right _ (device_degree G hw u contact input site owner align c v))
  have budget := device_cost G hw u contact input site owner align (D:=D) c
  rw [charge_site] at budget
  simp only [c.hops_eq_zero paid,zero_mul,Nat.cast_zero,add_zero] at budget
  have r : (portLoad (device₀ c) v:ℝ)≤3*((limit:ℝ)+(total:ℝ)) := by exact_mod_cast node
  linarith

section
set_option Elab.async false
set_option maxHeartbeats 1200000

private theorem projected_portLoad {d e : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network d P bits) (M : (q : N.Site) → Network e (Slot N q) (slotWidth N q))
    (x : (DescentNetworkSubstitution.network N M).Site)
    (selected : Fintype (Slot N x.1)) :
    portLoad (DescentNetworkSubstitution.network N M) x =
      @portLoad e (Slot N x.1) (slotWidth N x.1) selected (M x.1) x.2 := by
  obtain ⟨q,j⟩ := x
  have same := DescentNetworkSubstitution.portLoad_substitute N M q j
  exact same.trans (congrArg
    (fun inst : Fintype (Slot N q) => @portLoad e (Slot N q) (slotWidth N q) inst (M q) j)
    (Subsingleton.elim _ selected))

theorem bank_portLoad
    (select : ∀ (side : Bool) (host : W),
      Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align side host)
    (v : (network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D).Site) :
    portLoad (network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D) v =
      portLoad (device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D)
        (select v.1.1 v.1.2)) v.2 :=
  projected_portLoad
    (DescentRouterBank.network D contact input site owner (fun _ : I => u))
    (fun q => device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D)
      (select q.1 q.2)) v _

end

end
end Hierarchy.DescentMixedRouter

end OAI
