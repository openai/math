import OAI.Hierarchy.DescentNumberedFallbackNode

namespace OAI
/-! # The first operand of an installed exceptional gate at its root -/
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentContactTree DescentRouterSlots DescentOrderedWords DescentBatchedBank DescentLaneGates
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
variable {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
  (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
  (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
local notation "selection" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align selection D
local notation "programAt" => sizedProgram G hw u m p hp fit P.contact P.input P.site P.owner P.align key D selection
variable (s : Bool) (t : H)
local notation "book" => P.fallbackBook s t
local notation "code" => DescentFixedNamedContact.code (book).codes (link P.contact P.owner s (.inr t))

theorem installedTreeArity (q : Physical.Site (book).height) (e : Cell code q.1.val q.2) (b : Fin m) :
    ((programAt (⟨(s,.inr t),q⟩ : (bank).Site)).op (installedTreeGate P G hw pay hardware key D m p hp fit s t q e b)).arity=2 :=by
  subst u
  rfl

variable (e : Item P.contact P.owner s (.inr t)) (b : Fin m)
local notation "q₀" => (⟨0,prefixAt code 0 e⟩ : Physical.Site (book).height)
local notation "rootSite" => (⟨(s,.inr t),q₀⟩ : (bank).Site)
local notation "u₀" => installedTreeGate P G hw pay hardware key D m p hp fit s t q₀ ⟨e,rfl⟩ b
local notation "order₀" => DescentOrderedReset.fibreKey key (P.input s) (P.input s e.val)
local notation "rank₀" => (before order₀ ⟨e.val,rfl⟩).card

include key m hp fit b in
def installedRootLane : Lane p (boundaryWidth bank rootSite) :=
  ((programAt rootSite).op u₀).arg
    ⟨0,by rw [installedTreeArity];decide⟩

local notation "leftLane" => installedRootLane P G hw pay hardware key D m p hp fit s t e b

/-- The installed input socket retains its side and original input label. Its
first bit counts earlier grains in this particular input fibre. -/
theorem installedRootLane_fields :
    Sum.map Subtype.val Subtype.val (leftLane).port=.inr (s,P.input s e.val) ∧
      (leftLane).start=DescentTreeLaneProgram.batchStart order₀ ⟨e.val,rfl⟩ m p b ∧ (leftLane).stride=1 :=by
  subst u
  refine ⟨rfl,?_,rfl⟩
  have first := DescentTreeLaneProgram.previous_fields D P.contact P.input P.site P.owner
    P.align m p hp s (.inr t) (book).codes key (2^n) e b (0 : Fin ((book).height+1))
  simp only [Fin.cases_zero] at first
  have start := congrArg (fun a => a.2.1) first
  refine start.trans ?_
  unfold DescentTreeLaneProgram.batchStart
  apply congrArg (fun items : Finset { i : I // P.input s i = P.input s e.val } =>
    items.card*(m*p) + b.val*p)
  ext i
  simp only [before, Finset.mem_filter, Finset.mem_univ, true_and]

theorem installedRootLane_socket :
    ∃sock : Attached bank rootSite, (leftLane).port=.inr sock ∧ sock.val=(s,P.input s e.val) ∧
      (leftLane).bundleStart=rank₀*m+b.val ∧ (leftLane).stride=1 :=by
  obtain ⟨addr,start,step⟩:=installedRootLane_fields P G hw pay hardware key D m p hp fit s t e b
  have base : (leftLane).bundleStart=rank₀*m+b.val :=by
    change (leftLane).start/p=_
    rw [start]
    change (rank₀*(m*p)+b.val*p)/p=_
    rw [←Nat.mul_assoc,←Nat.add_mul,Nat.mul_div_cancel _ hp]
  cases found : (leftLane).port with
  | inl cable=>rw [found] at addr;cases addr
  | inr sock=>
    rw [found] at addr
    exact ⟨sock,rfl,Sum.inr.inj addr,base,step⟩

end
end Hierarchy.DescentChosenRouter

namespace Hierarchy.DescentSixParty.ResetInput
open Computability.BorderVNP.Crossing DescentKernelHistory DescentChosenRouter DescentRouterSlots
open DescentContactTree DescentOrderedWords DescentLaneGates
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
variable {F P : Type} [Field F] {d N : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin N)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p) (s : Bool) (t : Z.Fallback)
local notation "R" => Z.placement
local notation "book" => (R).fallbackBook s t
local notation "code" => DescentFixedNamedContact.code (book).codes (link (R).contact (R).owner s (.inr t))
variable (e : Item Z.placement.contact Z.placement.owner s (.inr t)) (b : Fin m)
local notation "q₀" => (⟨0,prefixAt code 0 e⟩ : Physical.Site (book).height)
local notation "venue" => (⟨(s,.inr t),q₀⟩ : Z.bank.Site)
local notation "order₀" => DescentOrderedReset.fibreKey key ((R).input s) ((R).input s e.val)

include key m hp fit b in
abbrev rootLane : Lane p (boundaryWidth Z.bank venue) :=
  installedRootLane R Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s t e b
local notation "leftLane" => Z.rootLane key m p hp fit s t e b

theorem rootLane_fields :
    Sum.map Subtype.val Subtype.val (leftLane).port=.inr (s,(R).input s e.val) ∧
      (leftLane).start=DescentTreeLaneProgram.batchStart order₀ ⟨e.val,rfl⟩ m p b ∧ (leftLane).stride=1 :=
  installedRootLane_fields R Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s t e b

theorem rootLane_socket :
    ∃sock : Attached Z.bank venue, (leftLane).port=.inr sock ∧ sock.val=(s,(R).input s e.val) ∧
      (leftLane).bundleStart=(before order₀ ⟨e.val,rfl⟩).card*m+b.val ∧ (leftLane).stride=1 :=
  installedRootLane_socket R Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s t e b

include key m p hp fit b in
theorem rootLane_attach : Z.bank.attach (s,(R).input s e.val)=venue :=by
  obtain ⟨sock,_,addr,_,_⟩:=Z.rootLane_socket key m p hp fit s t e b
  rw [←addr]
  exact sock.property

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
