import Mathlib.Data.List.OfFn
import OAI.Hierarchy.DescentRosterOrder
import OAI.Hierarchy.DescentInstalledHops
import OAI.Hierarchy.DescentRelativeContacts

namespace OAI
/-! # The complete common leaf roster used by every physical fallback tree -/

namespace Hierarchy.DescentRelativeContacts
open DescentGL DescentColonies DescentContacts DescentContactTree DescentFineTerminals DescentChosenRouter
open DescentMixedRouter DescentRouterSlots
open scoped Classical BigOperators
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
    {k r n f g B Δ : ℕ} (P : Placement V I H A k (2^n))
local notation "Y" => (2^n : ℕ)
local notation "radius" => (32*Nat.clog 2 (2*Δ))
variable (near : V→Finset V) (mass : V→Block k→ℕ) (room : ∀v i,mass v i≤B)
variable (hub : V→Bool) (row : Bool→V×Block k→Fin (2^n)) (code : H ↪ V×Endpoint (2^n))
local notation "N" => name (D:=radius) (f:=f) (g:=g) near mass room (Placement.b P) hub (Placement.L P) row
local notation "roster" => window (k:=r) (g:=g) (f:=f) (D:=radius) near hub

/-- A real incident cable appears at the address of its opposite in the
complete, relative (hence coarse-block-independent) catalog. -/
def rosterIndex (named : ∀s o,code (P.fall s o)=N s o) (rk : r≤k) (base : ∀v,k-r≤P.b v)
    (fit : ∀v,P.b v≤k-f) (smooth : ∀v w,w∈near v→P.b v≤P.b w+radius)
    (full : ∀v,hub v=true→P.b v=k-f) (fg : f≤g) (gr : g≤r)
    (adj : ∀s i,(P.old (!s) i).1∈near (P.old s i).1)
    (block : ∀s i,(P.old (!s) i).2=(P.old s i).2)
    (single : ∀s i,¬(hub (P.old s i).1=true ∧ hub (P.old (!s) i).1=true))
    (s : Bool) (t : H) : LinkId P.owner s (.inr t) ↪ ↥(roster (relative k r (code t))) := by
  let opp := opposite P s t
  have real (e : LinkId P.owner s (.inr t)) :
      coarse k r (code (opp e))=coarse k r (code t) ∧
      k-r≤(code (opp e)).2.1.1 ∧ relative k r (code (opp e))∈roster (relative k r (code t)) := by
    obtain ⟨i,own,target⟩ := opposite_realized P s t e
    change P.fall (!s) (P.old (!s) i.val)=opp e at target
    rw [←target,←own,named,named]
    have eq := block s i.val
    have back := adj (!s) i.val
    simp only [Bool.not_not] at back
    refine ⟨?_,?_,?_⟩
    · rw [coarse_name near mass room P.b hub P.L row base fit gr,
        coarse_name near mass room P.b hub P.L row base fit gr,eq]
    · let o := P.old (!s) i.val
      have low : k-r≤leaf (D:=radius) (f:=f) near mass room P.b o.1 (rearrange P.L o.2) :=
        (base _).trans (le_max_left ..)
      cases hh : hub o.1
      · change k-r≤(name (D:=radius) (f:=f) (g:=g) near mass room P.b hub P.L row (!s) o).2.1.1
        simpa [name,hh] using low
      · change k-r≤(name (D:=radius) (f:=f) (g:=g) near mass room P.b hub P.L row (!s) o).2.1.1
        simp [name,hh];omega
    · have this := normalized_neighbor near mass room P.b hub P.L row rk base fit smooth full fg gr
        (adj s i.val) back (single s i.val) s (!s) (P.old s i.val).2
      have other : ((P.old (!s) i.val).1,(P.old s i.val).2)=P.old (!s) i.val := Prod.ext rfl eq.symm
      simpa only [other,Prod.eta] using this
  exact ⟨fun e=>⟨relative k r (code (opp e)),(real e).2.2⟩,fun a b same=>
    opposite_injective P s t (code.injective (relative_injective (real a).2.1 (real b).2.1
      ((real a).1.trans (real b).1.symm) (congrArg Subtype.val same)))⟩

/-- The actual binary digits sent to the padded tree use the full roster type.
This type and its encoding depend only on the normalized source name. -/
def bookAt (vertex : V↪ℕ) (t : H) {C : Type}
    (indices : C ↪ ↥(roster (relative k r (code t)))) : Book C :=
  ⟨codeHeight ↥(roster (relative k r (code t))),indices.trans (DescentRosterOrder.directory (DescentRosterOrder.endpoint vertex) _)⟩

omit [Fintype V] [Fintype H] in
theorem book_depth (vertex : V↪ℕ) (positive : 0<Δ) (degree : ∀v,(near v).card≤Δ) (t : H) {C : Type}
    (indices : C ↪ ↥(roster (relative k r (code t)))) :
    (bookAt (Δ:=Δ) (g:=g) (f:=f) near hub code vertex t indices).height≤
      terminalDepth Δ Y f g (code t).2.2.isSome := by
  let z := relative k r (code t)
  change Nat.clog 2 (Fintype.card ↥(roster z))≤terminalDepth Δ Y f g z.2.2.isSome
  rw [Fintype.card_coe]
  cases is : z.2.2.isSome
  · simpa [z,window,is,terminalDepth] using
      Nat.clog_mono_right 2 (hub_names (near z.1) (degree z.1) Y r z.2.1.2 radius f g)
  · simpa [window,is,terminalDepth] using
      nonhub_height (near z.1) positive (Nat.two_pow_pos _) (degree z.1) z.2.1.1 z.2.1.2 (r-g) hub

end
end Hierarchy.DescentRelativeContacts

namespace Hierarchy.DescentChosenRouter
open DescentRouterSlots
open scoped Classical
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] {k n : ℕ}

/-- Actual directed endpoint leaves have a common, reversible address after
the coarse block is erased, including empty orientation directories. -/
def Placement.CommonFallback (P : Placement V I H A k (2^n)) {Z : Type*} (name : H→Z) : Prop :=
  (∀s t t',name t=name t'→(P.fallbackBook s t).height=(P.fallbackBook s t').height) ∧
  ∀s t t',name t=name t'→∀(e : LinkId P.owner s (.inr t)) (e' : LinkId P.owner s (.inr t')),
    List.ofFn ((P.fallbackBook s t).codes e)=List.ofFn ((P.fallbackBook s t').codes e') ↔
      name (opposite P s t e)=name (opposite P s t' e')

/-- A true leaf of the published local trie reads the rank of its opposite
terminal among the common candidate names, using the shared host IDs. -/
structure Placement.LeafRoster (P : Placement V I H A k (2^n))
    (vertex : V↪ℕ) (name : H→V×DescentContacts.Endpoint (2^n)) where
  window : V×DescentContacts.Endpoint (2^n)→Finset (V×DescentContacts.Endpoint (2^n))
  depth : ∀s t,(P.fallbackBook s t).height=Nat.clog 2 (window (name t)).card
  digits : ∀s t (e : LinkId P.owner s (.inr t)),
    (DescentRotor.bitWord _ ((P.fallbackBook s t).codes e)).val=
      (Finset.univ.filter (fun y : ↥(window (name t))=>
        DescentRosterOrder.endpoint vertex y.val <
          DescentRosterOrder.endpoint vertex (name (opposite P s t e)))).card

end
end Hierarchy.DescentChosenRouter

namespace Hierarchy.DescentRelativeContacts
open DescentContacts DescentContactTree DescentFineTerminals DescentChosenRouter DescentRouterSlots
open scoped Classical
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
    {k r n f g Δ : ℕ} (P : Placement V I H A k (2^n))
local notation "radius" => (32*Nat.clog 2 (2*Δ))
variable (near : V→Finset V) (hub : V→Bool) (code : H ↪ V×Endpoint (2^n))
local notation "N" => fun t=>shortName (k-r) (code t)
local notation "roster" => window (k:=r) (g:=g) (f:=f) (D:=radius) near hub

private theorem digits {Z : Type} (order : Z↪ℕ) (a b : Finset Z) (eq : a=b) (u : ↥a) (v : ↥b) :
    List.ofFn (DescentRosterOrder.directory order a u)=List.ofFn (DescentRosterOrder.directory order b v) ↔ u.val=v.val := by
  subst b
  rw [List.ofFn_inj,(DescentRosterOrder.directory order a).injective.eq_iff,Subtype.ext_iff]

private theorem opposite_book (book : ∀ s t, DescentMixedRouter.Book (LinkId P.owner s (.inr t)))
    (s : Bool) (t : H) (e : LinkId P.owner s (.inr t)) :
    opposite {P with fallbackBook := book} s t e = opposite P s t e := by
  rcases e with ⟨a|p,hit⟩
  · simp [Placement.owner,DescentChosenRouter.owner] at hit
  · rfl

theorem common_book_install (vertex : V↪ℕ)
    (index : ∀s t,LinkId P.owner s (.inr t) ↪ ↥(roster (N t)))
    (origin : ∀s t e,(index s t e).val=N (opposite P s t e)) :
    ({P with fallbackBook := fun s t=>bookAt (Δ:=Δ) (k:=k) (r:=r) (f:=f) (g:=g) near hub code vertex t (index s t)}).CommonFallback N := by
  constructor
  · intro s t t' same
    change codeHeight ↥(roster (N t))=codeHeight ↥(roster (N t'))
    rw [same]
  · intro s t t' same a b
    let book := fun s t => bookAt (Δ:=Δ) (k:=k) (r:=r) (f:=f) (g:=g) near hub code vertex t (index s t)
    have nameAt (t : H) (e : LinkId P.owner s (.inr t)) :
        (index s t e).val = N (opposite {P with fallbackBook := book} s t e) :=
      (origin s t e).trans (congrArg N (opposite_book P book s t e).symm)
    refine (digits (DescentRosterOrder.endpoint vertex) _ _ (congrArg roster same)
      (index s t a) (index s t' b)).trans ?_
    exact ⟨fun h => (nameAt t a).symm.trans (h.trans (nameAt t' b)),
      fun h => (nameAt t a).trans (h.trans (nameAt t' b).symm)⟩

def issued_leaf_roster (vertex : V↪ℕ)
    (index : ∀s t,LinkId P.owner s (.inr t) ↪ ↥(roster (N t)))
    (origin : ∀s t e,(index s t e).val=N (opposite P s t e)) :
    ({P with fallbackBook:=fun s t=>bookAt (Δ:=Δ) (k:=k) (r:=r) (f:=f) (g:=g) near hub code vertex t (index s t)}).LeafRoster vertex N where
  window:=roster
  depth s t:=by apply congrArg (Nat.clog 2);exact Fintype.card_coe _
  digits s t e:=by
    let book := fun s t => bookAt (Δ:=Δ) (k:=k) (r:=r) (f:=f) (g:=g) near hub code vertex t (index s t)
    have endpoint := (origin s t e).trans (congrArg N (opposite_book P book s t e).symm)
    refine (DescentRosterOrder.directory_ord (DescentRosterOrder.endpoint vertex) _ (index s t e)).trans ?_
    exact congrArg (fun x : V × Endpoint (2^n) =>
      (Finset.univ.filter (fun y : ↥(roster (N t)) =>
        DescentRosterOrder.endpoint vertex y.val < DescentRosterOrder.endpoint vertex x)).card) endpoint

end
end Hierarchy.DescentRelativeContacts

end OAI
