import OAI.Hierarchy.DescentFallbackLeafScan
import OAI.Hierarchy.DescentResetSourceFrame

namespace OAI
/-! # Reading the installed book's bit index by scanning the previous host aperture -/

namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentGL DescentColonies DescentChosenRouter DescentRelativeContacts DescentRouterSlots
open DescentFallbackLeafScan
open scoped Classical
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
variable {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
variable (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K Δ : ℕ)
    (wt : V→Block k→ℕ) (flow : V→V→Block k→ℝ)
variable (roster : SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K flow Δ wt)
local notation "fallbackDegree" => 32*Nat.clog 2 (2*Δ)
local notation "hub'" => fun v=>hub (frame.host.symm v)
local notation "p" => Z.placement
local notation "win" => DescentFineTerminals.window (k:=Z.k-T.commonDepth) (D:=fallbackDegree) (g:=g) (f:=f) T.columns.near hub'
local notation "name" => fun (t : Z.Fallback)=>shortName T.commonDepth (T.code t)
variable (peer : V→Fin Δ→Option V) (real : ∀v x,x∈near v ↔ ∃j,peer v j=some x)
local notation "row" => fun (v : Z.V) (j : Fin Δ)=>Option.map frame.host (peer (frame.host.symm v) j)

include roster real

theorem actual_roster : ∀v x,x∈T.columns.near v ↔ ∃j,row v j=some x := by
  intro v x
  obtain ⟨a,rfl⟩:=frame.host.surjective v
  obtain ⟨b,rfl⟩:=frame.host.surjective x
  rw [roster.2.1 a b,real a b]
  change (∃j,peer a j=some b) ↔
    ∃j,Option.map frame.host (peer (frame.host.symm (frame.host a)) j)=some (frame.host b)
  rw [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨j,Option.map_eq_some_iff.mpr ⟨b,hj,rfl⟩⟩
  · rintro ⟨j,hj⟩
    obtain ⟨q,hq,atHost⟩ := Option.map_eq_some_iff.mp hj
    exact ⟨j,hq.trans (congrArg some (frame.host.injective atHost))⟩

theorem source_leaf (s : Bool) (t : Z.Fallback) (e : LinkId (p).owner s (.inr t)) :
    (DescentRotor.bitWord _ (((p).fallbackBook s t).codes e)).val=
      (Finset.univ.filter (fun j : Fin Δ×Fin (2^Ht)=>
        ((candidate (k:=Z.k-T.commonDepth) (D:=fallbackDegree) (g:=g) (f:=f) hub' row (name t) j).any
          (fun x=>decide (DescentRosterOrder.endpoint T.columns.host x <
            DescentRosterOrder.endpoint T.columns.host (name (opposite (p) s t e))))))).card := by
  let src:=name t
  let test (x : Z.V × DescentContacts.Endpoint (2^Z.n)) := decide (DescentRosterOrder.endpoint T.columns.host x <
    DescentRosterOrder.endpoint T.columns.host (name (opposite (p) s t e)))
  have real':=actual_roster frame vertex near n f B wire K Δ wt flow roster peer real
  have same:=roster.2.2.2.2.1 src
  have room : (win src).card≤2^Ht := by
    rw [←same]
    exact (Nat.le_pow_clog (by decide : 1<2) _).trans
      (Nat.pow_le_pow_right (by decide) ((T.leaves.depth s t).symm.le.trans (T.bookHeight s t)))
  rw [T.leaves.digits s t e]
  have eqn:=scan_card T.columns.near hub' row real' src room test
  rw [←same] at eqn
  simpa [test,src] using eqn.symm

theorem source_height (s : Bool) (t : Z.Fallback) :
    ((p).fallbackBook s t).height=Nat.clog 2
      (Finset.univ.filter (fun j : Fin Δ×Fin (2^Ht)=>
        (candidate (k:=Z.k-T.commonDepth) (D:=fallbackDegree) (g:=g) (f:=f) hub' row (name t) j).isSome)).card := by
  let src:=name t
  have real':=actual_roster frame vertex near n f B wire K Δ wt flow roster peer real
  have same:=roster.2.2.2.2.1 src
  have room : (win src).card≤2^Ht := by
    rw [←same]
    exact (Nat.le_pow_clog (by decide : 1<2) _).trans
      (Nat.pow_le_pow_right (by decide) ((T.leaves.depth s t).symm.le.trans (T.bookHeight s t)))
  have eqn:=scan_card T.columns.near hub' row real' src room (fun _=>true)
  have any (o : Option (Z.V×DescentContacts.Endpoint (2^Z.n))) : o.any (fun _=>true)=o.isSome := by cases o <;> rfl
  have hits : (Finset.univ.filter (fun j : Fin Δ×Fin (2^Ht)=>
      (candidate (k:=Z.k-T.commonDepth) (D:=fallbackDegree) (g:=g) (f:=f) hub' row src j).isSome)).card =
      (win src).card := by simpa [any] using eqn
  exact (T.leaves.depth s t).trans (congrArg (Nat.clog 2) ((congrArg Finset.card same).trans hits.symm))

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
