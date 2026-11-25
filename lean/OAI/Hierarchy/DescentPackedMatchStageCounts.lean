import OAI.Hierarchy.DescentPackedMatchStageSeats
import OAI.Hierarchy.DescentPackedMatchCensus
import OAI.Hierarchy.DescentPackedMatchLiveAmount

namespace OAI
/-! # Measured full packed source histogram for the actual marked graph -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentStageEdgeReceipt DescentSIMDLookup
open scoped Classical
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
variable (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "keyCount" => 2^(k+1)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage

def blank (r D p d : ℕ) : Panel r D p d := ⟨fun _=>0,fun _ _=>0,fun _ _=>0⟩

def spread {r D p d : ℕ} (u : J×V→Panel r D p d) (h : Fin H) (g : Fin G) : Panel r D p d :=
  if live : ∃ z : J×V,groups z.1=g ∧ hosts z.2=h then u live.choose else blank r D p d

omit [DecidableEq V] [DecidableEq J] in
theorem spread_hit {r D p d : ℕ} (u : J×V→Panel r D p d) (z : J×V) :
    spread groups hosts u (hosts z.2) (groups z.1)=u z := by
  have hit : ∃y : J×V,groups y.1=groups z.1 ∧ hosts y.2=hosts z.2 := ⟨z,rfl,rfl⟩
  rw [spread,dite_eq_left hit]
  exact congrArg u (Prod.ext (groups.injective hit.choose_spec.1) (hosts.injective hit.choose_spec.2))

variable (rank : (J×V)↪ℕ) (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 + (scanColorAt he A.stage u).toNat)
    (sorted : RosterSorted A next rank) (route : Routes A native S ready names next) (df : A.degree<2^short)
variable (profile : ℕ)
local notation "s" => shape (2^k) A.degree (2*A.cap) profile
local notation "real" => spread groups hosts panel
local notation "descriptors" => Gather.flat (Gather.descriptorInputs (K:=keyCount) s A.cap real)

include coord named fit winner sorted route df in
theorem all_counts :
    Chronology.Counts (slot he A groups hosts hm) (countIn he A)
      (fun i=>laneCounts s M (topologyWords s descriptors i)) := by
  refine graph_counts (C:=ScanColonies he A.stage) s hm descriptors ?_ (sourceIndex he A groups hosts) (countIn he A) ?_ ?_
    (slot he A groups hosts hm) (slot_eq he A groups hosts hm)
  · intro h g
    let kh : Fin keyCount × Fin H := finProdFinEquiv.symm h
    exact shape_bounded profile A.cap kh.1.val (real kh.2 g) (fun _=>0)
  · intro c
    let z : J×V := (addr c).1
    have measured := live_amount (short:=short) A native S ready names win next he rank coord named fit winner sorted route df profile c (fun _=>0)
    have found : real (hosts z.2) (groups z.1)=panel z := spread_hit groups hosts panel z
    rw [sourceIndex_eq he A groups hosts c]
    simp only [Gather.flat,Equiv.symm_apply_apply,Gather.descriptorInputs]
    exact (congrArg (fun u : Panel (2^k) A.degree (2*A.cap) short =>
      PackedMatch.amount (inputs s A.cap (keyAt he A c).val u (fun _=>0))) found).trans measured
  · intro h g missing
    let vh : Fin keyCount × Fin H := finProdFinEquiv.symm h
    change PackedMatch.amount (inputs s A.cap vh.1.val (real vh.2 g) (fun _=>0))=0
    by_cases host : ∃z : J×V,groups z.1=g ∧ hosts z.2=vh.2
    · obtain ⟨z,zg,zh⟩:=host
      have hole : ¬∃c : ScanColonies he A.stage,(addr c).1=z ∧ heap (addr c).2=vh.1.val := by
        rintro ⟨c,hc,hk⟩
        apply missing c
        have key : keyAt he A c=vh.1 := Fin.ext hk
        have atHost := (congrArg (fun z : J×V => hosts z.2) hc).trans zh
        have atGroup := (congrArg (fun z : J×V => groups z.1) hc).trans zg
        refine (sourceIndex_eq he A groups hosts c).trans (Prod.ext ?_ atGroup)
        exact (congrArg finProdFinEquiv (Prod.ext key atHost)).trans (finProdFinEquiv.apply_symm_apply h)
      have chosen : real vh.2 g=panel z := by
        rw [←zg,←zh]
        exact spread_hit groups hosts panel z
      rw [chosen,ghost_inputs (short:=short) A native S ready names win next he fit winner s A.cap vh.1.val z hole]
      exact amount_zero s _ (fun _=>rfl)
    · have empty : real vh.2 g=blank (2^k) A.degree (2*A.cap) short := by
        unfold spread
        rw [dite_eq_right host]
      rw [empty,vacant s A.cap vh.1.val (blank _ _ _ _) (fun _ alive=>False.elim (alive rfl))]
      exact amount_zero s _ (fun _=>rfl)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
