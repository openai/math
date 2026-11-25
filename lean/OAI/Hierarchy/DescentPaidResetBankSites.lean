import OAI.Hierarchy.DescentPaidResetBank
import OAI.Hierarchy.DescentInstalledRotorLayers
import OAI.Hierarchy.DescentBatchedReentry
import OAI.Hierarchy.DescentPackedInstalledPrivate

namespace OAI
/-! # Mixed-bank population at a genuine selected reset site -/
namespace Hierarchy.DescentBatchedBank
open Computability.BorderVNP.Crossing DescentRotor DescentKernelHistory DescentResetGates DescentMixedRouter
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits M : ℕ} (G : Graph n h) (hw : 0<bits) (u m p : ℕ) (hp : 0<p) (fit : u=m*p)
variable (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin M) (D : ℕ)
variable (select : ∀s w,Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align s w)
local notation "bank" => DescentMixedRouter.network G hw u contact input site owner align select D
local notation "coeff" => DescentMixedRouter.Ordered.coefficients G hw u contact input site owner align key D select


local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align
set_option quotPrecheck false in
local notation "dev" => DescentMixedRouter.device G hw u contact input site owner align (D:=D)
open DescentContactTree DescentPaidResidentCount.Reset DescentRouterSlots

open private Hierarchy.DescentChosenRouter.circuitLayers from
  OAI.Hierarchy.DescentInstalledRotorLayers

def localFund (s : Bool) (w : W) : (z : Ch s w)→(dev z).Site→ℕ
  | .good _ _ _ chip,v=>
    let layers := Hierarchy.DescentChosenRouter.circuitLayers chip
    Rotor.funded G C₀ bits m layers ((DescentCommonPalette.rotorSiteEquiv G D layers C₀ bits u).symm v)
  | .exceptional data,⟨j,node⟩=>Fintype.card (Cell
      (DescentFixedNamedContact.code data.book.codes (link contact owner s w)) j.val node)*m

omit [Fintype R] in
theorem sized_funds (v : (bank).Site) :
    Fintype.card (sizedProgram G hw u m p hp fit contact input site owner align key D select v).Node=
      localFund G hw u m contact input site owner align D v.1.1 v.1.2 (select v.1.1 v.1.2) v.2 := by
  subst u
  rcases v with ⟨⟨side,root⟩,v⟩
  change Fintype.card (deviceProgram G hw m p hp contact input site owner align key D (select side root) v).Node=
    localFund G hw (m*p) m contact input site owner align D side root (select side root) v
  revert v
  dsimp only
  generalize select side root=choice
  intro v
  cases choice with
  | exceptional data=>
    rcases v with ⟨j,node⟩
    let Nodes := Cell (DescentFixedNamedContact.code data.book.codes (link contact owner side root)) j.val node
    calc
      _ = Fintype.card (Nodes × Fin m) := Fintype.card_congr (Equiv.refl _)
      _ = Fintype.card Nodes * m := by rw [Fintype.card_prod,Fintype.card_fin]
      _ = _ := congrArg (· * m) (Fintype.card_congr (Equiv.refl _))
  | good first last pay P=>
    exact Rotor.physical D m p hp contact input site owner align side root G first last P key v
end
end Hierarchy.DescentBatchedBank

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots
open DescentPackedFallbackTree
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "fits" => frame.enough.trans (Nat.sub_le ..)
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "theSite" => DescentIssuedFallbackPanel.endSite A


local notation "slots" => 2^(m-c)*(2*A.cap)
set_option quotPrecheck false in
local notation "treeBook" => fun s t=>(R).fallbackBook s t
set_option quotPrecheck false in
local notation "dest" => fun s t=>(treeBook s t).codes



open DescentPaidResidentCount.Reset DescentPaidResidentCount.Reset.BankIssue DescentPackedPrivateMenu
open DescentMixedRouter DescentPackedFallbackTree DescentSharedCableNames
variable {L : ℕ} (key : (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)).graph.Edge↪Fin L) (batch p : ℕ) (positive : 0<p)
    (unit : 0<Z.unit) (multiple : Z.unit=batch*p) {Hbound : ℕ} (vertex : Z.V↪Fin Hbound)
local notation "arr" => leafPanel A S ready digits native Z T frame
local notation "chosen" => DescentChosenRouter.selected (R) Z.graph Z.positive Z.pay Z.circuit
set_option quotPrecheck false in
local notation "dev" => DescentMixedRouter.device Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align (D:=d)
set_option quotPrecheck false in
local notation:max "rootKey" side:arg g:arg => Z.rootsOf T vertex unit side (arr side) (Z.rootTicket T g)
  (vertex (Z.rootVertex T g)) (Z.rootBlock T g)

def fundedSite (side : Bool) : (t : (R).Site)→(dev (chosen side t)).Site→BankIssue.Site Z.graph Ht
  | .inl good,actor=>
    let layers := DescentChosenRouter.selectedRotorLayers (R) Z.graph Z.positive Z.pay Z.circuit side good
    .rotor ((DescentCommonPalette.rotorSiteEquiv Z.graph d layers C Z.width Z.unit).symm actor)
  | .inr t,⟨q,node⟩=>.tree ⟨q.val,lt_of_lt_of_le q.isLt (Nat.succ_le_succ (T.bookHeight side t))⟩ node

private theorem card_using {α : Type*} {i j : Fintype α} {n : ℕ}
    (count : @Fintype.card α j = n) : @Fintype.card α i = n :=
  (@Fintype.card_congr α α i j (Equiv.refl _)).trans count

theorem bank_paid (side : Bool) (t : (R).Site) (actor : (dev (chosen side t)).Site) :
    Fintype.card (Z.laneRecipe key batch p positive multiple ⟨(side,t),actor⟩).Node=
      BankIssue.amount Z.graph C Z.width batch (fundedSite A S ready Z T side t actor) (rootKey side t) := by
  change Fintype.card (Z.laneProgram key batch p positive multiple ⟨(side,t),actor⟩).Node=_
  refine (DescentBatchedBank.sized_funds Z.graph Z.positive Z.unit batch p positive multiple
    (R).contact (R).input (R).site (R).owner (R).align key d chosen ⟨(side,t),actor⟩).trans ?_
  rw [Z.rootsOf_read]
  cases t with
  | inl good=>
    let layers := DescentChosenRouter.selectedRotorLayers (R) Z.graph Z.positive Z.pay Z.circuit side good
    let bare := (DescentCommonPalette.rotorSiteEquiv Z.graph d layers C Z.width Z.unit).symm actor
    change Rotor.funded Z.graph C Z.width batch layers bare =
      Rotor.funded Z.graph C Z.width batch (Z.circuit side good).layers bare
    exact congrArg (fun l => Rotor.funded Z.graph C Z.width batch l bare)
      (DescentChosenRouter.selectedRotorLayers_eq (R) Z.graph Z.positive Z.pay Z.circuit side good)
  | inr t=>
    rcases actor with ⟨j,node⟩
    have population := bank_population A S ready digits native Z T frame side t ⟨j,node⟩
    let level : Fin (Ht+1) := ⟨j.val,j.isLt.trans_le (Nat.succ_le_succ (T.bookHeight side t))⟩
    calc
      _ = DescentPackedFallbackTree.count (arr side t) (Tree.window Ht node) * batch :=
        congrArg (· * batch) (card_using population)
      _ = _ := (BankIssue.tree_amount (l:=Z.layerBits) Z.graph C Z.width batch
        (DescentResetCableSlots.interval (Z.k-T.commonDepth) (Z.fallLabel T t))
        (DescentResetCableSlots.optional (T.code t).2.2) (Z.placement.fallbackBook side t).height
        (T.bookHeight side t) (arr side t) level node (Nat.le_of_lt_succ j.isLt)).symm

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
