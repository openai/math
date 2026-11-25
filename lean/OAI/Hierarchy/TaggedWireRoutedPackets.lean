import OAI.Hierarchy.TaggedWireInstalls
import OAI.Hierarchy.ProbeStripOccupancy
import OAI.Hierarchy.ProbeSelectedPacketWidths

namespace OAI
/-! # The signed packet followed by its physical stock, radius, and tree turns -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open Probe AdaptiveProbe Strip
open scoped BigOperators Classical

variable {S N H copies : ℕ} {F : Type} [Field F]

/-- The ordered old rows are the signed physical roles and broadcast edges. The
new rows are the actual native inventory/paid edge directory, including aliases. -/
structure RowRouting (row : Row F S H copies) (phys : Fin N→Chord S) where
  Roles : Type
  [finite : Fintype Roles]
  source : Roles→Chord S
  bits : Histogram (Fin H) copies→Roles→ℕ
  shape : ∀c,optionWidths source (bits c)=row.output c
  install : Installs source phys
  order : Fin (Fintype.card Roles)≃Roles
  occurrences : ℕ
  ordinal : Fin occurrences≃Σi,Fin ((install.steps order) i).length

attribute [instance] RowRouting.finite

namespace RowRouting
variable {row : Row F S H copies} {phys : Fin N→Chord S} (R : RowRouting row phys)

def post (c : Histogram (Fin H) copies) := installedWidths phys (R.install.load (R.bits c))

def entry (c : Histogram (Fin H) copies) : SiteMatrix (State row.input) (State (R.post c)) F :=
  SiteMatrix.compose (row.entry c) (Installs.transport (R.shape c) rfl (R.install.operator R.order (R.bits c) R.ordinal))

theorem entry_sum (x : ∀s,State row.input s) :
    (raw F row.input).coeff x=∑c,SiteMatrix.act (R.entry c) (raw F (R.post c)).coeff x := by
  rw [row.sum x]
  apply Finset.sum_congr rfl
  intro c _
  let K:=Installs.transport (R.shape c) rfl (R.install.operator (F:=F) R.order (R.bits c) R.ordinal)
  have routed : (raw F (row.output c)).coeff=SiteMatrix.act K (raw F (R.post c)).coeff := by
    funext y
    exact Installs.transported (R.shape c) rfl _ (R.install.operator_action R.order (R.bits c) R.ordinal) y
  rw [routed]
  exact SiteMatrix.act_compose (row.entry c) K (raw F (R.post c)).coeff x

def of_strip {n k : ℕ} {E Ball : Type} [Fintype E] [Fintype Ball]
    (roles : E→DistinctPair (TreeSite n k)) (place : Ball×TreeSite n k ↪ Fin S) (u : Ball)
    (width : Histogram (Fin H) copies→E→ℕ) (selector : ℕ)
    (physical : ∀c,row.output c=optionWidths (reportedRole place roles u) (width c)+
      optionWidths (reportedRole place (treeEnds n k) u) (fun _=>selector))
    (placed : Installs (Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)) phys)
    (order : Fin (Fintype.card (E⊕TreeLink n k))≃E⊕TreeLink n k)
    {r : ℕ} (ordinal : Fin r≃Σi,Fin ((placed.steps order) i).length) : RowRouting row phys where
  Roles := E⊕TreeLink n k
  source := Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)
  bits c := Sum.elim (width c) (fun _=>selector)
  shape c := (option_pair _ _ _ _).trans (physical c).symm
  install := placed
  order := order
  occurrences := r
  ordinal := ordinal

def skipped (phys : Fin N→Chord S) (H : ℕ) : RowRouting (Row.skipped (F:=F) (S:=S) H) phys where
  Roles := Empty
  source := Empty.elim
  bits _ := Empty.elim
  shape _ := by simp [optionWidths,Row.output]
  install := ⟨Empty.elim,fun i=>i.elim⟩
  order := (Fintype.equivFin Empty).symm
  occurrences := 0
  ordinal :=
    { toFun := Fin.elim0
      invFun := fun z => Empty.elim ((Fintype.equivFin Empty).symm z.1)
      left_inv := fun i => Fin.elim0 i
      right_inv := fun z => Empty.elim ((Fintype.equivFin Empty).symm z.1) }

end RowRouting
end Hierarchy.WireTelescope.ChosenPackets

end
end OAI
