import OAI.Hierarchy.DescentBitQuotient
import OAI.Hierarchy.DescentRecordedHistory

namespace OAI
/-! # Original atoms and six genuinely new scalar calls under one selected substitution -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentSixParty GadgetNetwork
open scoped Classical BigOperators
noncomputable section
variable {U P I C F : Type} [Field F] [Fintype I] {d : ℕ} {w : P→ℕ}
variable (G : PoweredGadget F) (W : World F d P w) (pick : I×Fin 2↪W.graph.Edge)
variable (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b)
variable {Z : ℕ} (room : ∀i,z i≤Z) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "sw" => branchWidth G z p
local notation "M" => physical W.graph pick sw
local notation "loc" => newSite W.graph pick (bestLayout sw) pack
local notation "pos" => (fun _ : Merged W.graph pick (bestLayout sw) pack => (0:EuclideanSpace ℝ (Fin d)))
local notation "ball" => (fun v=> (by simp : ‖pos v‖≤1))
variable (old : SiteBits (U:=U) W.graph) (scalar : U→List (List Bool)→F)

private theorem boundary_input_length {n : ℕ} (net : Network n P w) {u : net.Site}
    (edge : ∀e : Incident net u, Word (net.width e.val))
    (pin : ∀a : Attached net u, Word (w a.val)) (b : Boundary net u) :
    (input net edge pin b).length = boundaryWidth net u b := by
  cases b <;> exact List.length_ofFn

private theorem boundary_input_sample {n : ℕ} (net : Network n P w) {u : net.Site}
    (edge : ∀e : Incident net u, Word (net.width e.val))
    (pin : ∀a : Attached net u, Word (w a.val)) (b : BitRef (boundaryWidth net u)) :
    (input net edge pin b.1).getD b.2.val false = localBit net edge pin b := by
  rcases b with ⟨e | a, j⟩ <;> exact finiteWord_read _ j false

private theorem carriedBit_width (u : W.graph.Site) (b : Boundary W.graph u) :
    boundaryWidth (M) (.inl u) (oldBoundary W.graph pick sw u b) = boundaryWidth W.graph u b := by
  let edges : Local W.graph pick sw (.inl u) := fun _ _ => false
  let pins : (a : Attached (M) (.inl u)) → Word (w a.val) := fun _ _ => false
  have lengths := congrArg List.length (congrFun (old_input W.graph pick sw u edges pins) b)
  exact (boundary_input_length (M) edges pins (oldBoundary W.graph pick sw u b)).symm.trans
    (lengths.trans (boundary_input_length W.graph _ _ b))

def carriedBit (u : W.graph.Site) (b : BitRef (boundaryWidth W.graph u)) :
    BitRef (boundaryWidth (M) (.inl u)) :=
  ⟨oldBoundary W.graph pick sw u b.1, Fin.cast (carriedBit_width G W pick z p u b.1).symm b.2⟩

private theorem carriedBit_read (u : W.graph.Site) (edge : Local W.graph pick sw (.inl u))
    (pin : (a : Attached (M) (.inl u)) → Word (w a.val)) (b : BitRef (boundaryWidth W.graph u)) :
    localBit (M) edge pin (carriedBit G W pick z p u b) =
      localBit W.graph (siteWord W.graph pick sw u edge) (fun a => pin ⟨a.1, congrArg Sum.inl a.property⟩) b := by
  have sample := congrArg (fun xs : List Bool => xs.getD b.2.val false)
    (congrFun (old_input W.graph pick sw u edge pin) b.1)
  exact (boundary_input_sample (M) edge pin (carriedBit G W pick z p u b)).symm.trans
    (sample.trans (boundary_input_sample W.graph _ _ b))

def physicalBits (v : (M).Site) :
    BitRecipe (U ⊕ GadgetTag G Z) (Boundary (M) v) (boundaryWidth (M) v) :=
  match v with
  | .inl u=>((old u).reroute (carriedBit G W pick z p u)).retag Sum.inl
  | .inr (i,j)=>(BitRecipe.expose (roleRecipe G W.graph pick z room p i j) (boundaryWidth (M) _)).retag Sum.inr

def recordedBits (c : (recorded G W pick z hz fit pack p).graph.Site) :
    BitRecipe (U ⊕ GadgetTag G Z) (Boundary (recorded G W pick z hz fit pack p).graph c) (boundaryWidth (recorded G W pick z hz fit pack p).graph c) :=
  quotientBits (M) loc pos ball (physicalBits G W pick z room p old) c

theorem recorded_bits_read (valid : ReadsBits W.graph scalar old W.tables) :
    ReadsBits (recorded G W pick z hz fit pack p).graph (Sum.elim scalar (gadgetScalar G)) (recordedBits G W pick z hz fit room pack p old) (recorded G W pick z hz fit pack p).tables := by
  apply quotient_reads
  apply (reads_iff_local ..).mpr
  intro v
  rcases v with u|⟨i,j⟩
  · intro read pin
    rw [physicalBits,BitRecipe.retag_eval,BitRecipe.reroute_eval]
    change (old u).value scalar _=W.tables u _ _
    rw [←(reads_iff_local W.graph scalar old W.tables).mp valid u]
    apply congrArg ((old u).value scalar)
    exact funext (carriedBit_read G W pick z p u read pin)
  · intro read pin
    let words : ∀b : Boundary (M) (.inr (i,j)),Word (boundaryWidth (M) (.inr (i,j)) b) :=
      fun b=>match b with | .inl e=>read e | .inr a=>pin a
    have eqBits : localBit (M) read pin=(fun b=>words b.1 b.2) := by funext b;rcases b with ⟨_|_,t⟩ <;> rfl
    have eqWords : (fun b=>wordList (words b))=input (M) read pin := by funext b;cases b <;> rfl
    rw [physicalBits,BitRecipe.retag_eval,eqBits,BitRecipe.expose_eval,eqWords]
    exact role_read G W.graph pick z hz fit room p i j read pin

end
end Hierarchy.DescentKernelHistory

end OAI
