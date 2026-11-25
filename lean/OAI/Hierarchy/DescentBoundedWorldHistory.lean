import OAI.Hierarchy.DescentRecipeNodeTypes
import OAI.Hierarchy.DescentBitGadget
import OAI.Hierarchy.DescentBitUnbundling
import OAI.Hierarchy.DescentOrdinaryHistory

namespace OAI
/-! # Typed local descriptions on actual selected worlds and their normalizations -/

namespace Hierarchy.DescentKernelHistory
open DescentSixParty Computability.BorderVNP.Crossing DescentHostDirectory
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}

namespace BitDescription
variable {W : MarkedWorld F d P bits} (B : BitDescription W)
def ofRecipe (R : Description W) : BitDescription W :=
  ⟨R.Tag,R.scalar,fun v=>BitRecipe.expose (R.recipe v) (boundaryWidth W.graph v),expose_reads _ _ _ _ R.correct⟩

def terminal : Description W :=
  ⟨(B.Tag×List ℕ)×List ℕ,BitRecipe.gatheredScalar B.scalar,fun v=>(B.recipe v).asRecipe,terminal_local W.graph B.scalar B.recipe W.tables B.correct⟩

def selected {I C : Type} [Fintype I] (G : PoweredGadget F) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) {Z : ℕ} (room : ∀i,z i≤Z)
    (pack : W.graph.Site→C) (p : I→Profile G.C) : BitDescription (W.selected G pick z hz fit pack p) :=
  ⟨B.Tag⊕GadgetTag G Z,Sum.elim B.scalar (gadgetScalar G),recordedBits G W.toWorld pick z hz fit room pack p B.recipe,
    recorded_bits_read G W.toWorld pick z hz fit room pack p B.recipe B.scalar B.correct⟩

def coalesced {V : Type} [DecidableEq V] (key : W.graph.Site→Key V) (flag : V→Bool) (k g : ℕ) :
    BitDescription (W.coalesced key flag k g) := by
  let loc := MarkedWorld.address W key flag k g
  let pos := fun _ : MarkedWorld.reclaimed W key flag k g=>(0:EuclideanSpace ℝ (Fin d))
  have ball (v : MarkedWorld.reclaimed W key flag k g) : ‖pos v‖≤1 := by simp [pos]
  exact ⟨B.Tag,B.scalar,quotientBits W.graph loc pos ball B.recipe,quotient_reads W.graph loc pos ball B.scalar B.recipe W.tables B.correct⟩

def pieces (m : W.graph.Edge→ℕ) (q : ℕ) (fit : ∀e∈W.core,W.graph.width e=m e*q) :
    BitDescription (W.pieces q m fit) :=
  ⟨B.Tag,B.scalar,unbundleBits W.graph W.core m q fit B.recipe,unbundle_reads W.graph W.core m q fit B.scalar B.recipe W.tables B.correct⟩

def renamed (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) : BitDescription (PhysicalRename.world W s e) where
  Tag := B.Tag
  scalar := B.scalar
  recipe v := (B.recipe (s.symm v)).reroute (PhysicalRename.boundaryBit W.graph s e v)
  correct := PhysicalRename.readsBits W.graph s e B.scalar W.tables B.recipe B.correct

def follow {W : MarkedWorld F d P bits} (normal : Normalize W) : BitDescription W→BitDescription normal.result := by
  induction normal with
  | done W => exact id
  | named W s e rest ih => exact fun b => ih (b.renamed s e)
  | merge W V key flag k g rest ih => exact fun b => ih (b.coalesced (V:=V) key flag k g)
  | split W q m fit rest ih => exact fun b => ih (b.pieces m q fit)

open DescentInitialHost Catalyst
def initial {k p : ℕ} (X : Approximation F k p) (R s : ℕ) (c : (initialGroup X R s).Choice) :
    BitDescription ((initialGroup X R s).state c) := ofRecipe (Description.initial X R s c)

end BitDescription
end
end Hierarchy.DescentKernelHistory

end OAI
