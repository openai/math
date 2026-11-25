import OAI.Hierarchy.DescentPrivateWireOrigin
import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentCableDonorNames
import OAI.Hierarchy.DescentPackedOperand
import OAI.Hierarchy.DescentRecordedBranch

namespace OAI
/-! # The two true raw-cable captures in the short private-word directory -/
namespace Hierarchy.DescentPrivateRawLabels
open DescentBundleHistory DescentSixParty DescentSharedCableNames DescentCableDonorNames
open DescentPackedOperand
open scoped Classical
noncomputable section
variable {F P J V I C : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype I]
    {d k i p D : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i)
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (prof : I→Profile G.C)
local notation "M" => GadgetNetwork.physical W.graph pick (branchWidth G z prof)
local notation "anchor" => DescentCableDonorNames.anchor pick
variable (loc : (GadgetNetwork.physical W.graph pick (branchWidth G z prof)).Site→C) (halo : Halo C W.graph.Site D)
    (arrive : ∀e : (GadgetNetwork.physical W.graph pick (branchWidth G z prof)).Edge,
      W.graph.src (DescentCableDonorNames.anchor pick e)∈halo.member (loc ((GadgetNetwork.physical W.graph pick (branchWidth G z prof)).src e)))

include S ready hz fit in
/-- Every raw p-word has a real first-grain old donor, including internal
six-party supply edges of positive width. -/
theorem parent_positive (_hp : 0<p) (w : WireWord M p) : 0<A.grainCount (anchor w.1) := by
  have oldPos : 0<W.graph.width (anchor w.1) := by
    rcases w with ⟨e|(⟨u,j⟩|⟨u,j⟩),x⟩
    · exact lt_of_lt_of_le (Nat.zero_lt_of_lt x.isLt) (Nat.div_le_self _ _)
    · exact (fit u 0).symm ▸ Nat.mul_pos (hz u) G.base_pos
    · exact (fit u 0).symm ▸ Nat.mul_pos (hz u) G.base_pos
  have fact:=A.grainCount_fit S ready (anchor w.1)
  apply Nat.pos_of_ne_zero
  intro zero
  rw [zero,Nat.zero_mul] at fact
  exact (Nat.ne_of_gt oldPos) fact

abbrev LocalWire (c : C) := {w : WireWord M p //loc ((M).src w.1)=c}
local notation "LocalAt" c => LocalWire (W:=W) (G:=G) (p:=p) pick z prof loc c

def root {c : C} (w : LocalAt c) : Fin D :=
  halo.slot c ⟨W.graph.src (anchor w.val.1),
    (congrArg (fun site => W.graph.src (anchor w.val.1) ∈ halo.member site) w.property).mp
      (arrive w.val.1)⟩
def old {c : C} (hp : 0<p) (w : LocalAt c) : Fin A.cap :=
  Stage.outgoing A native S ready ⟨anchor w.val.1,parent_positive A S ready pick z hz fit prof hp w.val⟩

/-- The unexpanded parent of all ten born rows is the first matched old
cable. Its fixed role digit identifies the literal old/arm/supply edge. -/
def ticket {c : C} (hp : 0<p) (w : LocalAt c) : ℕ :=
  11*(old A native S ready pick z hz fit prof loc hp w).val+(role w.val.1).val

theorem ticket_fields {c : C} (hp : 0<p) (u v : LocalAt c)
    (donor : root (W:=W) (G:=G) (p:=p) pick z prof loc halo arrive u=
      root (W:=W) (G:=G) (p:=p) pick z prof loc halo arrive v)
    (name : ticket A native S ready pick z hz fit prof loc hp u=ticket A native S ready pick z hz fit prof loc hp v)
    (chunk : u.val.2.val=v.val.2.val) : u=v := by
  have same : W.graph.src (anchor u.val.1)=W.graph.src (anchor v.val.1) :=
    congrArg Subtype.val ((halo.slot c).injective donor)
  have ru:=(role u.val.1).isLt
  have rv:=(role v.val.1).isLt
  unfold ticket at name
  have roleEq : role u.val.1=role v.val.1 := Fin.ext (by omega)
  have oldEq : old A native S ready pick z hz fit prof loc hp u=old A native S ready pick z hz fit prof loc hp v :=
    Fin.ext (by omega)
  have prev:=Stage.outgoing_identify A native S ready
    ⟨anchor u.val.1,parent_positive A S ready pick z hz fit prof hp u.val⟩
    ⟨anchor v.val.1,parent_positive A S ready pick z hz fit prof hp v.val⟩ same oldEq
  have wireEq:=identify pick (congrArg Subtype.val prev) roleEq
  apply Subtype.ext
  apply Sigma.ext wireEq
  apply (Fin.heq_ext_iff (congrArg (fun e=>(M).width e/p) wireEq)).mpr
  exact chunk

def capture {c : C} (hp : 0<p) (second : Bool) (peer : (LocalAt c)→ℕ) :
    (LocalAt c) ↪ Key where
  toFun w:=
    let ctor:=if second then Key.second else Key.first
    ctor (root (W:=W) (G:=G) (p:=p) pick z prof loc halo arrive w).val (peer w)
      (ticket A native S ready pick z hz fit prof loc hp w) w.val.2.val
  inj' := by
    intro a b eqn
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Key.first.injEq,Key.second.injEq] at eqn <;>
      exact ticket_fields A native S ready pick z hz fit prof loc halo arrive hp a b
        (Fin.ext eqn.1) eqn.2.2.1 eqn.2.2.2

end
end Hierarchy.DescentPrivateRawLabels

end OAI
