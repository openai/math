import OAI.Hierarchy.DescentPackLabels
import OAI.Hierarchy.DescentOccurrenceColors
import OAI.Hierarchy.DescentBlockGroup

namespace OAI
/-! # Actual old wire count, block load and the immutable affine-color stream -/

namespace Hierarchy.DescentPacking
open Computability.BorderVNP.Crossing DescentWalshTables
open scoped BigOperators Classical
noncomputable section

variable {D : ℕ} {P : Type*} {bits : P→ℕ} (N : Network D P bits)
variable {C : Type} [Fintype C] [DecidableEq C] (core : Finset N.Edge) (home : N.Site→C)

theorem live_is_core :
    (∑u : N.Site,live (nativeTraffic N core home) u)=core.card := by
  let dest : (coreGraph N core).Edge → C := fun e => home (N.dst e.val)
  calc
    _ = Fintype.card (Atom (edgeTraffic (coreGraph N core) dest)) := by
      simp only [Atom,Fintype.card_sigma,Fintype.card_fin,live,nativeTraffic,dest]
      refine Finset.sum_congr (Finset.ext fun u =>
        ⟨fun _ => @Finset.mem_univ (coreGraph N core).Site _ u,
          fun _ => @Finset.mem_univ N.Site _ u⟩) ?_
      intro u _
      refine Finset.sum_congr (by ext c; simp) ?_
      intro c _
      exact Fintype.card_congr (Equiv.refl _)
    _ = Fintype.card (coreGraph N core).Edge := (Fintype.card_congr (graphAtom _ dest)).symm
    _ = core.card := Fintype.card_coe core

theorem colony_rows (pay : N.Site→ℕ) :
    (∑c,amount pay (groupStream home c))=∑u,pay u := by
  simp only [amount_groupStream]
  rw [Finset.sum_comm]
  simp

theorem group_wire_amount :
    (∑c,amount (live (nativeTraffic N core home)) (groupStream home c))=core.card :=
  (colony_rows N home _).trans (live_is_core N core home)

theorem uniform_volume {q : ℕ} (fixedWidth : ∀e∈core,N.width e=q) :
    (∑e∈core,N.width e)=q*core.card := by
  calc
    _ = ∑_e∈core,q := Finset.sum_congr rfl fixedWidth
    _ = _ := by simp [Nat.mul_comm]

omit [Fintype C] in
theorem group_side {k : ℕ} (addr : N.Site→Bits k) (a : Bits k) (b : ZMod 2) (t : Bool) (c : C) :
    side addr a b t (groupStream home c)=colorSites home (fun u=>decide (binaryRow a (addr u)+b=0)) t c := rfl

/-- Stacking different prior histories into a group preserves each old cable's
block address for every choice of invertible permutation or affine coloring. -/
theorem group_endpoints {I : Type} [Fintype I] {F : Type*} [Field F] {Ps : I→Type*}
    {widths : ∀i,Ps i→ℕ} (A : ∀i,DescentSixParty.World F D (Ps i) (widths i))
    {Z : Type*} (address : I→Z) (e : (DescentSixParty.blockGraph A).Edge) :
    address (((DescentSixParty.blockGraph A).src e).1)=address (((DescentSixParty.blockGraph A).dst e).1) := rfl

end
end Hierarchy.DescentPacking

end OAI
