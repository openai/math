import OAI.Hierarchy.DescentCoalescedRecords
import OAI.Hierarchy.DescentPiecesSiteUnits

namespace OAI
/-! # The retained coefficient of each ordinary address after hub coalescence and unbundling -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentHostDirectory DescentNetworkPartition GadgetNetwork
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {d : ℕ} {P V Atom : Type} {bits : P→ℕ} [DecidableEq V]
variable (W : MarkedWorld F d P bits) (key : W.graph.Site↪Key V) (hub : V→Bool) (k g : ℕ)
local notation "addr" => address W key hub k g
local notation "coarse" => W.coalesced key hub k g

private theorem ordinary_wires (x : W.graph.Site) (no : hub (key x).1=false) :
    GadgetNetwork.siteLoad (coarse).graph (addr x) ≤ GadgetNetwork.siteLoad W.graph x := by
  classical
  let old (e : W.graph.Edge) := if W.graph.src e=x ∨ W.graph.dst e=x then W.graph.width e else 0
  let loc := addr
  have hit (y : W.graph.Site) : loc y=loc x ↔ y=x :=
    ⟨fun eqn=>(ordinary_unique W key hub k g x y no eqn.symm).symm,fun eqn=>congrArg loc eqn⟩
  let incl : (coarse).graph.Edge ↪ W.graph.Edge := Function.Embedding.subtype
    (fun e : W.graph.Edge => loc (W.graph.src e) ≠ loc (W.graph.dst e))
  calc
    _ ≤ ∑ e : (coarse).graph.Edge, old (incl e) := by
      unfold GadgetNetwork.siteLoad
      apply Finset.sum_le_sum
      intro e _
      split
      · rename_i incident
        have physical : loc (W.graph.src e.val) = loc x ∨ loc (W.graph.dst e.val) = loc x := incident
        have before : W.graph.src e.val=x ∨ W.graph.dst e.val=x :=
          physical.imp (hit _).mp (hit _).mp
        change W.graph.width e.val ≤ old e.val
        simp only [old,ite_eq_left before,le_refl]
      · exact Nat.zero_le _
    _ ≤ ∑ e : W.graph.Edge, old e := by
      have h := Finset.sum_le_sum_of_subset (f:=old)
        (Finset.subset_univ ((Finset.univ : Finset (coarse).graph.Edge).map incl))
      simpa only [Finset.sum_map] using h
    _ = _ := by
      unfold GadgetNetwork.siteLoad
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : W.graph.src e=x ∨ W.graph.dst e=x <;> simp only [old,h,ite_true,ite_false]

variable (q : ℕ) (m : (MarkedWorld.coalesced W key hub k g).graph.Edge → ℕ)
variable (fit : ∀ e : (MarkedWorld.coalesced W key hub k g).graph.Edge, e ∈ (MarkedWorld.coalesced W key hub k g).core →
  (MarkedWorld.coalesced W key hub k g).graph.width e = m e * q)
local notation "post" => MarkedWorld.pieces coarse q m fit
local notation "flag" => MarkedWorld.coalescedHub W key hub k g

/-- Retaining the complete old record list at the unique ordinary address and splitting
marked cables into pieces cannot increase the actual local coefficient there. -/
theorem coalesced_pieces_ordinary_le (rec : W.graph.Site→List Atom) (wire β hist : ℕ)
    (sep : ∀e,W.graph.src e≠W.graph.dst e) (x : W.graph.Site) (no : hub (key x).1=false) :
    (post).siteUnits flag (coalescedRecords W key hub k g rec) wire β hist (addr x) ≤
      W.siteUnits (fun u=>hub (key u).1) rec wire β hist x := by
  let entries := coalescedRecords W key hub k g rec
  let loc := addr x
  have no' : flag loc = false := (coalesced_at_hub W key hub k g x).trans no
  have retained : entries loc = rec x := coalescedRecords_ordinary W key hub k g rec x no
  calc
    _ = (coarse).siteUnits flag entries wire β hist loc :=
      pieces_siteUnits coarse q m fit flag entries wire β hist loc
    _ = wire * GadgetNetwork.siteLoad (coarse).graph loc + hist * (entries loc).length :=
      siteUnits_nonhub coarse flag entries wire β hist loc no' (fun e => e.property)
    _ ≤ wire * GadgetNetwork.siteLoad W.graph x + hist * (rec x).length := by
      rw [retained]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left wire (ordinary_wires W key hub k g x no)) _
    _ = _ := (siteUnits_nonhub W (fun u => hub (key u).1) rec wire β hist x no sep).symm

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
