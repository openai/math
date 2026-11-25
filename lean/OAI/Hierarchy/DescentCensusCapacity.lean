import OAI.Hierarchy.DescentIntegralSiteLoad
import OAI.Hierarchy.DescentChosenOccupied

namespace OAI
/-! # Public capacities for the occupied rows of a branch-dependent graph census -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing DescentColonies
open scoped Classical BigOperators
noncomputable section
variable {F P V Aty : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits)

def blank : Finset W.graph.Edge :=
  W.coreᶜ.filter (fun e=>W.graph.width e=0)

omit [Field F] in
/-- Each counted edge occupies at least one paid grain at its own source.
Loops are still counted once. The reserve is independent of the scalar data. -/
theorem census_paid (edges : Finset W.graph.Edge) (pos : W.graph.Site→V) (blk : W.graph.Site→Block k)
    (hub : W.graph.Site→Bool) (records : W.graph.Site→List Aty) (wire hist grain cap : ℕ)
    (hw : 0<wire) (hg : 0<grain) (unit : ∀e∈edges,grain≤W.graph.width e)
    (paid : ∀v x,StarKeys.blockMass W.graph pos blk (W.siteUnits hub records wire 256 hist) v x≤wire*grain*cap) :
    edges.card≤(Fintype.card V*2^k)*cap := by
  let active (e : W.graph.Edge) := if e∈edges then wire*grain else 0
  have each (v : W.graph.Site) :
      (∑e,if v=W.graph.src e then active e else 0)≤W.siteUnits hub records wire 256 hist v := by
    unfold siteUnits
    apply le_trans _ (Nat.le_add_right _ _)
    apply le_trans _ (Nat.le_add_right _ _)
    apply Finset.sum_le_sum
    intro e _
    by_cases src : v=W.graph.src e
    · by_cases mem : e∈edges
      · have first:=Nat.mul_le_mul_left wire (unit e mem)
        have factor : 1≤(if hub (W.graph.src e) then 256 else 1 : ℕ) := by split <;> decide
        have next:=Nat.mul_le_mul_left (wire*W.graph.width e) factor
        simpa [active,src,mem] using first.trans (by simpa using next)
      · simp [active,src,mem]
    · simp [src]
  have volume : wire*grain*edges.card≤(Fintype.card V*2^k)*(wire*grain*cap) := calc
    _ = ∑e,active e := by simp [active,Finset.sum_ite_mem,Nat.mul_comm]
    _ = ∑v : W.graph.Site,∑e,if v=W.graph.src e then active e else 0 := by
      rw [Finset.sum_comm];simp
    _ ≤ ∑v,W.siteUnits hub records wire 256 hist v := Finset.sum_le_sum (fun v _=>each v)
    _ = ∑v,∑x,StarKeys.blockMass W.graph pos blk (W.siteUnits hub records wire 256 hist) v x :=
      (StarKeys.total_blockMass W.graph pos blk _).symm
    _ ≤ ∑_v : V,∑_x : Block k,wire*grain*cap :=
      Finset.sum_le_sum (fun v _=>Finset.sum_le_sum (fun x _=>paid v x))
    _ = _ := by simp [DescentColonies.Block,Nat.mul_assoc]
  apply (Nat.le_of_mul_le_mul_left (c:=wire*grain) _ (Nat.mul_pos hw hg))
  simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using volume

omit [Field F] in
/-- Genuine zero-width trunks are included separately. Counting the surviving
physical records does not require treating an empty trunk as a bit. -/
theorem census_all (pos : W.graph.Site→V) (blk : W.graph.Site→Block k)
    (hub : W.graph.Site→Bool) (records : W.graph.Site→List Aty) (wire hist grain cap : ℕ)
    (hw : 0<wire) (hg : 0<grain) (divs : ∀e,grain∣W.graph.width e)
    (core : ∀e∈W.core,W.graph.width e=grain)
    (paid : ∀v x,StarKeys.blockMass W.graph pos blk (W.siteUnits hub records wire 256 hist) v x≤wire*grain*cap) :
    Fintype.card W.graph.Edge ≤ (Fintype.card V*2^k)*cap+W.blank.card := by
  have good (e : W.graph.Edge) (h : e∈W.blankᶜ) : grain≤W.graph.width e := by
    by_cases mark : e∈W.core
    · exact (core e mark).ge
    · have positive : 0<W.graph.width e := by
        by_contra! zero
        exact (Finset.mem_compl.mp h) (Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr mark,Nat.eq_zero_of_le_zero zero⟩)
      exact Nat.le_of_dvd positive (divs e)
  have bounds := W.census_paid W.blankᶜ pos blk hub records wire hist grain cap hw hg good paid
  have total:=Finset.card_add_card_compl W.blank
  omega

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
