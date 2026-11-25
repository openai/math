import OAI.Computability.BorderVNP.PackedBottomGridSite
import OAI.Computability.BorderVNP.CellSourceTableBounds

/-! # Uniform table bounds for the actual initial routed grid site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse

/-- Bound every stored factor in every actual one-copy site table. -/
def Site.TableBound (s : Site) (M : ℕ) : Prop := ∀ fs ∈ s.boxes, ∀ f ∈ fs, f.TableBound M

/-- Larger table bounds cover the same factor, without changing any of its rows or keys. -/
theorem factor_mono {f : Factor} {M T : ℕ} (h : f.TableBound M) (le : M ≤ T) : f.TableBound T := by
  cases f <;> simp only [Factor.TableBound] at * <;> first | trivial | exact ⟨h.1.trans le,h.2.trans le⟩

/-- Staging a site's old inputs adds only equality records and retains its one-copy tables. -/
theorem Site.TableBound.retain {s : Site} {M : ℕ} (h : s.TableBound M) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).TableBound M := h

end Packing.Inherited

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical

private theorem compare_bound (a b : ℕ) : (compareUse a b).TableBound 8 := by simp [compareUse,Factor.TableBound]
private theorem zero_bound (a : ℕ) : (GridPadding.zeroFactor a).TableBound 8 := by simp [GridPadding.zeroFactor,Factor.TableBound]

private theorem stage_bound (rows : List Factor) (n : ℕ) (h : ∀ f ∈ rows, f.TableBound 8) :
    ∀ f ∈ stage n rows, f.TableBound 8 := by
  induction rows generalizing n with
  | nil => simp [stage]
  | cons f fs ih =>
    obtain ⟨hf,ht⟩ := List.forall_mem_cons.mp h
    cases f <;> simp only [stage,List.forall_mem_cons]
    all_goals exact ⟨by first | exact hf | apply compare_bound,ih _ ht⟩

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val)

/-- Every factor in the actual repeated bottom-site box has at most eight rows and
key entries. This includes the source gates, both staged inputs of each weighted
unary, every padded incidence word and every unused report word. -/
theorem born_tableBound (copies capFine capReport : ℕ) (degree : ∀ u, Fintype.card (CellBox.Lane N u) ≤ 3) :
    (born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
      copies capFine capReport).TableBound 8 := by
  change ∀ fs ∈ [stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules capFine capReport], ∀ f ∈ fs, Factor.TableBound f 8
  rw [List.forall_mem_singleton]
  simp only [stored,wiring,List.forall_mem_append]
  refine ⟨⟨stage_bound _ _ ?_,⟨⟨?_,?_⟩,?_⟩⟩,?_⟩
  · intro f hf
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hf
    cases rule : rules u with
    | truth table =>
      simp only [ruleFactor,Factor.TableBound,boolRows,List.length_ofFn]
      exact ⟨(degree u.val).trans (by decide),Nat.pow_le_pow_right (by decide) (degree u.val)⟩
    | unary => trivial
  · intro f hf
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
    exact compare_bound _ _
  · intro f hf
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
    exact zero_bound _
  · intro f hf
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
    exact zero_bound _
  · intro f hf
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
    exact zero_bound _

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
