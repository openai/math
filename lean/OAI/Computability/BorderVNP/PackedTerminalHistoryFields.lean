import OAI.Computability.BorderVNP.PackedTerminalHistoryRows
import OAI.Computability.BorderVNP.PackedTerminalRoutingFields
import OAI.Computability.BorderVNP.PackedInheritedWorkWords

/-! # Routing fields on the selected public profile of the enriched machine

The terminal geometry pass reads the verified history once. It appends the
finite cell-catalog lookup and the auxiliary-size pass on the same saved
word vector. Stable grouped exterior pointers are fixed by the original
bottom rows' rectangular offsets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicCapacity Shortening.PreparedBins
open BorderVNP.Epoch BorderVNP.Epoch.Round Packing VPVNP.VerifierNetwork TerminalCells Packing.Inherited.WorkWords
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {tiles pw start T w C b : ℕ} {shape : ℕ → Shape} {budget : ℕ → ℕ}
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {iw : ℕ → ℕ → ℕ}
    {deep : S.floor+1+S.drop*T ≤ start}

local notation "Bgood" => Boundary.Good (S:=S) (start:=start) (shape:=shape) (w:=w) (bits:=fun _ : Fin tiles => pw) budget
local notation "G" => Guess S start iw
local notation "W" => Boundary.Pins S start shape w T
variable (M : Machine deep (Boundary.Good (S:=S) (start:=start) (shape:=shape) (w:=w) (bits:=fun _ : Fin tiles => pw) budget) V iw) (leaf : Admissible (Boundary.Good (S:=S) (start:=start) (shape:=shape) (w:=w) (bits:=fun _ : Fin tiles => pw) budget) 0)
    {σ : Type} [Fintype σ] (bottom : Frame σ (Boundary.Pins S start shape w 0))
    (x : σ → Bool) (base : bottom.eval x = leaf.val.words)
local notation "leaves" => repeatLeaf (fan S) leaf T
local notation "tree" => repeatLeaf (fan S) bottom T
variable {τ : Type} [Fintype τ]
local notation "Γ" => τ ⊕ Boundary.Pins S start shape w T
local notation "routePins" => Frame.initial (Sum.inr : W → Γ)

include base in
/-- At every native accepted profile, this single fixed frame emits the true
pre-sewing physical fields on the history's own terminal layout. The two
side inputs describe the retained original names and the exact cumulative
staging widths in that same stored history. -/
theorem checked_fields (number : (Cube D → Deck (depth S start T+1)) ≃ Fin C)
    (vf : (shape T).sites ≤ 2^w) (cf : C ≤ 2^b) (width : pw < 2^w)
    (offset : Fin ((fan S)^T) → ℕ) (raw : τ → Bool) (aux : Frame Γ (Fin (shape T).sites × Fin w))
    (q : (M.system.histories T le_rfl leaves).Index) (g : Slot (fan S) G T → Bool)
    (selected : g = encode M.codec T le_rfl leaves q) :
    let s := (state (S:=M.system) T le_rfl leaves q).val
    let N := flattenPack T s.pack
    let y := Sum.elim raw (output M.steps T le_rfl tree x g)
    let F := TerminalCells.fields (Move:=allowedMoves (Cube D) S.budget) (q:=Fintype.card (Cube D))
      (d:=depth S start T) (E:=(shape T).edges) vf cf (groupRow (tiles:=tiles) offset) (fun _ => pw)
    let f := boundFrame (factorEnum D) number cf routePins aux
    (∀ z : Fin ((fan S)^T) × Fin tiles, offset z.1+z.2.val = (s.rows.site (N.layout.attach z)).val) →
    ∀ size : N.layout.Site → ℕ, Covers s.rows.site size aux y →
      flag M.steps T le_rfl tree x g = true ∧
      Packing.CellAddressPhysical.Represents N.layout (fun v => number (reduceMove (depth S start T) (s.route.origin v)))
        size s.rows.site s.rows.edge finProdFinEquiv.toEmbedding F (f.eval y) := by
  intro s N y F f host size covered
  have h := checked_routes M leaf bottom x base q g selected
  have eq : (routePins).eval y = output M.steps T le_rfl tree x g := by funext i; simp [y]
  refine ⟨h.1,route_represents (factorEnum D) number N s.route.flatten s.rows.flatten s.dummy
    finProdFinEquiv.toEmbedding vf cf (groupRow offset) (fun _ => pw)
    (fun z => (groupRow_pair offset z).trans (host z)) (fun _ => rfl) (fun _ => width) ?_
    routePins aux y (eq.symm ▸ h.2) size covered.live covered.hole⟩
  exact fun i hi => (hi ⟨finProdFinEquiv.symm i,finProdFinEquiv.apply_symm_apply i⟩).elim

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
