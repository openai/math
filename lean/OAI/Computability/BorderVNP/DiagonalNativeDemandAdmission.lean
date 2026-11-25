import OAI.Computability.BorderVNP.DiagonalHonestDeclarationBudget
import OAI.Computability.BorderVNP.PackedNativeDemandPacket
import OAI.Computability.BorderVNP.CubeLabelProducerVolumes

/-! # Every honest declaration of the signed seven-word packet is admitted -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical Diagonal Diagonal.CellEntries
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.GroupWeights TeamScales Filter
open scoped BigOperators Classical
open private list_get_sum from OAI.Computability.BorderVNP.CubeLabelProducerVolumes

open private read_write from OAI.Computability.BorderVNP.CubePhysicalDeclarationWords

private theorem allowed_of_canonical {n d blocks b h K s R X : ℕ} {Cell A : Type*} [Fintype A]
    (label : Cell → Label (n+1) d) (recv : A → Cell) (amount : A → ℕ)
    (sel : Packet n d blocks → Selector n K h)
    (ok : declarationCapacity R X blocks b K h
      (chosen b s sel,subtotals itemRow (crossCount b s sel) (chosen b s sel)) label recv amount) :
    broadcastAllowed R X blocks b K h label recv amount (broadcast b s sel) := by
  refine ⟨(RoutingISA.LocalRow.broadcast_passes_minimum b s sel).2,?_⟩
  let raw := broadcast b s sel
  have eqn : (Fin.ofNat (n+1) (readCode (n+1) raw.1),
      fun (pair : Sym2 (Fin d)) (j : Fin (n+1)) => readCode (declarationCap n d blocks b h s+1) (raw.2 pair j)) =
      (chosen b s sel,subtotals itemRow (crossCount b s sel) (chosen b s sel)) := by
    apply Prod.ext
    · apply Fin.ext
      simp only [raw,broadcast,read_write,Fin.ofNat,Fin.val_mk,Nat.mod_eq_of_lt (chosen b s sel).isLt]
    · funext pair j
      simp only [raw,broadcast,read_write]
  exact eqn.symm ▸ ok

/-- On the calibrated range, every selector on the physical mean-balanced
packet passes the independent public-capacity test. The rows, their
destinations and their widths come from the actual seven-word directory. -/
theorem eventually_packet_admission {F : Type} [Field F] (cube : FixedCube F)
    {α ξ : ℝ} (hα : 0 < α) (hξ : ξ < α/3) (hgap : 8*α*(cube.pred+1) < 1-ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ (r R d C : ℕ) {netDim ne np : ℕ}
      {P : Type} [Fintype P] {bits : P → ℕ} (N : Network netDim P bits)
      (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np)
      (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
      (gap : ℕ) (bounds : dir.DestinationBounds) {Team : Type} [Fintype Team] (teams : Fin (R+1) ≃ Team)
      (hd : 0 < d) (localMass : ℕ),
      let X := exterior ξ r k
      let list := rows N cell edge port dir old live gap
      let recv := receiver N cell edge port dir old live gap bounds
      let amount := fun j : Fin list.length => list[j.val].width
      ∀ budget : PackedLabelBudget N cell recv amount ((R+1)*X : ℕ) localMass (d^(cube.pred+1)),
      let placed := packet N cell edge port dir old live gap bounds cube teams hd budget
      1 ≤ r → (R+1 : ℝ) ≤ (k:ℝ)^(2*α) → d = alphabet α k →
      dir.teams=R+1 → dir.processors=r → dir.literal=literal α k → 0<dir.fields →
      dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2) →
      ∀ select : Packet cube.pred d placed.blocks → Selector cube.pred cube.copies cube.h,
      broadcastAllowed R X placed.blocks cube.b cube.copies cube.h placed.label recv amount
        (broadcast cube.b cube.width select) := by
  filter_upwards [cube.eventually_declarationCapacity hα hξ hgap] with k charge
  intro r R d C netDim ne np P _ bits N cell edge port dir old live gap bounds Team _ teams hd localMass X list recv
    amount budget placed hr hR groups dt dp dl fields tail select
  let index := chosen cube.b cube.width select
  let decl := (index,subtotals itemRow (crossCount cube.b cube.width select) index)
  apply allowed_of_canonical placed.label recv amount select
  have written := dir.populated_width (privatePair N cell edge port dir old live gap)
    (livePair N cell edge port dir old live gap) bounds.processors fields bounds.block tail
  change (list.map Directory.Row.width).sum ≤ dir.teams*((dir.fields+1)*(dir.processors*dir.literal)) at written
  rw [list_get_sum,dt,dp,dl] at written
  have f : dir.fields+1≤3 := by have hi := bounds.fields; omega
  have total : (∑ i, amount i) ≤ 3*(R+1)*r*literal α k := by
    exact written.trans ((Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ f)).trans_eq (by ring))
  have bal := (meanPackedLoads N cell recv amount (List.finRange C) (List.nodup_finRange _) (by ext; simp)
    cube.pred d hd budget).2
  have block : placed.blocks=blocksFor (X*(R+1) : ℕ) (cube.h*cube.b) (d^(cube.pred+1)) := by
    rw [Nat.mul_comm X]; rfl
  -- The arithmetic estimate uses just the symbol and cell dimensions.
  let dimensions : GroupWeights.Layout := ⟨0,0,d,cube.pred+1,0,0,0,0,C,0,0,0,0,0,0⟩
  apply charge r R dimensions placed.blocks (Fin list.length) decl select placed.label recv amount hr hR groups block
    ((passesLengths_iff cube.b cube.width select decl).2 rfl)
  · rw [Nat.mul_comm X]
    exact bal
  · exact total

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
