import OAI.Computability.BorderVNP.DiagonalExternalFreeCanonical
import OAI.Computability.BorderVNP.PackedRoutingPlaced
import OAI.Computability.BorderVNP.PackedCellWireView

/-! # Cell-local argument addresses for the delivered grouped free bank

The sparse geometry emitter gives each real grouped port its current
cell and supplied offset. The subsequent private placement pass keeps
these live rows. Therefore the fine box's ordinary cell-macro port
lookup reads precisely that receiver address for every private choice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Packing Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical
open Packing.RoutingOutputs RoutingISA RoutingISA.Transmission
open VPVNP.BurstRAM
open scoped Classical

variable {D R V g C m n : ℕ} (N : Network D (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C)
    (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)

/-- Actual live argument offsets in the compact per-cell supplied block. -/
def LivePlacement (lp : ℕ → ℕ × ℕ) : Prop := ∀ a : FreeBlock R V,
  let c := cell (N.attach a)
  lp (a.1.val*V+a.2.val) = (c.val,CellSlabs.start (suppliedRow N cell c edgeID portID)
    (suppliedWidth N cell c) (.inr ⟨a,rfl⟩))

variable {s d k w J : ℕ} (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    {σ : Type} [Fintype σ] (F : Fields s m n C d k w σ) {x : σ → Bool}

/-- The emitted live offsets and their physical owners still agree with the
same sewn network after the genuine private-placement pass. -/
theorem live_placement_of_image (net : Represents N cell aux siteID edgeID portID F x)
    (code : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (old : Fin J → N.Site) (head origin desc gap : ℕ) (before after : ℕ → ℕ)
    (image : Image F (siteID ∘ old) (portID ∘ finProdFinEquiv.symm) x origin before)
    (run : (privateLayout head origin m C J desc gap).Image before J after) :
    LivePlacement N cell edgeID portID (Directory.ISA.placement after (bases origin m C J).livePairs) := by
  let base := (bases origin m C J).livePairs
  let l := privateLayout head origin m C J desc gap
  have keep (addr : ℕ) (ha : base ≤ addr) : after addr = before addr := by
    apply run.outside
    · intro j hj
      dsimp only [base,bases] at ha
      dsimp only [privateLayout,bases]
      omega
    · right
      dsimp only [base,bases] at ha
      dsimp only [PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied,privateLayout,bases]
      omega
  intro a
  let z := a.1.val*V+a.2.val
  have hpos : (finProdFinEquiv a).val = z := by
    dsimp [z,finProdFinEquiv]
    ac_rfl
  have h := (image.placed N cell aux siteID edgeID portID F net code fit old finProdFinEquiv.symm origin before).2.2.2
    (finProdFinEquiv a)
  let result (p : FreeBlock R V) := ((cell (N.attach p)).val,CellSlabs.start
    (suppliedRow N cell (cell (N.attach p)) edgeID portID) (suppliedWidth N cell (cell (N.attach p)))
    (.inr ⟨p,rfl⟩))
  change Directory.ISA.placement before base (finProdFinEquiv a).val =
    result (finProdFinEquiv.symm (finProdFinEquiv a)) at h
  rw [Equiv.symm_apply_apply,hpos] at h
  refine Eq.trans ?_ h
  apply Prod.ext
  · exact keep _ (Nat.le_add_right ..)
  · exact keep _ (by change base ≤ base+z*2+1; omega)

variable {W : ℕ} (H : Fin (R+1) → TeamHistory W) (owner : ℕ → Fin (R+1)) (origin stride : ℕ)

/-- Full supplied vector at the physical RAM base of one receiving cell. -/
def nativeSupplied (c : Fin C) : Fin (suppliedSize N cell c) → Bool :=
  fun j => decide (((H (owner c.val)).history.val.2.2 (origin+c.val*stride+j.val)).val = 1)

private theorem port_start {P U : Type} [Fintype P] {sizes : P → ℕ} (N : Network D P sizes)
    (cell : N.Site → U) (c : U) (ei : N.Edge ↪ Fin m) (pi : P ↪ Fin n)
    (v : {v : N.Site // cell v = c}) (p : {p : P // N.attach p = v.val}) (j : Fin (sizes p.val))
    (f : Fintype (Supplied N cell c)) :
    (port N cell c ei pi v p j).val = @CellSlabs.start _ f (suppliedRow N cell c ei pi)
      (suppliedWidth N cell c) (.inr ⟨p.val,(congrArg cell p.property).trans v.property⟩)+j.val := by
  dsimp only [port,suppliedOrdinal,CellSlabs.ordinal,Equiv.ofBijective,Equiv.coe_fn_mk,CellSlabs.start]
  change _ + j.val = _ + j.val
  apply congrArg (· + j.val)
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro a _
  rfl

set_option maxHeartbeats 700000 in
/-- The cell's actual sparse argument lookup agrees with its grouped
receiver buffer for all internal choices, staged box values and lanes. -/
theorem cell_reads_received (lp : ℕ → ℕ × ℕ) (placement : LivePlacement N cell edgeID portID lp)
    (c : Fin C) (inside : Fin (guessedSize N cell c) → Bool) (stage : Fin (siteSize N cell c aux) → Bool)
    (v : {v : N.Site // cell v = c}) (p : {p : FreeBlock R V // N.attach p = v.val}) (j : Fin g) :
    CellSparse.lookup (bank N cell c aux inside stage (nativeSupplied N cell H owner origin stride c))
        (portBase N cell c edgeID portID aux v p+j.val) = receivedBank lp owner origin stride H p.val j := by
  have placed (a : FreeBlock R V) (c : Fin C) (hc : cell (N.attach a) = c) :
      lp (a.1.val*V+a.2.val) = (c.val,CellSlabs.start (suppliedRow N cell c edgeID portID)
        (suppliedWidth N cell c) (.inr ⟨a,hc⟩)) := by
    subst c
    exact placement a
  have hc := (congrArg cell p.property).trans v.property
  rw [port_at]
  unfold receivedBank receivedWord nativeSupplied
  rw [placed p.val c hc]
  have hv : (port N cell c edgeID portID v p j).val =
      CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) (.inr ⟨p.val,hc⟩)+j.val := by
    exact port_start N cell c edgeID portID v p j _
  let observe (a : ℕ) := decide (((H (owner c.val)).history.val.2.2 a).val = 1)
  apply congrArg observe
  rw [hv]
  simp only [Nat.add_assoc]

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
