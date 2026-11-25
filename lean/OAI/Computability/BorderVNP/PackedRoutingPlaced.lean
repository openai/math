import OAI.Computability.BorderVNP.PackedRoutingExport
import OAI.Computability.BorderVNP.PackedRoutingHeaders
import OAI.Computability.BorderVNP.PrivatePlacementNetwork

/-! # The native geometry arrays supply the true cell-bank placement

Old descriptions and grouped ports are resolved by their retained sparse IDs.
The separate private prefix pass then places each description after supplied
words, the reserved report gap, and the earlier descriptions for the same cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA
open private portKey from OAI.Computability.BorderVNP.PackedCellAddressPhysical
open scoped Classical

variable {D s m n C d k w J A : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ) {x : σ → Bool}
variable (net : Represents N cell aux siteID edgeID portID F x)
variable (code : ∀ c, (F.cells c).val = c.val)
variable (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)

include net code fit in
/-- The source directory of original sites is read at the current retained vertex.
The count row and the live placement are exact network-supplied positions. -/
theorem Image.placed (original : Fin J → N.Site) (live : Fin A → P) (origin : ℕ) (mem : ℕ → ℕ)
    (img : Image F (siteID ∘ original) (portID ∘ live) x origin mem) :
    (∀ j : Fin J, Directory.ISA.placement mem (bases origin m C J).privatePairs j =
      ((cell (original j)).val,0)) ∧
    (∀ c : Fin C, mem ((bases origin m C J).supplied+c.val) = suppliedSize N cell c) ∧
    (∀ c : Fin C, mem ((bases origin m C J).counters+c.val) = 0) ∧
    ∀ i : Fin A, let p := live i; let c := cell (N.attach p)
      Directory.ISA.placement mem (bases origin m C J).livePairs i =
        (c.val,CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) (.inr ⟨p,rfl⟩)) := by
  refine ⟨?_,?_,img.counterAt,?_⟩
  · intro j
    exact (img.privateAt j).trans (Prod.ext ((net.owner _).trans (code _)) rfl)
  · intro c
    exact (img.suppliedAt c).trans (SuppliedOffsets.cell_size N cell aux siteID edgeID portID F net fit c)
  · intro i
    exact (img.liveAt i).trans (Prod.ext ((portKey N cell aux siteID edgeID portID F net _).trans (code _))
      (SuppliedOffsets.port_base N cell aux siteID edgeID portID F net fit _))

/-- The layout the fixed private-prefix program reads for these arrays. -/
def privateLayout (head origin m C J desc gap : ℕ) : PrivatePlacement.Layout :=
  ⟨head,(bases origin m C J).privatePairs,J,desc,C,m,(bases origin m C J).ends,gap⟩

/-- Its six public operands and indirect tail capacity are the installed frame fields. -/
theorem privateFields {head origin m C J desc gap : ℕ} {mem : ℕ → ℕ} (h : Header head origin m C J mem)
    (entries : mem (head+66) = J) (width : mem (head+69) = desc) (tail : mem (mem (head+92)+8) = gap) :
    (privateLayout head origin m C J desc gap).Fields mem :=
  ⟨⟨h.privatePairs,entries,width⟩,⟨h.ends,h.cells,h.edges⟩,tail⟩

/-- The computed current owners, counts and live offsets are exactly the inputs of
the proved native bank allocation, in the true team-major grouped-port order. -/
noncomputable def Image.networkPlacement (dir : Directory.Layout) (original : Fin dir.entries → N.Site)
    (live : (Fin dir.teams × Fin dir.sites) ↪ P) (width : ∀ p, bits (live p) = dir.block)
    (head origin gap : ℕ) (before after : ℕ → ℕ)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin before) {W : ℕ}
    (run : (privateLayout head origin m C dir.entries dir.description gap).Image before dir.entries after)
    (room : (privateLayout head origin m C dir.entries dir.description gap).Fits W before) :=
  let b := bases origin m C dir.entries
  let l := privateLayout head origin m C dir.entries dir.description gap
  let facts := img.placed N cell aux siteID edgeID portID F net code fit original (live ∘ finProdFinEquiv.symm) origin before
  Directory.PrivateBank.networkPlacement N cell edgeID portID dir l before after run room rfl rfl (cell ∘ original)
    (fun i => by
      change before (b.privatePairs+2*i.val) = (cell (original i)).val
      simpa only [Directory.ISA.placement,Nat.mul_comm i.val 2] using congrArg Prod.fst (facts.1 i))
    live width
    (fun c => by simpa only [l,privateLayout,PrivatePlacement.Layout.supplied,bases,Nat.mul_comm 2 m] using facts.2.1 c)
    b.livePairs
    (by dsimp only [l,b,privateLayout,bases]; rw [Nat.mul_comm 2 dir.entries])
    (by dsimp only [l,b,privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied]
        rw [Nat.mul_comm 2 m]; omega)
    (fun a => by
      let result (p : P) := ( (cell (N.attach p)).val,CellSlabs.start
        (suppliedRow N cell (cell (N.attach p)) edgeID portID) (suppliedWidth N cell (cell (N.attach p)))
        (.inr ⟨p,rfl⟩))
      have hp := facts.2.2.2 (finProdFinEquiv a)
      change Directory.ISA.placement before b.livePairs (finProdFinEquiv a).val =
        result (live (finProdFinEquiv.symm (finProdFinEquiv a))) at hp
      rw [Equiv.symm_apply_apply] at hp
      change Directory.ISA.placement before b.livePairs (a.1.val*dir.sites+a.2.val) = result (live a)
      simpa only [finProdFinEquiv_apply_val,Nat.mul_comm dir.sites,Nat.add_comm a.2.val] using hp)


end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
