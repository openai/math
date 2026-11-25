import OAI.Computability.BorderVNP.PackedRoutingPrefix
import OAI.Computability.BorderVNP.PackedDirectoryOccupiedRun

/-! # Receiving offsets from the physical private-placement return

The private table stores the checked original cell owner and its prefix of earlier
descriptions. The live table stores the exact offset in the cell's supplied bank. The
same public bound therefore controls every meaningful operand of the native directory
pass, including when multiple old sites move to one cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA
open scoped Classical
open private prefix_le from OAI.Computability.BorderVNP.PackedRoutingPrefix

variable {D s m n C d k w J A : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable {σ : Type*} [Fintype σ]

set_option maxHeartbeats 1200000 in
/-- All native occupied slot words satisfy the actual cell-bank capacity. No bound
is imposed on values of unrelated RAM words outside these two arrays. -/
theorem Image.occupied_offsets (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : Fields s m n C d k w σ) {x : σ → Bool}
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (original : Fin J → N.Site) (live : Fin A → P)
    (head origin desc gap extent : ℕ) (before after : ℕ → ℕ)
    (h : Image F (siteID ∘ original) (portID ∘ live) x origin before)
    (run : (privateLayout head origin m C J desc gap).Image before J after)
    (cap : ∀ c, suppliedSize N cell c+gap+J*desc ≤ extent) :
    let b := bases origin m C J
    (∀ j < J, (Directory.ISA.placement after b.privatePairs j).2 ≤ extent) ∧
      ∀ a < A, (Directory.ISA.placement after b.livePairs a).2 ≤ extent := by
  intro b
  let q := privateLayout head origin m C J desc gap
  have facts := h.placed N cell aux siteID edgeID portID F net code fit original live origin before
  constructor
  · intro j hj
    let i : Fin J := ⟨j,hj⟩
    let c := cell (original i)
    have owner : q.owner before j = c.val := by
      simpa only [q,privateLayout,PrivatePlacement.Layout.owner,Directory.ISA.placement,Nat.mul_comm 2 j]
        using congrArg Prod.fst (facts.1 i)
    have counts := facts.2.1 c
    have sup : q.supplied = b.supplied := by dsimp [b,q,privateLayout,bases,PrivatePlacement.Layout.supplied]; omega
    have val := run.slots j hj
    change after (q.raw+2*j+1) = before (q.supplied+q.owner before j)+gap+
      PrivatePlacement.prefixCounts (q.owner before) desc j (q.owner before j) at val
    rw [owner,sup,counts] at val
    have earlier := (prefix_le (q.owner before) desc j c.val).trans (Nat.mul_le_mul_right desc hj.le)
    change after (q.raw+j*2+1) ≤ extent
    rw [Nat.mul_comm j 2,val]
    exact (Nat.add_le_add_left earlier _).trans (cap c)
  · intro a ha
    let i : Fin A := ⟨a,ha⟩
    let p := live i
    let c := cell (N.attach p)
    have beforeSlot := congrArg Prod.snd (facts.2.2.2 i)
    have same := run.outside (b.livePairs+a*2+1)
      (fun j hj => by dsimp [b,privateLayout,bases]; omega)
      (Or.inr (by dsimp [b,privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied]; omega))
    have bound := CellSlabs.end_le_capacity (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c)
      (Sum.inr ⟨p,rfl⟩)
    let port : Supplied N cell c := .inr ⟨p,rfl⟩
    let pos := CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) port
    have bound' : pos + suppliedWidth N cell c port ≤ suppliedSize N cell c := by
      unfold suppliedSize
      convert! bound using 1
      congr 2
      exact Subsingleton.elim _ _
    change after (b.livePairs+a*2+1) ≤ extent
    change before (b.livePairs+a*2+1) = pos at beforeSlot
    rw [same,beforeSlot]
    exact (Nat.le_add_right ..).trans (bound'.trans (by have := cap c; omega))

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
