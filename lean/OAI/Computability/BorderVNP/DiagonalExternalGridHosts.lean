import OAI.Computability.BorderVNP.ParseBatchWiredGrid
import OAI.Computability.BorderVNP.PackedGridExternal
import OAI.Computability.BorderVNP.DiagonalExternalFreeGroups

/-! # Bottom attachment hosts in the actual prewired processor grid

The public input is the processor-major prefix of the full slot envelope.
Its quotient by the grid block width selects the actual deck tile, and
its remainder selects the lane. Bottom copies share that tile but retain
separate lane slices. Different outer groups have separate copies of the tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.GridHosts

open Cover Crossing Packing Packing.DeckGrid TeamContraction ParseBatch.Prewire

/-- Total lookup of an ordinal in the actual tile order. Out-of-range addresses
select the first tile, including for a block with no occupied input slots. -/
def baseHost {S : Type} [Fintype S] [Nonempty S] (order : Fin (Fintype.card S) ≃ S)
    (i : ℕ) : S :=
  if h : i < Fintype.card S then order ⟨i,h⟩ else order ⟨0,Fintype.card_pos⟩

/-- An actual tile number is read directly from the given physical ordering. -/
theorem baseHost_val {S : Type} [Fintype S] [Nonempty S]
    (order : Fin (Fintype.card S) ≃ S) (i : Fin (Fintype.card S)) :
    baseHost order i.val = order i := by simp [baseHost]

variable {R r t pins link inner n : ℕ} {Edge : Type}
    (G : Wiring R r t pins link inner n Edge)

/-- The live processor rows fit inside the full paper slot envelope. -/
theorem publicRoom : r * publicWidth G ≤ r*n :=
  Nat.mul_le_mul_left r ((Nat.le_add_right (publicWidth G) inner).trans G.fits)

/-- The processor ordinals fit into the actual rounded number of tile words. -/
theorem gridRoom {V : ℕ} (hV : 0 < V) :
    r * publicWidth G ≤ V * blockWidth (r*n) V :=
  (publicRoom G).trans ((ceilDiv_le_iff_le_mul hV).mp le_rfl)

/-- The exact live-slot embedding of one processor array into the actual grid
words, including all the unused lanes at the end of the full slot envelope. -/
def wiredLane (V : ℕ) (hV : 0 < V) :
    (Fin r × Fin (publicWidth G)) ↪ (Σ _ : Fin V, Fin (blockWidth (r*n) V)) :=
  ((finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (publicRoom G))).trans
    (leafSlot hV (r*n))).trans (Equiv.sigmaEquivProd _ _).symm.toEmbedding

/-- The selected tile and lane are the Euclidean quotient and remainder of
the processor's ordinal, using the full envelope width. -/
theorem wiredLane_coordinates {V : ℕ} (hV : 0 < V) (p : Fin r × Fin (publicWidth G)) :
    let a := wiredLane G V hV p
    a.1.val = (finProdFinEquiv p).val / blockWidth (r*n) V ∧
      a.2.val = (finProdFinEquiv p).val % blockWidth (r*n) V := ⟨rfl,rfl⟩

variable {D : ℕ} (q depth : ℕ)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- The installed input port of the actual wired deck grid is at the tile
containing its live ordinal. -/
theorem wired_attach (p : Fin r × Fin (publicWidth G)) :
    (wiredGrid G q depth order position).attach p =
      baseHost order ((finProdFinEquiv p).val / blockWidth (r*n) (Fintype.card (Fin q → Deck (depth+2)))) :=
  (baseHost_val order (wiredLane G _ Fintype.card_pos p).1).symm

/-- The actual owner used when packing the input into one word per deck tile. -/
theorem wired_aligned (p : Fin r × Fin (publicWidth G)) :
    order (wiredLane G _ Fintype.card_pos p).1 = (wiredGrid G q depth order position).attach p := rfl

/-- Every bottom copy uses the same original tile for a processor ordinal. -/
theorem repeat_attach (copies : ℕ) (i : Fin copies) (p : Fin r × Fin (publicWidth G)) :
    ((wiredGrid G q depth order position).repeatGrid copies).attach (i,p) =
      baseHost order ((finProdFinEquiv p).val / blockWidth (r*n) (Fintype.card (Fin q → Deck (depth+2)))) :=
  wired_attach G q depth order position p

/-- Packing repeated inputs puts each real bit in the corresponding copy slice of its
original tile, exactly as in the forward external packing operation. -/
theorem repeat_lane (copies : ℕ) (i : Fin copies) (p : Fin r × Fin (publicWidth G)) :
    let V := Fintype.card (Fin q → Deck (depth+2))
    let g := blockWidth (r*n) V
    let a := Network.repeatLane (fun _ : Fin V => g) (wiredLane G V Fintype.card_pos) copies (i,p)
    order a.1 = ((wiredGrid G q depth order position).repeatGrid copies).attach (i,p) ∧
      a.2.val = i.val*g + (finProdFinEquiv p).val%g := by
  refine ⟨rfl,?_⟩
  let V := Fintype.card (Fin q → Deck (depth+2))
  change (finProdFinEquiv p).val % blockWidth (r*n) V + blockWidth (r*n) V * i.val =
    i.val * blockWidth (r*n) V + (finProdFinEquiv p).val % blockWidth (r*n) V
  ac_rfl

/-- Split a team into its outer pack and bottom copy in physical row-major order. -/
def teamBlocks (groups copies : ℕ) (h : groups*copies = R+1) :
    Fin (R+1) ≃ Fin groups × Fin copies :=
  (finCongr h.symm).trans finProdFinEquiv.symm

/-- The two public team coordinates are exactly the quotient and remainder. -/
theorem teamBlocks_coordinates (groups copies : ℕ) (h : groups*copies = R+1) (u : Fin (R+1)) :
    ((teamBlocks groups copies h u).1.val, (teamBlocks groups copies h u).2.val) =
      (u.val / copies,u.val % copies) := rfl

/-- In the initial parallel array the team-major index selects one outer grid.
Within that grid the bottom copy has the processor's physical block host. -/
theorem parallel_attach (groups copies : ℕ) (h : groups*copies = R+1)
    (u : Fin (R+1)) (p : Fin r × Fin (publicWidth G)) :
    let M := (wiredGrid G q depth order position).repeatGrid copies
    let z := teamBlocks groups copies h u
    (Network.parallel (fun _ : Fin groups => M)).attach (z.1,(z.2,p)) =
      ⟨z.1,baseHost (S := Fin q → Deck (depth+2)) order ((finProdFinEquiv p).val / blockWidth (r*n) (Fintype.card (Fin q → Deck (depth+2))))⟩ :=
  congrArg (Sigma.mk (teamBlocks groups copies h u).1) (repeat_attach G q depth order position copies _ p)

private def groupAddress (groups V W : ℕ) :
    Fin groups × (Σ _ : Fin V, Fin W) ≃ (Σ _ : Fin groups × Fin V, Fin W) where
  toFun a := ⟨(a.1,a.2.1),a.2.2⟩
  invFun a := (a.1.1,⟨a.1.2,a.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The real team, processor and bit input embedded in the public words of
the entire flat array of grouped bottom packs. -/
def groupedLane (V : ℕ) (hV : 0 < V) (groups copies : ℕ) (h : groups*copies = R+1) :
    PublicPort R r (G.program.length+t) link ↪
      (Σ _ : Fin groups × Fin V, Fin (copies * blockWidth (r*n) V)) :=
  let row := Fin r × Fin (publicWidth G)
  let lanes := Network.repeatLane (fun _ : Fin V => blockWidth (r*n) V) (wiredLane G V hV) copies
  ((((teamBlocks groups copies h).prodCongr (Equiv.refl row)).trans
    (Equiv.prodAssoc (Fin groups) (Fin copies) row)).toEmbedding.trans
    ((Function.Embedding.refl _).prodMap lanes)).trans (groupAddress groups V _).toEmbedding

/-- The physical grouped address records the outer team group, the true tile
ordinal and the bottom copy's slice followed by the original lane. -/
theorem groupedLane_coordinates {V : ℕ} (hV : 0 < V) (groups copies : ℕ)
    (h : groups*copies = R+1) (p : PublicPort R r (G.program.length+t) link) :
    let a := groupedLane G V hV groups copies h p
    let g := blockWidth (r*n) V
    a.1.1.val = p.1.val / copies ∧ a.1.2.val = (teamOrdinal p).val / g ∧
      a.2.val = p.1.val % copies * g + (teamOrdinal p).val % g := by
  refine ⟨rfl,rfl,?_⟩
  change (teamOrdinal p).val % blockWidth (r*n) V + blockWidth (r*n) V * (p.1.val % copies) =
    p.1.val % copies * blockWidth (r*n) V + (teamOrdinal p).val % blockWidth (r*n) V
  ac_rfl

/-- The actual parallel grouped networks attach the address of each real
public lane to its outer pack and its original deck tile. -/
theorem grouped_attach (groups copies : ℕ) (h : groups*copies = R+1)
    (p : PublicPort R r (G.program.length+t) link) :
    let V := Fintype.card (Fin q → Deck (depth+2))
    let N := (wiredGrid G q depth order position).groupedRepeat (fun _ : Fin V => blockWidth (r*n) V) order copies
    let a := groupedLane G V Fintype.card_pos groups copies h p
    (Network.parallel (fun _ : Fin groups => N)).attach a.1 =
      ⟨(teamBlocks groups copies h p.1).1,baseHost (S := Fin q → Deck (depth+2)) order
        ((teamOrdinal p).val / blockWidth (r*n) V)⟩ :=
  parallel_attach G q depth order position groups copies h p.1 p.2

end Diagonal.ExternalSew.GridHosts

end BorderVNP
end Computability
end OAI
