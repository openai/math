import OAI.Computability.BorderVNP.PackedRoutingPrefix
import OAI.Computability.BorderVNP.PackedCableMeans

/-! # Traffic of the native geometry, private-prefix, and demand-table stages

The private pass touches only its counters and slots. The directory pass then
publishes the exact positive rows. The sparse chooser on this memory therefore
uses the loads of the genuine crossed cables and grouped literal/pin deliveries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA VPVNP.BurstRAM
open BorderVNP.Cube Cube.LabelIndex Cube.Physical DiagonalResidueRAM ParseBatchSort
open scoped Classical

variable {D s m n C d k w J A : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ) {x : σ → Bool}

/-- Every cable word emitted by geometry survives the native private prefix pass. -/
theorem Image.cable_after_private {W : ℕ} (hk : k ≤ w) (wFit : w ≤ W) (old : Fin J → Fin s)
    (ports : Fin A → Fin n) (head origin desc gap : ℕ) (before : ℕ → ℕ) (mz : Memory W)
    (h : Image F old ports x origin before)
    (run : (privateLayout head origin m C J desc gap).Image before J (readings mz))
    (a : Fin (m*3)) : mz (origin+a.val) = word W (value fun j => (CableTriples.frame F hk le_rfl).eval x (a,j)) := by
  let u := finProdFinEquiv.symm a
  have ord : CableTriples.index u.1 u.2 = a := finProdFinEquiv.apply_symm_apply a
  have addr : a.val = u.1.val*3+u.2.val := (congrArg Fin.val ord).symm.trans (CableTriples.index_val ..)
  have preserve : readings mz (origin+a.val) = before (origin+a.val) := by
    apply run.outside
    · intro i hi
      dsimp [privateLayout,bases]
      have := a.isLt
      omega
    · left
      dsimp [privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied]
      have := a.isLt
      omega
  apply Fin.ext
  rw [word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0<2) wFit))]
  calc
    _ = before (origin+a.val) := preserve
    _ = CableTriples.get (CableTriples.row F x u.1) u.2 := by simpa only [addr,Nat.add_assoc] using h.cable u.1 u.2
    _ = _ := by rw [←ord,CableTriples.frame_value]

/-- The real prefix and demand writers preserve the cable array and produce precisely
the incoming rows at their actual physical cells. -/
theorem after_private_placement {W : ℕ} (l : LabelIndex.Layout) (N : Network D P bits)
    (cell : N.Site → Fin l.cells) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (edgeID : N.Edge ↪ Fin l.cableCount) (portID : P ↪ Fin n)
    (F : Fields s l.cableCount n l.cells d k w σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (hk : k ≤ w) (wFit : w ≤ W) (cells : 0 < l.cells)
    (dir : Directory.Layout) (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (width : ∀ k, bits (live k) = dir.block) (bound : dir.DestinationBounds)
    (head gap : ℕ) (before : ℕ → ℕ) (mz : Memory W) :
    let q := privateLayout head l.cables l.cableCount l.cells dir.entries dir.description gap
    let pairs := bases l.cables l.cableCount l.cells dir.entries
    let pp := Directory.ISA.placement (readings mz) q.raw
    let lp := Directory.ISA.placement (readings mz) pairs.livePairs
    let rows := dir.directory pp lp
    let mem := readings (Directory.ISA.publish mz head l.deliveries rows)
    Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x l.cables before →
    q.Image before dir.entries (readings mz) → q.Fits W before →
    rows.length = l.deliveryCount → head+9 < l.cables → head+9 < l.deliveries →
    (l.cables+l.cableCount*3 ≤ l.deliveries ∨ l.deliveries+7*l.deliveryCount ≤ l.cables) →
    (∀ i : Fin rows.length, ∀ a ∈ rows[i.val].words, a < 2^W) →
    ∃ recv : Fin rows.length → Fin l.cells, (∀ i, (recv i).val = rows[i.val].cell) ∧
      ∃ ep : Endpoints l mem, ∃ dataOrd : Fin rows.length ≃ Fin l.deliveryCount,
        MeanChoice.RowPlacement (networkRows N cell recv (fun i => rows[i.val].width)) (fromTables l mem ep)
          (Equiv.refl _) ((CableTriples.wireOrd N cell edgeID).sumMap dataOrd.toEmbedding) := by
  intro q pairs pp lp rows mem h run room count headC headD sep rawFit
  let place := h.networkPlacement N cell aux siteID edgeID portID F net code fit dir original live width
    head l.cables gap before (readings mz) run room
  have legal (key : dir.DestinationKey) : (dir.keyPlacement pp lp key).1 < l.cells := by
    have eq := congrArg Prod.fst (place.entry key)
    exact eq ▸ Fin.isLt _
  have cable := h.cable_after_private F hk wFit _ _ head l.cables dir.description gap before mz run
  obtain ⟨ep,chosen⟩ := CableTriples.published_placement N l cell aux siteID edgeID portID F hk le_rfl wFit
    net code cells mz head cable dir pp lp bound legal count headC headD sep rawFit
  exact ⟨_,fun _ => rfl,ep,finCongr count,chosen⟩

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
