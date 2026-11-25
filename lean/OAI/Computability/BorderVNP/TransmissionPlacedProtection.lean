import OAI.Computability.BorderVNP.TransmissionPlacedData
import OAI.Computability.BorderVNP.TransmissionSenderStable

/-! # Preservation of the source arrays below the cell and pair banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM Packing.Directory Function
open private data_dest from OAI.Computability.BorderVNP.TransmissionDataLastWrite

/-- Every reached store of a populated data row lies inside its cell allocation. -/
theorem data_destination_bounds {w : ℕ} {rows : ℕ → Range w} {d : Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) {owner : ℕ → ℕ} (cols : DataColumns rows d pp lp owner origin stride)
    (i : Fin (d.directory pp lp).length) (team : Word w) (mode : Role)
    (sel : (rows i).selected team = some (some mode)) (reg : Reg) (dest : reg ∈ mode.destinations) :
    origin ≤ ((rows i).bank team reg).val ∧
      ((rows i).bank team reg).val+(rows i).width.val ≤ origin+cells*stride := by
  obtain rfl := data_dest hw (cols.kind i) sel dest
  let r := (d.directory pp lp)[i.val]
  have positive : 0 < r.width := of_decide_eq_true (List.mem_filter.mp (List.getElem_mem i.isLt :
    r ∈ d.directory pp lp)).2
  let j : Fin r.width := ⟨r.width-1,by omega⟩
  have upper := placement.deliveredAt_lt bound origin stride room ⟨i,j⟩
  change origin+r.cell*stride+r.slot+j.val < origin+cells*stride at upper
  change origin ≤ (rows i).dstB.val ∧ (rows i).dstB.val+(rows i).width.val ≤ _
  rw [cols.destination,cols.width]
  change origin ≤ origin+r.cell*stride+r.slot ∧ origin+r.cell*stride+r.slot+r.width ≤ _
  dsimp only [j] at upper
  omega

/-- All native data and symbol-pair writes protect every processor or prepared pin
address below the first cell bank. The statement holds for any selected role on any
team, even when a later shared row is local to both endpoints. -/
theorem placed_protects_below_banks {w : ℕ} {rows : ℕ → Range w} {d : Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) {owner : ℕ → ℕ} (cols : DataColumns rows d pp lp owner origin stride)
    {g : Cube.SharedRows.Layout} (shared : g.LastWriteFields rows)
    (count : (d.directory pp lp).length = g.dataCount)
    (dataRoom : origin+cells*stride ≤ 2^w) (capacity : g.banks+g.stride*g.groups^2 ≤ 2^w)
    {k : ℕ} (reached : k < g.dataCount+g.groups.choose 2) (team : Word w)
    {a : ℕ} (low : a < min origin g.banks) : (rows k).protectsCell team a := by
  intro mode sel reg dest
  by_cases hd : k < (d.directory pp lp).length
  · obtain ⟨lo,hi⟩ := data_destination_bounds placement bound origin stride room hw cols ⟨k,hd⟩ team mode sel reg dest
    exact ⟨hi.trans (by omega),Or.inl ((lt_min_iff.mp low).1.trans_le lo)⟩
  · obtain ⟨lo,hi⟩ := shared_destination_bounds shared capacity k (by omega) reached team mode reg dest
    exact ⟨hi,Or.inl ((lt_min_iff.mp low).2.trans_le lo)⟩

/-- Data-first specialization of the protected prefix. -/
theorem placed_protects_below {w : ℕ} {rows : ℕ → Range w} {d : Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) {owner : ℕ → ℕ} (cols : DataColumns rows d pp lp owner origin stride)
    {g : Cube.SharedRows.Layout} (shared : g.LastWriteFields rows)
    (count : (d.directory pp lp).length = g.dataCount)
    (disjoint : origin+cells*stride ≤ g.banks) (capacity : g.banks+g.stride*g.groups^2 ≤ 2^w)
    {k : ℕ} (reached : k < g.dataCount+g.groups.choose 2) (team : Word w)
    {a : ℕ} (low : a < origin) : (rows k).protectsCell team a :=
  placed_protects_below_banks placement bound origin stride room hw cols shared count (by omega) capacity
    reached team (lt_min_iff.mpr ⟨low,by omega⟩)

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
