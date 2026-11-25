import OAI.Computability.BorderVNP.TransmissionDataMaterialized
import OAI.Computability.BorderVNP.TransmissionSharedLastWrite
import OAI.Computability.BorderVNP.PrivatePlacementNetwork

/-! # Last writers across the combined data and shared symbol-pair layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM Packing.Directory Function
open private index_covered destination_key ordered_span from OAI.Computability.BorderVNP.TransmissionSharedLastWrite

/-- Every selected shared destination lies in the fitted symbol-pair arena. This is
derived from the two real ordered endpoints of every emitted strict symbol pair. -/
theorem shared_destination_span {w : ℕ} {g : Cube.SharedRows.Layout} {rows : ℕ → Range w}
    (shared : g.LastWriteFields rows)
    (k : ℕ) (after : g.dataCount ≤ k) (doneAt : k < g.dataCount+g.groups.choose 2)
    (team : Word w) (mode : Role) (reg : Reg) (dest : reg ∈ mode.destinations) :
    g.banks ≤ ((rows k).bank team reg).val ∧
      ((rows k).bank team reg).val+(rows k).width.val ≤ g.banks+g.stride*g.groups^2 := by
  obtain ⟨t,ht,s,hs,rfl⟩ := index_covered g after doneAt
  obtain ⟨v,hv,base,_⟩ := destination_key shared team hs ht dest
  rw [base]
  have hi := ordered_span (l := g) hv
  have wid := shared.width t ht s hs
  omega

/-- Each fitted pair bank supplies a fitted word interval for an actual shared role. -/
theorem shared_destination_bounds {w : ℕ} {g : Cube.SharedRows.Layout} {rows : ℕ → Range w}
    (shared : g.LastWriteFields rows) (room : g.banks+g.stride*g.groups^2 ≤ 2^w)
    (k : ℕ) (after : g.dataCount ≤ k) (doneAt : k < g.dataCount+g.groups.choose 2)
    (team : Word w) (mode : Role) (reg : Reg) (dest : reg ∈ mode.destinations) :
    g.banks ≤ ((rows k).bank team reg).val ∧
      ((rows k).bank team reg).val+(rows k).width.val ≤ 2^w := by
  obtain ⟨lo,hi⟩ := shared_destination_span shared k after doneAt team mode reg dest
  exact ⟨lo,hi.trans room⟩

/-- With the packed-cell and pair arenas disjoint, every actual populated data bit is
the final physical store at its assigned consumer slot. Both writer images may be
obtained from the native programs via `DataColumns.of_writers` and
`Cube.SharedRows.Layout.LastWriteFields.of_scheduled`. -/
theorem placed_data_lastWrite_disjoint {w : ℕ} {rows : ℕ → Range w} {d : Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) {owner : ℕ → ℕ} (cols : DataColumns rows d pp lp owner origin stride)
    {g : Cube.SharedRows.Layout} (shared : g.LastWriteFields rows)
    (count : (d.directory pp lp).length = g.dataCount)
    (disjoint : origin+cells*stride ≤ g.banks ∨ g.banks+g.stride*g.groups^2 ≤ origin)
    (dataRoom : origin+cells*stride ≤ 2^w) (capacity : g.banks+g.stride*g.groups^2 ≤ 2^w)
    (i : Fin (d.directory pp lp).length) (j : Fin (d.directory pp lp)[i.val].width) :
    LastWrite rows (rows i).teamB (g.dataCount+g.groups.choose 2) i.val
      (if (rows i).teamA = (rows i).teamB then .dataHere else .receiveB) j.val
      (d.deliveredAt pp lp origin stride ⟨i,j⟩) := by
  apply data_lastWrite_disjoint placement bound origin stride room hw dataRoom cols _ (by omega)
  intro k hk hke mode _ reg hreg
  obtain ⟨lo,hi⟩ := shared_destination_span shared k (by rwa [← count]) hke (rows i).teamB mode reg hreg
  exact ⟨disjoint.elim (fun h => Or.inl (h.trans lo)) (fun h => Or.inr (hi.trans h)),hi.trans capacity⟩

/-- Data-first specialization of the two-order last-writer result. -/
theorem placed_data_lastWrite {w : ℕ} {rows : ℕ → Range w} {d : Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (placement : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) {owner : ℕ → ℕ} (cols : DataColumns rows d pp lp owner origin stride)
    {g : Cube.SharedRows.Layout} (shared : g.LastWriteFields rows)
    (count : (d.directory pp lp).length = g.dataCount)
    (disjoint : origin+cells*stride ≤ g.banks) (capacity : g.banks+g.stride*g.groups^2 ≤ 2^w)
    (i : Fin (d.directory pp lp).length) (j : Fin (d.directory pp lp)[i.val].width) :
    LastWrite rows (rows i).teamB (g.dataCount+g.groups.choose 2) i.val
      (if (rows i).teamA = (rows i).teamB then .dataHere else .receiveB) j.val
      (d.deliveredAt pp lp origin stride ⟨i,j⟩) :=
  placed_data_lastWrite_disjoint placement bound origin stride room hw cols shared count (Or.inl disjoint)
    (by omega) capacity i j

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
