import OAI.Hierarchy.ProtocolRAMCalendarCatalystArchive

namespace OAI
/-! # From every original dated negative cell to the actual used-reserve bank -/

namespace Hierarchy.ProtocolRAM.CatalystArchive
open Computability.VPVNP.BurstRAM PrivateRAM Calendar
open scoped BigOperators Classical
noncomputable section

variable {count payload w : ℕ} (c : Mesh) (issued : Attempt→Entry count payload)

/-- The dependent row rank accounts once for every original signed position. -/
theorem dated_total (charge : Event→ℕ)
    (read : ∀ t : Fin (events c).length,charge ((events c).get t)=∑j,(atTime c issued t).bits j) :
    ((events c).map charge).sum=∑ j,debit c issued j := by
  have list : (events c).map charge=List.ofFn (fun t : Fin (events c).length=>charge ((events c).get t)) :=
    (List.ofFn_getElem_eq_map (events c) charge).symm
  rw [list,List.sum_ofFn]
  simp only [read]
  rw [←(rank c issued).sum_comp (debit c issued),Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  let score := fun x : (Σ t,Fin (atTime c issued t).rows) => (atTime c issued x.1).bits x.2
  exact (congrArg score ((rank c issued).symm_apply_apply ⟨t,j⟩)).symm

/-- The physical scatter accounts for the same bits at every typed physical
owner, regardless of the ordering used to number the (column,axis) pairs. -/
theorem dated_total_used {G : Type*} [Fintype G] (charge : Event→ℕ) (keys : G≃Fin count)
    (a : ReserveUse.Archive) (b : RouteSettlement.Banks) (reserve : ℕ)
    (site : Fin (recordCount c issued)→Fin count) (m : Memory w)
    (mounted : ReserveUse.Mounted a b reserve site (debit c issued) m)
    (usedRoom : count≤b.used.size) (reserveRoom : count≤b.reserved.size)
    (bound : ∀ i,(∑j,if site j=i then debit c issued j else 0)≤reserve)
    (wide : reserve<2^w)
    (read : ∀ t : Fin (events c).length,charge ((events c).get t)=∑j,(atTime c issued t).bits j) :
    ((events c).map charge).sum=
      ∑ p,RouteSettlement.actual b.used (ReserveUse.output a b reserve site (debit c issued) m) (keys p).val := by
  rw [dated_total c issued charge read]
  have actual := sum_reported_debits a b reserve site (debit c issued) m mounted usedRoom reserveRoom bound wide
  exact actual.symm.trans (keys.sum_comp (fun i=>RouteSettlement.actual b.used
    (ReserveUse.output a b reserve site (debit c issued) m) i.val)).symm

theorem dated_native_used_le {G : Type*} (keys : G≃Fin count) (a : ReserveUse.Archive)
    (b : RouteSettlement.Banks) (reserve : ℕ) (site : Fin (recordCount c issued)→Fin count) (m : Memory w)
    (mounted : ReserveUse.Mounted a b reserve site (debit c issued) m)
    (usedRoom : count≤b.used.size) (reserveRoom : count≤b.reserved.size)
    (bound : ∀ i,(∑j,if site j=i then debit c issued j else 0)≤reserve) (wide : reserve<2^w) (p : G) :
    RouteSettlement.actual b.used (ReserveUse.output a b reserve site (debit c issued) m) (keys p).val≤reserve :=
  (ReserveUse.reported a b reserve site (debit c issued) m mounted (keys p) usedRoom reserveRoom
    (bound (keys p)) wide).1.le.trans (bound (keys p))

end
end Hierarchy.ProtocolRAM.CatalystArchive

end OAI
