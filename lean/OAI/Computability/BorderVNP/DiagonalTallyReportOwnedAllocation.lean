import OAI.Computability.BorderVNP.DiagonalTallyReportAllocatedWrites
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedReportFrame
import OAI.Computability.BorderVNP.CubePhysicalOwnedReportSlots

/-! # Realizing the report reservation bounds from the stable global bundle directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open DiagonalTallyAllocation RoutingISA Packing.BundleDirectory

variable {l : ReportLayout} {N C : ℕ} {Team : Type*} (cs : List (ReportCell l))
    (owner : Fin N → Fin C) (team : Fin C → Team) (t : Team)
    (cells : Fin cs.length ≃ {c : Fin C // team c=t})
    (source : Fin N → ReportBundle)
    (grouped : ∀ i : Fin cs.length, cs[i].bundles=(sourceRows owner (cells i).val.val).map source)

include cells grouped in
/-- The total number of visited bundles is the cardinality of the team's genuine
source rows. Each global source ordinal contributes at most one row. -/
theorem ownedBundleCount_le : (cs.map fun c => c.bundles.length).sum ≤ N := by
  let e := ownedBundleEquiv cs owner team t cells source grouped
  have cap := Fintype.card_le_of_injective (fun u : OwnedBundle cs => (e u).val)
    (Subtype.val_injective.comp e.injective)
  rw [← Fin.sum_univ_fun_getElem]
  simpa only [OwnedBundle,Fintype.card_sigma,Fintype.card_fin,Fin.getElem_fin] using cap

include cells grouped in
/-- Physical weighted-copy count across the owned rows is at most the total over
genuine global sources. This allows unequal clone multiplicities. -/
theorem teamWeighted_le_sources : teamWeighted cs ≤ ∑ r, (source r).useCount := by
  classical
  let e := ownedBundleEquiv cs owner team t cells source grouped
  have read (u : OwnedBundle cs) :
      cs[u.1].bundles[u.2].useCount=(source (e u).val).useCount :=
    congrArg ReportBundle.useCount (ownedBundleEquiv_read cs owner team t cells source grouped u)
  have eq : teamWeighted cs = ∑ u : OwnedBundle cs, (source (e u).val).useCount := by
    simp_rw [← read]
    rw [show (∑ u : OwnedBundle cs, cs[u.1].bundles[u.2].useCount) =
      ∑ i : Fin cs.length, ∑ j : Fin cs[i].bundles.length, cs[i].bundles[j].useCount from Fintype.sum_sigma _]
    simp_rw [show ∀ i : Fin cs.length, (∑ j : Fin cs[i].bundles.length, cs[i].bundles[j].useCount) =
      weightedCopies cs[i].bundles from fun i => Fin.sum_univ_fun_getElem ..]
    exact (Fin.sum_univ_fun_getElem cs (fun c => weightedCopies c.bundles)).symm
  rw [eq,e.sum_comp (fun u => (source u.val).useCount)]
  let selected := Finset.univ.filter (fun r => team (owner r)=t)
  calc
    _ = ∑ r ∈ selected, (source r).useCount := (Finset.sum_subtype selected
      (p := fun r => team (owner r)=t) (by simp [selected]) (fun r => (source r).useCount)).symm
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

/-- For the real source slots and a common clone multiplicity the global bound
is exactly the number of copies times the size of the one-copy marked-slot set. -/
theorem source_uses_eq_copies {Slots : Type*} [Fintype Slots] (row : Slots → Fin N) (copies : ℕ)
    (clone : ∀ r, (source r).header.copies=copies)
    (marks : ∀ r, Fin (source r).positions.length ≃ {v : Slots // row v=r}) :
    (∑ r, (source r).useCount)=copies*Fintype.card Slots := by
  classical
  have pos (r : Fin N) : (source r).positions.length=Fintype.card {v : Slots // row v=r} := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (marks r)
  have total := Fintype.card_congr (Equiv.sigmaFiberEquiv row)
  rw [Fintype.card_sigma] at total
  simp_rw [ReportBundle.useCount,clone,pos]
  rw [← Finset.sum_mul,total,Nat.mul_comm]

/-- A length-only stride can reserve one six-word zero row and nine words per
marked position for each original bundle of the individual global cell. -/
theorem supplementWords_le (bs : List ReportBundle) (W : ℕ) (marks : ∀ b∈bs,b.positions.length ≤ W) :
    supplementWords bs ≤ bs.length*(9*W+6) := by
  induction bs with
  | nil => simp [supplementWords]
  | cons b bs ih =>
    obtain ⟨here,tail⟩ := List.forall_mem_cons.mp marks
    have rest := ih tail
    unfold supplementWords at rest ⊢
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [Nat.succ_mul bs.length]
    omega

/-- Instantiate every report output reservation from the native owned-cell
numbering, stable original bundle rows and their true global volume bounds. -/
theorem ReportAllocation.of_sourceRows_le (pre : BeforeTasks) (post : AfterTasks) (banks : CellBanks.Layout)
    (frame control h H body zeroAddr : ℕ) (cs : List (ReportCell (reportLayout pre post frame control h H body zeroAddr)))
    {N C : ℕ} (owner : Fin N → Fin C) (team : Fin C → Team) (t : Team)
    (cells : Fin cs.length ≃ {c : Fin C // team c=t}) (source : Fin N → ReportBundle)
    (numbers : ∀ i, cs[i].number=(cells i).val.val)
    (grouped : ∀ i : Fin cs.length, cs[i].bundles=(sourceRows owner (cells i).val.val).map source)
    (physical : C ≤ banks.cells) (bankCells : banks.cells ≤ pre.bound.cells) (postCells : post.bound.cells=pre.bound.cells)
    (frameBefore : frame+96 ≤ banks.bankStart) (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (preBefore : pre.limit ≤ post.start)
    (receive : ∀ c∈cs, c.external=banks.bank c.number ∧ c.supplied+c.tailWidth ≤ banks.stride)
    (supp : ∀ v : Fin C, supplementWords ((sourceRows owner v.val).map source) ≤ pre.bound.supplementStride)
    (bundles : N ≤ post.bound.bundles) (marks : ∀ r, (source r).positions.length ≤ post.bound.marked)
    (copies : (∑ r, (source r).useCount) ≤ post.bound.uses) :
    ReportAllocation pre post banks (reportLayout pre post frame control h H body zeroAddr) cs post.reportCursor := by
  obtain ⟨ix,num⟩ := ownedIndex_of_equiv team t cells numbers
  let cast : Fin C ↪ Fin banks.cells := ⟨Fin.castLE physical,Fin.castLE_injective physical⟩
  refine ⟨bankCells,postCells,frameBefore,bankBefore,preBefore,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨ix.trans cast,num⟩,receive,?_,
    (ownedBundleCount_le cs owner team t cells source grouped).trans bundles,?_,
    (teamWeighted_le_sources cs owner team t cells source grouped).trans copies⟩
  · intro c hc
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
    exact (grouped ⟨i,hi⟩) ▸ supp (cells ⟨i,hi⟩).val
  · intro c hc b hb
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
    change b∈cs[(⟨i,hi⟩ : Fin cs.length)].bundles at hb
    rw [grouped,List.mem_map] at hb
    obtain ⟨r,_,rfl⟩ := hb
    exact marks r

/-- Specialization where the physical and padded cell counts coincide. -/
theorem ReportAllocation.of_sourceRows (pre : BeforeTasks) (post : AfterTasks) (banks : CellBanks.Layout)
    (frame control h H body zeroAddr : ℕ) (cs : List (ReportCell (reportLayout pre post frame control h H body zeroAddr)))
    {N C : ℕ} (cellLimit : C ≤ pre.bound.cells) (owner : Fin N → Fin C) (team : Fin C → Team) (t : Team)
    (cells : Fin cs.length ≃ {c : Fin C // team c=t}) (source : Fin N → ReportBundle)
    (numbers : ∀ i, cs[i].number=(cells i).val.val)
    (grouped : ∀ i : Fin cs.length, cs[i].bundles=(sourceRows owner (cells i).val.val).map source)
    (bankCells : banks.cells=pre.bound.cells) (postCells : post.bound.cells=pre.bound.cells)
    (frameBefore : frame+96 ≤ banks.bankStart) (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (preBefore : pre.limit ≤ post.start)
    (receive : ∀ c∈cs, c.external=banks.bank c.number ∧ c.supplied+c.tailWidth ≤ banks.stride)
    (supp : ∀ v : Fin C, supplementWords ((sourceRows owner v.val).map source) ≤ pre.bound.supplementStride)
    (bundles : N ≤ post.bound.bundles) (marks : ∀ r, (source r).positions.length ≤ post.bound.marked)
    (copies : (∑ r, (source r).useCount) ≤ post.bound.uses) :
    ReportAllocation pre post banks (reportLayout pre post frame control h H body zeroAddr) cs post.reportCursor :=
  ReportAllocation.of_sourceRows_le pre post banks frame control h H body zeroAddr cs owner team t cells source
    numbers grouped (bankCells ▸ cellLimit) bankCells.le postCells frameBefore bankBefore preBefore
    receive supp bundles marks copies

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
