import OAI.Computability.BorderVNP.PackedInheritedWorkCellRoom
import OAI.Computability.BorderVNP.PackedBankInheritedScalarCapacity

/-! # Address cost when final sewing carries the whole preceding extent -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening InheritedBank CellAddresses Finset
open scoped Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (prior payload amount : N.Site → ℕ)

/-- Sum a site's private charge over an arbitrary region using the exact singleton
decomposition of the physical records. -/
theorem region_amount_le (each : ∀ v, amount v ≤ localRecords N true prior payload (fun u => u=v))
    (test : N.Site → Prop) : testedWidth amount test ≤ localRecords N true prior payload test := by
  let sites := univ.filter test
  have eq : (fun v : N.Site => id v ∈ sites) = test := by
    funext v; apply propext; simp [sites]
  have raw := localRecords_near N true prior payload id sites
  rw [eq] at raw
  simp only [id_eq] at raw
  rw [raw,testedWidth,← sum_filter]
  exact sum_le_sum fun v _ => each v

variable (programs : Site.Programs N)

/-- The complete previous site extents at a cell fit its expanded budget. The private
payload and incident bits are disjoint charges in each singleton count. -/
theorem program_sizes_le (test : N.Site → Prop) :
    testedWidth (fun v => (programs v).program.size) test ≤
      localRecords N true programs.bankFields.prior programs.bankFields.payload test := by
  apply region_amount_le N _ _ _ _ test
  intro v
  have h := payload_incoming_le N programs.bankFields.prior programs.bankFields.payload v (fun u => u=v) rfl
  exact (Nat.add_le_add (Nat.le_add_right _ _) (programs v).size.le).trans h

variable {C : Type} (cell : N.Site → C) (c : C)

/-- The previous extent is staged before the newly sewn incidence area. Canonical
cables and external ports consume at most a second copy of the new region's wire budget. -/
theorem staged_sewn_le (old : N.Site → ℕ) :
    guessedSize N cell c + siteSize N cell c (fun v => old v+incoming N v) + suppliedSize N cell c ≤
      testedWidth old (fun v => cell v=c) + 2*localRecords N true prior payload (fun v => cell v=c) := by
  let test := fun v => cell v=c
  have h := region_amount_le N prior payload (incoming N) (fun v => wireCapacity_le N id v prior payload) test
  have canon := wireCapacity_le N cell c prior payload
  have add : siteSize N cell c (fun v => old v+incoming N v) =
      testedWidth old test + testedWidth (incoming N) test := by
    rw [siteSize_eq]
    unfold testedWidth
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    by_cases eq : cell v=c <;> simp [test,eq]
  rw [add]
  change guessedSize N cell c + (testedWidth old test + testedWidth (incoming N) test) + suppliedSize N cell c ≤
    testedWidth old test + 2*localRecords N true prior payload test
  change guessedSize N cell c + suppliedSize N cell c ≤ localRecords N true prior payload test at canon
  omega

/-- A live site's staging extent is contained in its owning cell's complete allocation. -/
theorem size_le_owner (amount : N.Site → ℕ) (v : N.Site) :
    amount v ≤ guessedSize N cell (cell v)+siteSize N cell (cell v) amount+suppliedSize N cell (cell v) := by
  have h : amount v ≤ siteSize N cell (cell v) amount :=
    Finset.single_le_sum (f := fun z : {u : N.Site // cell u = cell v} => amount z.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨v,rfl⟩)
  omega

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
