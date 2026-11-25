import OAI.Computability.BorderVNP.PackedBankMergedLoad
import OAI.Computability.BorderVNP.PackedBankInheritedDenseCharges
import OAI.Computability.BorderVNP.ShortenEpochRoundRecords

/-! # Source record caps for the computed permanent work and extent words

The individual extent contains the work and one physical incidence area.
The merged cell additionally contains its canonical private and exterior
wires. Both fit the actual selected tile cap by fixed constants.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Epoch Epoch.Round Cover PackedHistoryCircuit.Normalized CellAddresses InheritedBank
open private site_load_le from OAI.Computability.BorderVNP.PackedBankMergedLoad
open private localRecords_mono from OAI.Computability.BorderVNP.ShortenEpochRoundRecords
open scoped Classical

variable {D : ℕ} {P : Type} {T : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (state : N.Site → Site) (owner : N.Site → T) (bound : ℕ)

/-- The physical expanded-record budget pays for each work prefix and each
incidence bit at its owning tile. -/
theorem size_le_cap (hin : ∀ v, (state v).incoming = incoming N v)
    (cap : ∀ t, localRecords N true (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad)
      (fun v => owner v = t) ≤ bound) (v : N.Site) : (state v).size ≤ 2*bound := by
  let one := localRecords N true (fun u => (state u).staticNodes) (fun u => (state u).expandedLoad) (fun u => u=v)
  have h1 : (state v).work ≤ one := (Nat.le_add_right _ _).trans (site_load_le N state v).2
  have h2 : (state v).incoming ≤ one := (hin v).le.trans
    (wireCapacity_le N id v (fun u => (state u).staticNodes) (fun u => (state u).expandedLoad))
  have hb : one ≤ bound := (localRecords_mono N true _ _ (fun u hu => congrArg owner (show u = v from hu))).trans
    (cap (owner v))
  exact (Nat.add_le_add (h1.trans hb) (h2.trans hb)).trans_eq (two_mul bound).symm

/-- The real merged cell directory with exactly the computed widths fits the
word addressing budget whenever three times the owning record cap fits. -/
theorem cell_room {C : Type} (cell : N.Site → C) (hin : ∀ v, (state v).incoming = incoming N v)
    (cap : ∀ c, localRecords N true (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad)
      (fun v => cell v = c) ≤ bound) {w : ℕ} (fit : 3*bound < 2^w) (c : C) :
    guessedSize N cell c + siteSize N cell c (fun v => (state v).size) + suppliedSize N cell c < 2^w :=
  (merged_bank_capacity N state cell c hin).trans_lt ((Nat.mul_le_mul_left 3 (cap c)).trans_lt fit)

variable {K : Type*} {I : Type} [Fintype I] {lev w : ℕ} (p : PlacedPack D P bits K I lev)

/-- A true cumulative cap on the selected placed pack supplies the exact
word-fit hypothesis of the work circuit. -/
theorem size_lt_of_within (site : p.pack.layout.Site → Site)
    (hin : ∀ v, (site v).incoming = incoming p.pack.layout v)
    (h : RecordsWithin p ⟨fun v => (site v).staticNodes,fun v => (site v).expandedLoad⟩ true bound)
    (room : 2*bound < 2^w) (v : p.pack.layout.Site) : (site v).size < 2^w := by
  apply (size_le_cap p.pack.layout site (fun v => productAddress lev (p.site v)) bound hin _ v).trans_lt room
  intro t
  exact (Nat.le_add_left _ 1).trans (h t)

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
