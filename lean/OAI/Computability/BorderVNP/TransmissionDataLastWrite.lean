import OAI.Computability.BorderVNP.TransmissionDataAddresses
import OAI.Computability.BorderVNP.TransmissionDataImage
import OAI.Computability.BorderVNP.TransmissionLastWriteLayout

/-! # Last writers of the actual placed data inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM Packing.Directory Function

variable {w : ℕ}

/-- On the receiver, a data row selects either a local copy or a physical read
from team A. A data row never writes its nominal A destination. -/
theorem Range.receivingData (r : Range w) (hw : 0 < w) (tag : r.kind = 1) :
    r.selected r.teamB = some (some (if r.teamA = r.teamB then .dataHere else .receiveB)) := by
  have one : (1 : Word w) ≠ 0 := fun h => by
    have v := congrArg Fin.val h
    simp only [Fin.val_one',Fin.val_zero,Nat.mod_eq_of_lt (Nat.one_lt_pow hw.ne' (by decide : 1 < 2))] at v
    omega
  by_cases here : r.teamA = r.teamB <;>
    simp [Range.selected,Range.bank,decision,Decision.role,tag,one,here,Ne.symm]

private theorem data_dest {r : Range w} {team : Word w} (hw : 0 < w) (tag : r.kind = 1)
    {mode : Role} (sel : r.selected team = some (some mode)) {reg : Reg}
    (dst : reg ∈ mode.destinations) : reg = 14 := by
  have one : (1 : Word w) ≠ 0 := fun h => by
    have v := congrArg Fin.val h
    simp only [Fin.val_one',Fin.val_zero,Nat.mod_eq_of_lt (Nat.one_lt_pow hw.ne' (by decide : 1 < 2))] at v
    omega
  simp (config := {decide := true}) only [Range.selected,decision,Decision.role,Range.bank,tag] at sel
  split_ifs at sel <;> cases sel <;> simp_all [Role.destinations]

/-- The four transfer columns that concern a data destination. These are read from
the scheduler image by `DataWriter.range_fields`; the source columns locate
the source team and its prepared data. -/
structure DataColumns (rows : ℕ → Range w) (d : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (owner : ℕ → ℕ) (origin stride : ℕ) : Prop where
  /-- All entries of the data prefix have tag one. -/
  kind : ∀ i : Fin (d.directory pp lp).length, (rows i).kind = 1
  /-- Destination team is the owner of the actual cell. -/
  team : ∀ i : Fin (d.directory pp lp).length, (rows i).teamB.val = owner (d.directory pp lp)[i.val].cell
  /-- Length of the exact populated delivery piece. -/
  width : ∀ i : Fin (d.directory pp lp).length, (rows i).width.val = (d.directory pp lp)[i.val].width
  /-- Receiver location is its physical bank base plus the within-cell slot. -/
  destination : ∀ i : Fin (d.directory pp lp).length,
    (rows i).dstB.val = origin+(d.directory pp lp)[i.val].cell*stride+(d.directory pp lp)[i.val].slot

/-- In the completed data-plus-shared directory, each bit of a genuine populated
data demand is the last writer of its assigned cell input. Compaction retains the
candidate, the two slicing schemes distinguish logical lanes, and the supplied-word
allocation gives distinct absolute addresses even for two ranges on the same team. -/
theorem data_lastWrite_disjoint {rows : ℕ → Range w} {d : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (place : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) (fits : origin+cells*stride ≤ 2^w) {owner : ℕ → ℕ}
    (cols : DataColumns rows d pp lp owner origin stride) (count : ℕ) (enough : (d.directory pp lp).length ≤ count)
    (i : Fin (d.directory pp lp).length) (j : Fin (d.directory pp lp)[i.val].width)
    (shared : ∀ k, (d.directory pp lp).length ≤ k → k < count → ∀ m,
      (rows k).selected (rows i).teamB = some (some m) → ∀ reg ∈ m.destinations,
        (origin+cells*stride ≤ ((rows k).bank (rows i).teamB reg).val ∨
         ((rows k).bank (rows i).teamB reg).val + (rows k).width.val ≤ origin) ∧
        ((rows k).bank (rows i).teamB reg).val + (rows k).width.val ≤ 2^w) :
    LastWrite rows (rows i).teamB count i.val
      (if (rows i).teamA = (rows i).teamB then .dataHere else .receiveB) j.val
      (d.deliveredAt pp lp origin stride ⟨i,j⟩) := by
  let team := (rows i).teamB
  let mode : Role := if (rows i).teamA = team then .dataHere else .receiveB
  let a := d.deliveredAt pp lp origin stride ⟨i,j⟩
  have addr (n : Fin (d.directory pp lp).length) (k : Fin (d.directory pp lp)[n.val].width) :
      d.deliveredAt pp lp origin stride ⟨n,k⟩ = (rows n).dstB.val+k.val :=
    congrArg (· + k.val) (cols.destination n).symm
  have input_lt (n : Fin (d.directory pp lp).length) (k : Fin (d.directory pp lp)[n.val].width) :
      (rows n).dstB.val+k.val < origin+cells*stride := addr n k ▸ place.deliveredAt_lt bound origin stride room ⟨n,k⟩
  have positive (n : Fin (d.directory pp lp).length) : 0 < (d.directory pp lp)[n.val].width := by
    have mem := List.getElem_mem n.isLt
    exact of_decide_eq_true (List.mem_filter.mp (show (d.directory pp lp)[n.val] ∈ d.directory pp lp from mem)).2
  have fit (n : Fin (d.directory pp lp).length) :
      (rows n).dstB.val+(rows n).width.val ≤ 2^w := by
    let k : Fin (d.directory pp lp)[n.val].width := ⟨_,Nat.sub_lt (positive n) (by decide : 0 < 1)⟩
    have h := (input_lt n k).trans_le fits
    dsimp [k] at h
    rw [cols.width]; omega
  have selected : (rows i).selected team = some (some mode) := (rows i).receivingData hw (cols.kind i)
  apply LastWrite.of_intervals (i.isLt.trans_le enough) (show j.val < (rows i).width.val by rw [cols.width]; exact j.isLt)
    selected 14 (by dsimp [mode]; split <;> decide) (addr i j)
  · intro e he; rw [data_dest hw (cols.kind i) selected he]; exact fit i
  · intro e he; exact Or.inl (congrArg (fun x => ((rows i).bank team x).val) (data_dest hw (cols.kind i) selected he))
  · intro n hin hn m hm reg hr
    by_cases raw : n < (d.directory pp lp).length
    · let p : Fin (d.directory pp lp).length := ⟨n,raw⟩
      have hreg : reg = 14 := data_dest hw (cols.kind p) hm hr
      subst reg
      refine ⟨fit p,?_⟩
      change a < (rows p).dstB.val ∨ (rows p).dstB.val+(rows p).width.val ≤ a
      by_contra! clash
      let k : Fin (d.directory pp lp)[p.val].width := ⟨a-(rows p).dstB.val,by rw [← cols.width p]; omega⟩
      have he : d.deliveredAt pp lp origin stride ⟨i,j⟩ = d.deliveredAt pp lp origin stride ⟨p,k⟩ := by
        rw [addr p k]; change a = (rows p).dstB.val+(a-(rows p).dstB.val); omega
      have same := congrArg (fun b : d.PopulatedBit pp lp => b.1.val) (place.deliveredAt_injective bound origin stride room he)
      exact (Nat.ne_of_lt hin) same
    · obtain ⟨start,cap⟩ := shared n (by omega) hn m hm reg hr
      refine ⟨cap,start.elim (fun lo => Or.inl ((place.deliveredAt_lt bound origin stride room ⟨i,j⟩).trans_le lo)) ?_⟩
      intro hi
      have lo : origin ≤ a := by
        change origin ≤ origin + _ + _ + _
        omega
      exact Or.inr (hi.trans lo)

/-- The data-first specialization places every later writable range above the data slabs. -/
theorem data_lastWrite {rows : ℕ → Range w} {d : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (place : BankPlacement d pp lp A cell id width) (bound : d.DestinationBounds)
    (origin stride : ℕ) (room : ∀ c, DataSlabs.size cell width c ≤ stride)
    (hw : 0 < w) (fits : origin+cells*stride ≤ 2^w) {owner : ℕ → ℕ}
    (cols : DataColumns rows d pp lp owner origin stride) (count : ℕ) (enough : (d.directory pp lp).length ≤ count)
    (i : Fin (d.directory pp lp).length) (j : Fin (d.directory pp lp)[i.val].width)
    (shared : ∀ k, (d.directory pp lp).length ≤ k → k < count → ∀ m,
      (rows k).selected (rows i).teamB = some (some m) → ∀ reg ∈ m.destinations,
        origin+cells*stride ≤ ((rows k).bank (rows i).teamB reg).val ∧
        ((rows k).bank (rows i).teamB reg).val + (rows k).width.val ≤ 2^w) :
    LastWrite rows (rows i).teamB count i.val
      (if (rows i).teamA = (rows i).teamB then .dataHere else .receiveB) j.val
      (d.deliveredAt pp lp origin stride ⟨i,j⟩) := by
  apply data_lastWrite_disjoint place bound origin stride room hw fits cols count enough i j
  intro k hk hc m hm r hr
  obtain ⟨lo,fit⟩ := shared k hk hc m hm r hr
  exact ⟨Or.inl lo,fit⟩

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
