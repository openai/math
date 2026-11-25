import OAI.Hierarchy.ProtocolRAMDateSpillPrefixOrder
import OAI.Hierarchy.ProtocolRAMCatalogueMount

namespace OAI
/-! # Exact paid destination prefixes of an original spill path -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open AdaptiveProbe ProbeStage ProbeStage.CoreBoard ProbeStage.CoreBoard.HistoryRoles
open WireTelescope NamedAperture Tagged.PassiveWindow Computability.VPVNP.BurstRAM PrivateRAM
open LinearAlgebra.SpectralBooks ChordGraph
open scoped BigOperators Classical
variable {h W k attempts axes native : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marks : ReportSockets.Marks h W k attempts) (b : CatalogueRows.Board) (order : Fin b.coreRows ≃ Edges S h (2^W) k)
    (sized : attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    (axis : Catalysts h W k≃Fin axes) (m : Memory native)
local notation "d" => 2^W
local notation "N" => Stages h d
local notation "G" => Goods h W k
local notation "Cat" => Catalogue S π depth marks
local notation "names" => timeRows S π depth marks b order sized axis
local notation "sites" => siteLast h d k+1
local notation "ord" => b.ordinal S π depth marks order sized
local notation "B" => b.coreMount π (siteNumber h d k) order m

theorem core_only (spill : G→ℕ) (f : Fin b.rows) (positive : 0<routeLoad (B).ordinary spill f) :
    ∃e : Edges S h d k,(B).row e=f := by
  by_contra none
  have absent (i : G) : f∉(B).ordinary i:=by
    intro hit
    obtain ⟨e,_,eq⟩:=List.mem_map.mp hit
    exact none ⟨e,eq⟩
  have zero : routeLoad (B).ordinary spill f=0:=by
    exact Finset.sum_eq_zero (fun i _=>by simp [List.count_eq_zero.mpr (absent i)])
  omega

private theorem core_chord (pad : Chord sites) (e : Edges S h d k) :
    filledChord (B).actual pad ((B).row e)=sorted S π depth marks (.inl (.inl e)) := by
  have distinct:=actual_distinct S π depth marks (.inl e)
  have diff : ((siteNumber h d k) (ends π e).1)≠(siteNumber h d k) (ends π e).2 :=
    (siteNumber h d k).injective.ne distinct
  unfold filledChord
  simp only [(B).tail,(B).head,graph]
  rw [dite_eq_right diff]; rfl

/-- Only genuine original core records can receive this dated spill. Its physical
recipient's exact ordered prefix agrees with the signed sparse board, even when
several positive chronological rows connect the same two sites. -/
theorem new_prefix_on_paid (pad : Chord sites) (spill : G→ℕ) (c : Cat)
    (positive : 0<routeLoad (B).ordinary spill (ord c)) :
    let mass:=routeLoad (B).ordinary spill
    prefixAt (sorted S π depth marks ∘ names)
      ((Sum.elim (fun u:Cat=>mass (ord u)) (fun _:G⊕Catalysts h W k=>0)) ∘ names) ((names).symm (.inl c))=
      prefixAt (filledChord (B).actual pad) mass (ord c) := by
  intro mass
  let out:=filledChord (B).actual pad
  let input:=sorted S π depth marks
  let read (e : Fin b.rows):=if e.val<(ord c).val ∧ out e=out (ord c) then mass e else 0
  let amount:Source S π depth marks→ℕ:=Sum.elim (fun u:Cat=>mass (ord u)) (fun _=>0)
  let record (a : Source S π depth marks):=if ((names).symm a).val<((names).symm (.inl c)).val ∧
      input a=input (.inl c) then amount a else 0
  have hits (u:Cat) (on : 0< mass (ord u)) : out (ord u)=input (.inl u) := by
    obtain ⟨e,eq⟩:=core_only S π b order m spill (ord u) on
    have same : Sum.inl e=u:=(ord).injective eq
    rw [←same]
    exact core_chord S π depth marks b order m pad e
  have head:=hits c positive
  have used (u : Cat) : record (.inl u)=read (ord u) := by
    by_cases on : 0< mass (ord u)
    · have target:=hits u on
      have seq : ((names).symm (.inl u)).val<((names).symm (.inl c)).val ↔ (ord u).val<(ord c).val:=by
        simpa only [Equiv.apply_symm_apply, key_paid] using
          (time_before S π depth marks b order sized axis ((names).symm (.inl u)) ((names).symm (.inl c)))
      simp only [record,amount,Sum.elim_inl,read,target,head,seq]
    · simp [record,read,amount,Nat.eq_zero_of_not_pos on]
  simp only [prefixAt,original_prefix]
  calc
    _ = ∑j,record (names j) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [record,amount,input,key]
    _ = ∑a,record a := (names).sum_comp record
    _ = ∑u : Cat,read (ord u) := by
      rw [Fintype.sum_sum_type]
      have vacant (t : G⊕Catalysts h W k) : record (.inr t)=0:=by simp [record,amount]
      simp only [used,vacant,Finset.sum_const_zero,Nat.add_zero]
    _ = ∑e∈Finset.univ.map ord,read e := (Finset.sum_map ..).symm
    _ = ∑e:Fin b.rows,read e := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro e _ miss
      have zero : mass e=0:=by
        by_contra hz
        obtain ⟨j,eq⟩:=core_only S π b order m spill e (Nat.pos_of_ne_zero hz)
        exact miss (Finset.mem_map.mpr ⟨.inl j,Finset.mem_univ _,eq⟩)
      simp [read,zero]
    _ = _ := by simp [read,out,key]

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
end

end OAI
