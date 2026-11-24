import OAI.Computability.VPVNP.CompressorShrinkResidentRun
import OAI.Computability.VPVNP.CompressorShrinkResidentHeaders
import OAI.Computability.VPVNP.CompressorShrinkResidentCosts

/-! # Resident directories in the memory after publication of all six heads -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkResidentRun

open BurstRAM Compression ShrinkResidentLayout ShrinkHistoryRows ShrinkResidentsPlan
open scoped Fin.CommRing Classical

variable {a g w : ℕ} (X : State a (packingLaneBits a g)) (first level : ℕ) (side : Bool)
local notation "L" => layout X first

private theorem fiber_bound (maps : Bool) (v) :
    (residents (ShrinkResidentDirectory.oldOrder X maps) (ShrinkResidentDirectory.place X maps side) v).length ≤ rowCapacity a maps := by
  let f := ShrinkResidentDirectory.place X maps side
  let e : {u // v=f u} ≃ {u // f u=v} := Equiv.subtypeEquivRight fun _ => eq_comm
  apply (Fintype.card_congr e).le.trans
  cases maps with
  | false => exact (hidden_count X side v).le
  | true => exact (map_count X side v).le

/-- Every public count and ordered-ID read used by a local handler falls
inside the resident data allocation, including when several fields share one owner. -/
theorem directory_addresses (maps : Bool) (fit : (L).endAddr < 2^w) :
    let p := outputBank (w:=w) X first maps
    (∀ v, let x := (p 3).val+((packedOrder X).entries.symm v).val
      first≤x ∧ x<(L).endAddr) ∧
    (∀ v (j : Fin (residents (ShrinkResidentDirectory.oldOrder X maps) (ShrinkResidentDirectory.place X maps side) v).length),
      let x := (p 5).val+((packedOrder X).entries.symm v).val*(p 4).val+j.val
      first≤x ∧ x<(L).endAddr) := by
  dsimp only
  let p := outputBank (w:=w) X first maps
  obtain ⟨_,_,_,hn,hc,hcap,hr⟩ := ShrinkResidentLayout.frame X first maps fit
  change (p 2).val=(L).sites at hn
  change (p 3).val=(L).counts maps at hc
  change (p 4).val=rowCapacity a maps at hcap
  change (p 5).val=(L).rows maps at hr
  obtain ⟨lo,own,cnt,upper⟩ := (L).ranges maps
  change first ≤ (L).owner maps at lo
  have fits (v) : ((packedOrder X).entries.symm v).val < (L).sites := ((packedOrder X).entries.symm v).isLt
  constructor
  · intro v
    let addr := (p 3).val + ((packedOrder X).entries.symm v).val
    have range : first≤addr ∧ addr<(L).endAddr := by dsimp only [addr]; rw [hc]; have := fits v; omega
    exact range
  · intro v j
    let row := ((packedOrder X).entries.symm v).val
    let addr := (p 5).val+row*(p 4).val+j.val
    have rowSize := Nat.mul_le_mul_right (rowCapacity a maps) (fits v)
    change (row+1)*rowCapacity a maps ≤ (L).sites*rowCapacity a maps at rowSize
    rw [Nat.succ_mul,← size_eq_rows X first maps] at rowSize
    have col := j.isLt.trans_le (fiber_bound X side maps v)
    have range : first≤addr ∧ addr<(L).endAddr := by dsimp only [addr]; rw [hr,hcap]; omega
    exact range

/-- Counts and ordered resident IDs depend only on the allocated data rectangle. -/
theorem transfer (maps : Bool) {m m' : Memory w}
    (dir : Directory (ShrinkResidentDirectory.oldOrder X maps) (packedOrder X)
      (ShrinkResidentDirectory.place X maps side) (outputBank X first maps) m)
    (fit : (L).endAddr < 2^w) (keep : ∀ x, first≤x → x<(L).endAddr → m' x=m x) :
    Directory (ShrinkResidentDirectory.oldOrder X maps) (packedOrder X)
      (ShrinkResidentDirectory.place X maps side) (outputBank X first maps) m' := by
  obtain ⟨counts,ids⟩ := directory_addresses X first side maps fit
  constructor
  · intro v
    rw [keep _ (counts v).1 (counts v).2]; exact dir.count v
  · intro v j
    rw [keep _ (ids v j).1 (ids v j).2]; exact dir.idAt v j

/-- Memory after both the hidden-field and party-map scans and the six writes publishing their
directory heads in the old level header. -/
def endMemory (m : Memory w) (h r : Passes w) :=
  after (r.final (h.final m)) (eventLog (List.ofFn (headerReport level L w)))

/-- Executing both owner and row scans, followed by the six fixed publishers,
produces the typed resident directories and the public pointers to read them. -/
theorem published_both (absolute roleHead : Word w) (m : Memory w)
    (space : Areas X first absolute roleHead) (dir : ShrinkResidentDirectory.Absolute X absolute m)
    (roles : DemandRAM.RoleColumns X side roleHead.val m) (headerRoom : level+36 ≤ 2^w)
    (apart : level+36≤first ∨ (L).endAddr≤level+30) :
    ∃ h r : Passes w, Built X first absolute roleHead side false m h ∧
      Built X first absolute roleHead side true (h.final m) r ∧
      (∀ i : Fin 6, endMemory X first level m h r (level+(30+i.val))=(headValues L i : Word w)) ∧
      (∀ maps : Bool, Directory (ShrinkResidentDirectory.oldOrder X maps) (packedOrder X)
        (ShrinkResidentDirectory.place X maps side) (outputBank X first maps) (endMemory X first level m h r)) ∧
      RAMBuckets.cost Report.probes (h.all++r.all++List.ofFn (headerReport level L w))=(L).charge := by
  obtain ⟨h,r,hb,rb,hidden,cost⟩ := both X first absolute roleHead side space m dir roles
  obtain ⟨heads,frame⟩ := published level L headerRoom (r.final (h.final m))
  refine ⟨h,r,hb,rb,heads,fun maps => transfer X first side maps (m:=r.final (h.final m)) ?_ space.fit ?_,?_⟩
  · cases maps
    · exact hidden
    · exact rb.directory
  · intro addr lo hi
    exact frame addr (apart.elim (fun h => .inr (h.trans lo)) (fun h => .inl (hi.trans_le h)))
  · rw [RAMBuckets.cost_append,cost]
    have hh : RAMBuckets.cost Report.probes (List.ofFn (headerReport level L w)) = 12 := rfl
    rw [hh]; rfl

end CompressorRecords.ShrinkResidentRun

end

end VPVNP
end Computability
end OAI
