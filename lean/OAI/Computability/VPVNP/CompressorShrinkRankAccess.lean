import OAI.Computability.VPVNP.CompressorBundleGatherFootprint
import OAI.Computability.VPVNP.CompressorBundleRankFootprint
import OAI.Computability.VPVNP.CompressorShrinkSetupFootprint

/-! # Physical read and write regions for bundle gather and rank

The stored lists prove that every followed ID belongs to the old port range.
The rank scan's owner array is still readable after ranking, which identifies
each scanned key row before the rank was written.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkInput.Run

open BurstRAM PrimedStackRAM Compression Compression.PackingData BundleKeys BundleGather
open ShrinkRankSpace BundleLists PortRankRAM
open private table_legal from OAI.Computability.VPVNP.CompressorBundleTableReadback
open scoped Classical

variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w} {start : ℕ}
variable {m : Memory w} (r : Run X T start m)

local notation "Z" => plan X start
local notation "A" => Shape.A (plan X start)
local notation "B" => Shape.B (plan X start)
local notation "Q" => Shape.Q (plan X start)
local notation "sh" => placementBank X T start
local notation "q" => Shape.collectBank (plan X start) w
local notation "keyHead" => Fin.ofNat (2^w) (Shape.key (plan X start))
local notation "out" => Fin.ofNat (2^w) (Shape.gathered (plan X start))
local notation "dest" => Fin.ofNat (2^w) (Shape.ranks (plan X start))
local notation "K" => Shape.gatheredTable (plan X start) w T
local notation "R" => BundleGather.rankPublic q keyHead out dest
local notation "P" => X.packingData
local notation "O" => oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex
local notation "MS" => after r.greedy.post (eventLog r.sites)
local notation "ML" => after (after (after MS (eventLog r.clear)) (eventLog r.classify)) (eventLog r.append)
local notation "MG" => after ML (eventLog r.gather)

theorem gather_access (room : stop X start < 2^w) :
    LogAccess (fun z ↦ (Z).key ≤ z ∧ z < (Z).gathered)
      (fun z ↦ (Z).gathered ≤ z ∧ z < (Z).ranks) r.gather := by
  obtain ⟨h₁,h₂,_,h₄⟩ := range_bounds X start
  have fit := h₄.trans_lt room
  have val := (Z).values T sh Fintype.card_pos fit
  have scalar := (Z).scalarFits Fintype.card_pos fit
  obtain ⟨_,layout,_⟩ := (Z).regions T sh Fintype.card_pos ((r.greedy.old 5).trans (h₁.trans h₂)) fit
  have hn : B+B ≤ 2^w := by have := scalar.2.1; omega
  have stored : Stored P O sites q ML := by
    intro b
    exact r.ranking.ranked.lists.rows _ (show (bucketIndex sites b).val % (2^w) < (q 2).val by
      rw [Nat.mod_eq_of_lt ((bucketIndex sites b).isLt.trans_le hn),val.buckets,two_mul]
      exact (bucketIndex sites b).isLt)
  have count : Fixed.entryCount K = A := by
    change B*(2^(Shrink.colors a)*2^a/4+Q)=A
    rw [Nat.mul_add]; exact bundle_rows_total ..
  have legal := table_legal P O sites q keyHead out T.width (State.two_le_packingColors a)
    scalar.1.le hn layout ML stored
  have raw := Fixed.table_access K layout (count ▸ scalar.1) ML legal r.gather (count ▸ r.ranking.ranked.gather)
  have hs : Fixed.slots K = (Z).rectangleSize := by
    change (B+B)*(q 4).val = (2*B)*Q
    rw [val.stride,two_mul]
  have hg : (Z).ids+(Z).rectangleSize = (Z).gathered := rfl
  have hr : (Z).gathered+(Z).rectangleSize = (Z).ranks := rfl
  have hk : (Z).key+A ≤ (Z).ids := by
    change rankBase X start+A+A ≤ rankBase X start+2*A+2*B; omega
  have ids : (K).idsBase.val = (Z).ids := val.ids
  have keys : (K).keyBase.val = (Z).key := val.key
  have dst : (K).outputBase.val = (Z).gathered := val.gathered
  apply LogAccess.mono raw
  · intro z hz; rcases hz with ⟨lo,hi⟩ | ⟨lo,hi⟩
    · rw [ids] at lo hi; rw [hs,hg] at hi; exact ⟨by omega,hi⟩
    · change z < (K).keyBase.val+A at hi; rw [keys] at lo hi; exact ⟨lo,by omega⟩
  · intro z hz; rw [dst,hs,hr] at hz; exact hz

theorem rank_access (room : stop X start < 2^w) :
    LogAccess (fun z ↦ rankBase X start ≤ z ∧ z < (Z).ranks)
      (fun z ↦ (Z).ranks ≤ z ∧ z < widthBase X start) r.rank := by
  obtain ⟨h₁,h₂,_,h₄⟩ := range_bounds X start
  have fit := h₄.trans_lt room
  have val := (Z).values T sh Fintype.card_pos fit
  have hA := ((Z).scalarFits Fintype.card_pos fit).1
  have ownHead : (R 0).val = rankBase X start := val.owner
  have keyVal : (R 1).val = (Z).key := val.key
  have rowHead : (R 2).val = (Z).gathered := val.gathered
  have stride : (R 3).val = Q := val.stride
  have countHead : (R 4).val = (Z).counts := val.counts
  have rankHead : (R 5).val = (Z).ranks := val.ranks
  have keyNat : rankBase X start+A = (Z).key := rfl
  have countNat : rankBase X start+2*A = (Z).counts := rfl
  have idNat : (Z).counts+2*B = (Z).ids := rfl
  have gatheredNat : (Z).ids+(2*B)*Q = (Z).gathered := rfl
  have rankNat : (Z).gathered+(2*B)*Q = (Z).ranks := rfl
  have top : (Z).ranks+A < 2^w := fit
  have ownerBound (j : ℕ) (hj : j < A) : (owner R MG (Fin.ofNat _ j)).val < 2*B := by
    let x : Fin A := ⟨j,hj⟩
    let e := (O).symm x
    have he : (O e).val = j := congrArg Fin.val ((O).apply_symm_apply x)
    have stored := r.ranking.owners e
    change r.rankPost ((R 0).val+(O e).val) = _ at stored
    rw [he] at stored
    have low := r.ranking.ranked.rank.frame ((R 0).val+j) (.inl (by change _ < (R 5).val; omega))
    change r.rankPost ((R 0).val+j) = MG ((R 0).val+j) at low
    rw [PortRankRAM.owner,Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt (by omega),← low,stored]
    have hb : (bucketIndex sites (bucketOf P e)).val < B+B := (bucketIndex sites _).isLt
    exact (Nat.mod_le ..).trans_lt (by omega)
  have rd (j : ℕ) (hj : j < A) (v : Word w) (hv : v ∈ inputs R MG (Fin.ofNat _ j) Q) :
      rankBase X start ≤ v.val ∧ v.val < (Z).ranks := by
    let i := Fin.ofNat (2^w) j
    let u := owner R MG i
    have hu : u.val < 2*B := ownerBound j hj
    have hi : i.val = j := Nat.mod_eq_of_lt (hj.trans hA)
    change v ∈ [R 0+i,R 1+i,R 4+u] ++ (List.range Q).map (fun z ↦ PortRankRAM.start R MG i + Fin.ofNat _ z) at hv
    rcases List.mem_append.mp hv with h | h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl
      · rw [Fin.val_add,ownHead,hi,Nat.mod_eq_of_lt (by omega)]; exact ⟨by omega,by omega⟩
      · rw [Fin.val_add,keyVal,hi,Nat.mod_eq_of_lt (by omega)]; exact ⟨by omega,by omega⟩
      · rw [Fin.val_add,countHead,Nat.mod_eq_of_lt (by omega)]; exact ⟨by omega,by omega⟩
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
      have hz' := List.mem_range.mp hz
      have hh := Nat.mul_le_mul_right Q hu
      rw [Nat.succ_mul] at hh
      have addr : (PortRankRAM.start R MG i+Fin.ofNat _ z).val = (Z).gathered+u.val*Q+z := by
        change (R 2+u*R 3+Fin.ofNat _ z).val = _
        rw [Fin.val_add,Fin.val_add,Fin.val_mul,Fin.val_ofNat,rowHead,stride,
          Nat.mod_eq_of_lt (by omega : u.val*Q < 2^w),
          Nat.mod_eq_of_lt (by omega : (Z).gathered+u.val*Q < 2^w),
          Nat.mod_eq_of_lt (by omega : z < 2^w),Nat.mod_eq_of_lt (by omega)]
      rw [addr]; exact ⟨by omega,by omega⟩
  have reg : Regions R MG Q A := ⟨by rw [rankHead]; exact top.le,
    fun j hj x hx ↦ .inl (by rw [rankHead]; exact (rd j hj x hx).2)⟩
  exact scan_access R MG Q A reg _ _ rd (fun j hj ↦ by rw [rankHead]; exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩)
    r.rank r.ranking.ranked.rank.executed

end CompressorRecords.ShrinkInput.Run

end VPVNP
end Computability
end OAI
