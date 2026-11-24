import OAI.Computability.VPVNP.CompressorRecordsShrinkInput
import OAI.Computability.VPVNP.CompressorLogAccess
import OAI.Computability.VPVNP.CompressorSlotFillFootprint
import OAI.Computability.VPVNP.CompressorSlotScanFootprint

/-! # Addresses accessed while preparing a shrinking state's bundle lists

The preliminary placement and classification read their old input columns.
Their writes, as well as all counter clears and bounded appends, lie in the
new shrinking arena. This permits each native segment to run with the
scheduler control memory overlaid below the data.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkInput

open BurstRAM Compression PrimedStackRAM SourceTransport
open private offsets from OAI.Computability.VPVNP.CompressorRecordsShrinkPlacement
open private site_lt from OAI.Computability.VPVNP.CompressorRecordsShrinkRankArena

variable {w a g : ℕ}

private abbrev Within (lo hi z : ℕ) := lo ≤ z ∧ z < hi

private theorem address {lo hi size : ℕ} (base i : Word w) (low : lo ≤ base.val)
    (index : i.val < size) (before : base.val+size ≤ hi) (fit : hi ≤ 2^w) :
    Within lo hi (base+i).val := by
  rw [Fin.val_add,Nat.mod_eq_of_lt (by omega)]
  exact ⟨by omega,by omega⟩

private theorem placement_row (p : Fin 14 → Word w) (m : Memory w) (i : Word w)
    (rd wr : ℕ → Prop) (read : ∀ c : Fin 4, rd (ShrinkRAM.readAddr p c i))
    (write : ∀ c : Fin 4, wr (ShrinkRAM.outAddr p c i)) :
    Reads rd (ShrinkRAM.events p m i) ∧ Writes wr (ShrinkRAM.events p m i) := by
  constructor <;> intro a v h
  · simp only [ShrinkRAM.events,List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,
      reduceCtorEq,Event.read.injEq,and_false,or_false,false_or] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    exacts [read 0,read 1,read 2,read 3]
  · simp only [ShrinkRAM.events,List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,
      reduceCtorEq,Event.write.injEq,and_false,or_false,false_or] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    exacts [write 0,write 1,write 2,write 3]

private theorem classify_row (p : Fin 11 → Word w) (m : Memory w) (i : Word w)
    (rd wr : ℕ → Prop) (read : ∀ c : Fin 6, rd (BundleRAM.readAddress p m i c).val)
    (write : ∀ c : Fin 2, wr (BundleRAM.outAddr p c i)) :
    Reads rd (BundleRAM.events p m i) ∧ Writes wr (BundleRAM.events p m i) := by
  constructor <;> intro a v h
  · simp only [BundleRAM.events,List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,
      reduceCtorEq,Event.read.injEq,and_false,or_false,false_or] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    exacts [read 0,read 1,read 2,read 3,read 4,read 5]
  · simp only [BundleRAM.events,List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,
      reduceCtorEq,Event.write.injEq,and_false,or_false,false_or] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩
    exacts [write 0,write 1]

namespace Run

variable {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w} {start : ℕ}
variable {m : Memory w} (r : Run X T start m)

local notation "N" => Fintype.card X.Base
local notation "S" => N*2^(packingLaneBits a g)
local notation "A" => S*2^a
local notation "Z" => plan X start
local notation "sh" => placementBank X T start
local notation "wb" => widthBase X start
local notation "p" => ShrinkRankSpace.Shape.classifyBank (plan X start) T (placementBank X T start)
local notation "q" => ShrinkRankSpace.Shape.collectBank (plan X start) w

theorem placement_access (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) (room : stop X start < 2^w) :
    LogAccess (Within lo (placementBase X start)) (Within (placementBase X start) (rankBase X start)) r.sites := by
  let P := ((template ShrinkRAM.visit 0).instantiate w sh).program
  obtain ⟨h₁,h₂,h₃,h₄⟩ := range_bounds X start
  have init : lo ≤ start := (low 0).trans ((Nat.le_add_right ..).trans (r.greedy.old 0))
  have fit := h₃.trans_lt (h₄.trans_lt room)
  have bank := r.bankParams room
  have hb := r.inputBounds
  have bounds := GreedyArena.bounds start N a
  have lc : lo ≤ (sh 6).val := by
    change lo ≤ start % (2^w)
    rw [Nat.mod_eq_of_lt (h₁.trans_lt (h₂.trans_lt fit))]; exact init
  have lt : lo ≤ (sh 7).val := by
    change lo ≤ GreedyArena.offsetBase start N a % (2^w)
    have k : GreedyArena.offsetBase start N a < 2^w := by have := r.greedy.room; omega
    rw [Nat.mod_eq_of_lt k]; exact init.trans (by unfold GreedyArena.offsetBase; omega)
  apply SlotEventBounds.scan P 65 S (ShrinkRAM.events sh) (fun _ ↦ True) _ _
    (ShrinkRAM.visit_native sh) _ _ _ trivial r.positions
  intro j hj mem _
  let i := Fin.ofNat (2^w) j
  have hi : i.val < S := (Nat.mod_le ..).trans_lt hj
  have off := offsets X T _ _ _ false bank i hi
  have rd (c : Fin 4) : Within lo (placementBase X start) (ShrinkRAM.readAddr sh c i) := by
    fin_cases c
    · exact address _ _ lc off.1 hb.1 (h₂.trans fit.le)
    · exact address _ _ lt off.1 hb.2.1 (h₂.trans fit.le)
    · exact address _ _ (low 0) off.2 hb.2.2.1 (h₂.trans fit.le)
    · exact address _ _ (low 2) off.2 hb.2.2.2 (h₂.trans fit.le)
  have wr (c : Fin 4) : Within (placementBase X start) (rankBase X start) (ShrinkRAM.outAddr sh c i) := by
    apply address _ i _ hi (pre_starts X T start room c) fit.le
    rw [show (sh (c.natAdd 10)).val = placementBase X start+c.val*S from ShrinkPlacement.starts X T _ _ _ false fit c]
    exact Nat.le_add_right ..
  exact ⟨(placement_row sh mem i _ _ rd wr).1,(placement_row sh mem i _ _ rd wr).2,trivial⟩

theorem clear_access (room : stop X start < 2^w) :
    LogAccess (fun _ ↦ False) (Within (Z).counts (Z).ids) r.clear := by
  have fit := (range_bounds X start).2.2.2.trans_lt room
  have hv := (Z).values T sh Fintype.card_pos fit
  have hb : (Z).counts+2*(Z).B ≤ 2^w := by
    change (Z).counts+2*(Z).B+(Z).rectangleSize+(Z).rectangleSize+(Z).A < 2^w at fit
    omega
  exact direct_scan _ 8 4 2 (Z).counts (2*(Z).B) (fun _ ↦ (0 : Word w)) hb
    (fun mem i ↦ SliceRAM.clearVisit_native (q 3) i mem) _ _ r.ranking.clear

theorem classify_access (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) (room : stop X start < 2^w) :
    LogAccess (Within lo (rankBase X start)) (Within (rankBase X start) (Z).counts) r.classify := by
  let prog := ((template BundleRAM.visit 0).instantiate w p).program
  obtain ⟨h₁,h₂,h₃,h₄⟩ := range_bounds X start
  have fit := h₄.trans_lt room
  have hZ := (Z).values T sh Fintype.card_pos fit
  have hA := ((Z).scalarFits Fintype.card_pos fit).1.le
  have lowStart : lo ≤ start := (low 3).trans ((Nat.le_add_right ..).trans (r.greedy.old 3))
  have old (c : Fin 6) : (T.column c).val+A ≤ rankBase X start :=
    (r.greedy.old c).trans (h₁.trans h₂)
  have counts : (Z).counts = rankBase X start+2*A := rfl
  have cfit : (Z).counts ≤ wb := by
    change (Z).counts ≤ (Z).counts+2*(Z).B+(Z).rectangleSize+(Z).rectangleSize+(Z).A; omega
  have hrank := h₃.trans fit.le
  have hw (i : Word w) (hi : i.val < A) (c : Fin 2) : Within (rankBase X start) (Z).counts (BundleRAM.outAddr p c i) := by
    fin_cases c
    · apply address (p 9) i _ hi _ (cfit.trans fit.le)
      · exact hZ.owner.ge
      · rw [hZ.owner,counts]; change rankBase X start+A ≤ rankBase X start+2*A; omega
    · apply address (p 10) i _ hi _ (cfit.trans fit.le)
      · rw [hZ.key]; exact Nat.le_add_right ..
      · rw [hZ.key,counts]; change rankBase X start+A+A ≤ rankBase X start+2*A; omega
  let ms := after r.greedy.post (eventLog r.sites)
  let m₀ := after ms (eventLog r.clear)
  have incSite : T.Represents X ms := r.greedy.incidence.retain (fun c ↦ (r.greedy.old c).trans h₁) r.siteFrame
  have inc₀ : T.Represents X m₀ := incSite.retain old (fun z hz ↦
    SourceTransport.after_outside ms (r.clear_access room).2 (fun h ↦ by have hx := h.1; rw [counts] at hx; omega))
  have lowPre (t : Fin 4) : lo ≤ (sh (t.natAdd 10)).val := by
    rw [show (sh (t.natAdd 10)).val = placementBase X start+t.val*S from
      ShrinkPlacement.starts X T _ _ _ false (h₃.trans_lt fit) t]
    exact (lowStart.trans h₁).trans (Nat.le_add_right ..)
  apply SlotEventBounds.scan prog (1+BundleRAM.visit.length) A (BundleRAM.events p) (T.Represents X) _ _
    (BundleRAM.visit_native p) _ m₀ r.classify inc₀ r.ranking.ranked.classify
  intro j hj mem inc
  let i := Fin.ofNat (2^w) j
  have hi : i.val < A := (Nat.mod_le ..).trans_lt hj
  obtain ⟨hs,ht⟩ := site_lt X T sh (rankBase X start) mem inc.actual hZ hA i hi
  have rd (c : Fin 6) : Within lo (rankBase X start) (BundleRAM.readAddress p mem i c).val := by
    fin_cases c
    · exact address T.actualOut i (low 3) hi (old 3) hrank
    · exact address (sh 11) _ (lowPre 1) hs (pre_starts X T start room 1) hrank
    · exact address (sh 11) _ (lowPre 1) ht (pre_starts X T start room 1) hrank
    · exact address (sh 10) _ (lowPre 0) hs (pre_starts X T start room 0) hrank
    · exact address (sh 12) _ (lowPre 2) hs (pre_starts X T start room 2) hrank
    · exact address (sh 12) _ (lowPre 2) ht (pre_starts X T start room 2) hrank
  obtain ⟨reads,writes⟩ := classify_row p mem i _ _ rd (hw i hi)
  exact ⟨reads,writes,inc.retain old (fun z hz ↦ SourceTransport.after_outside mem writes (fun h ↦ hz.not_ge h.1))⟩

theorem append_access (room : stop X start < 2^w) :
    LogAccess (Within (rankBase X start) (Z).ids) (Within (Z).counts (Z).gathered) r.append := by
  have h := range_bounds X start
  have fit := h.2.2.2.trans_lt room
  have hv := (Z).values T sh Fintype.card_pos fit
  have before := (r.greedy.old 5).trans (h.1.trans h.2.1)
  have reg := ((Z).regions T sh Fintype.card_pos before fit).1
  have raw := SlotFillFootprint.append_run reg r.ranking.ranked.append
  have own : (q 1).val = rankBase X start := hv.owner
  have cend : (Z).counts+2*(Z).B = (Z).ids := rfl
  have rend : (Z).ids+2*(Z).B*(Z).Q = (Z).gathered := rfl
  have cstart : rankBase X start+2*A = (Z).counts := rfl
  apply LogAccess.mono raw
  · intro x hx
    rcases hx with ⟨hx₁,hx₂⟩ | ⟨hx₁,hx₂⟩
    · rw [own,hv.count] at *; change x < rankBase X start+A at hx₂; exact ⟨hx₁,by omega⟩
    · rw [hv.counts] at hx₁ hx₂; rw [hv.buckets] at hx₂; exact ⟨by omega,by omega⟩
  · intro x hx
    rcases hx with ⟨hx₁,hx₂⟩ | ⟨hx₁,hx₂⟩
    · rw [hv.counts] at hx₁ hx₂; rw [hv.buckets] at hx₂; exact ⟨hx₁,by omega⟩
    · rw [hv.ids] at hx₁ hx₂; rw [hv.buckets,hv.stride,rend] at hx₂; exact ⟨by omega,hx₂⟩

end Run

end CompressorRecords.ShrinkInput

end VPVNP
end Computability
end OAI
