import OAI.Computability.VPVNP.CompressorRefreshStageFrame
import OAI.Computability.VPVNP.CompressorRecordRefreshPrepareAllocation

/-!
# Guarded refresh gather, directory and segment scans

The first two scans read only the old incidence columns. The offset scan reads the new
scratch columns, using the translated destination stored by the bundle scan. All three
write inside the selected level's allocation and return consecutive ordinal cursors.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.FrontFrame

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.Refresh
open SourceTransport StageFrame Allocation NewSlots
open scoped Fin.CommRing

open private gather_step from OAI.Computability.VPVNP.CompressorRecordRefreshOldWidths
open private step from OAI.Computability.VPVNP.CompressorRecordRefreshDirectory
open private bundle_le destination_at from OAI.Computability.VPVNP.CompressorRecordRefreshScan

variable {w a g : ℕ}

/-- An address in one of the six old incidence columns within the specified segment count. -/
def OldCell (T : IncidenceDirectory w) (segments x : ℕ) : Prop :=
  ∃ c : Fin 6, (T.column c).val ≤ x ∧ x < (T.column c).val + segments

/-- An address in the half-open interval allocated to this refresh level. -/
def LevelCell (P : Plan) (x : ℕ) : Prop := P.start ≤ x ∧ x < P.stop

private theorem demand_le (P : Plan) : P.demand ≤ P.stop := by
  dsimp only [Plan.stop, Plan.next, Plan.reverseSlot, Plan.targetPort, Plan.supply, Plan.term]
  omega

private theorem segments_lt (P : Plan) (room : P.stop < 2^w) : P.segments < 2^w := by
  have := demand_le P
  dsimp only [Plan.demand] at this
  omega

private theorem old_cell (P : Plan) (T : IncidenceDirectory w) (room : P.stop < 2^w)
    (before : ∀ c, (T.column c).val+P.segments ≤ P.start) (c : Fin 6) (i : BurstRAM.Word w) (hi : i.val < P.segments) :
    OldCell T P.segments (T.column c+i).val := by
  have hd := demand_le P
  dsimp only [Plan.demand] at hd
  have := before c
  rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  exact ⟨c,by omega,by omega⟩

private theorem scratch_cell (P : Plan) (room : P.stop < 2^w) (c : Fin 8) (hc : c ≠ 0) (i : BurstRAM.Word w)
    (hi : i.val < P.segments) : LevelCell P (P.scratch w c+i).val := by
  have hd := demand_le P
  obtain ⟨low,high⟩ := P.scratch_interval (hd.trans room.le) c hc i hi
  exact ⟨low,high.trans_le hd⟩

variable (X : State a (a+g)) (T : IncidenceDirectory w) (a₀ dH t stride start : ℕ)
local notation "P" => plan X a₀ dH t stride start
local notation "Q" => Plan.scratch P w
local notation "S" => Plan.segments P
local notation "N" => Plan.sites P
local notation "L" => (word (bits := w) (2^g))
local notation "G" => gatherWords Q L T.width
local notation "B" => directoryWords Q L T.baseOut T.shift
local notation "O" => IncidenceDirectory.baseOrder X

/-- The entire gather reads the old width permutation and writes only inside the selected level. -/
theorem gather_scan (before : ∀ c, (T.column c).val+S ≤ start) (room : (P).stop < 2^w)
    (m : Memory w) (rs : List (Report w))
    (run : runSegment ((template RefreshGather.gather 0).instantiate w G).program 24
      (some 0) m (List.replicate S []) = some rs) :
    Scanned 0 S rs ∧ RefreshGather.Gathered G m (after m (eventLog rs)) S ∧
      Reads (OldCell T S) (eventLog rs) ∧ Writes (LevelCell P) (eventLog rs) := by
  let data := G
  have alloc := prepare_layout X T a₀ dH t stride start before room
  have fit := segments_lt (P) room
  apply scan _ 24 0 S (fun j n ↦ RefreshGather.Gathered G m n j) (RefreshGather.events data)
    (OldCell T S) (LevelCell P) (fun j _ _ m ↦ RefreshGather.gather_native data m j) _ (Nat.zero_le _) m rs
    ⟨fun _ h ↦ (Nat.not_lt_zero _ h).elim,fun _ _ ↦ rfl⟩ (by simpa only [Nat.sub_zero,Nat.cast_zero] using run)
  intro j _ hj m' h
  let i : BurstRAM.Word w := j
  have hv : i.val = j := Nat.mod_eq_of_lt (hj.trans fit)
  have hi : i.val < S := hv ▸ hj
  have hold := gather_index_lt (Q 0) L i (Fintype.card X.Base)
    (by rw [alloc.degree]; exact Nat.two_pow_pos _) (by rw [alloc.lanes]; exact Nat.two_pow_pos _)
    (by rw [alloc.degree,alloc.lanes]; exact hi)
  rw [alloc.degree,alloc.lanes] at hold
  have old : OldCell T S (RefreshGather.widthAddress data i).val := old_cell (P) T room before 5 _ hold
  have fresh : LevelCell P (data 3+i).val := scratch_cell (P) room 1 (by decide) i hi
  refine ⟨?_,?_,?_⟩
  · simpa only [RefreshGather.gather_after,hv] using gather_step alloc.gather i hi (hv ▸ h)
  · intro addr v mem
    simp [RefreshGather.events] at mem
    exact mem.1 ▸ old
  · intro addr v mem
    simp [RefreshGather.events] at mem
    exact mem.1 ▸ fresh

/-- Every bundle reads an old target and displacement, initializes three scratch cells,
and advances the ordinal and the genuine partial-directory invariant. -/
theorem bundles_scan (before : ∀ c, (T.column c).val+S ≤ start) (room : (P).stop < 2^w)
    (m : Memory w) (source : BundleDirectory.BaseTables (splitSlots X) O B m) (rs : List (Report w))
    (run : runSegment ((template BundleDirectory.visit 0).instantiate w B).program 28
      (some 0) m (List.replicate N []) = some rs) :
    Scanned 0 N rs ∧ BundleDirectory.Prefix (splitSlots X) O B (after m (eventLog rs)) N ∧
      Reads (OldCell T S) (eventLog rs) ∧ Writes (LevelCell P) (eventLog rs) := by
  let data := B
  have alloc := prepare_layout X T a₀ dH t stride start before room
  have ns : N ≤ S := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
  have fit := ns.trans_lt (segments_lt (P) room)
  apply scan _ 28 0 N (fun j m ↦ BundleDirectory.Prefix (splitSlots X) O B m j) (BundleDirectory.events data)
    (OldCell T S) (LevelCell P) (fun j _ _ m ↦ BundleDirectory.visit_native data m j) _ (Nat.zero_le _) m rs
    ⟨source,fun _ h ↦ (Nat.not_lt_zero _ h).elim⟩ (by simpa only [Nat.sub_zero,Nat.cast_zero] using run)
  intro j _ hj m' h
  let i : BurstRAM.Word w := j
  have hv : i.val = j := Nat.mod_eq_of_lt (hj.trans fit)
  have hi : i.val < N := hv ▸ hj
  have arc : (BundleDirectory.sourceArc data i).val < S :=
    ((Nat.mod_le ..).trans (Nat.div_le_self ..)).trans_lt (hi.trans_le ns)
  have a₁ : OldCell T S (data 1+BundleDirectory.sourceArc data i).val := old_cell (P) T room before 0 _ arc
  have a₅ : OldCell T S (data 5+BundleDirectory.sourceArc data i).val := old_cell (P) T room before 2 _ arc
  have a₂ : LevelCell P (data 2+i).val := scratch_cell (P) room 2 (by decide) i (hi.trans_le ns)
  have a₃ : LevelCell P (data 3+i).val := scratch_cell (P) room 3 (by decide) i (hi.trans_le ns)
  have a₄ : LevelCell P (data 4+i).val := scratch_cell (P) room 4 (by decide) i (hi.trans_le ns)
  refine ⟨?_,?_,?_⟩
  · simpa only [BundleDirectory.events_after,hv] using step (splitSlots X) O B alloc.directory m' i hi (hv ▸ h)
  · intro addr v mem
    simp [BundleDirectory.events] at mem
    rcases mem with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> assumption
  · intro addr v mem
    simp [BundleDirectory.events] at mem
    rcases mem with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> assumption

/-- The selected segment permutation stays inside the scratch arrays in every prefix. -/
theorem offsets_scan (room : (P).stop < 2^w) (reg : RefreshRAM.Regions Q S)
    (A : RefreshRAM.Input w) (legal : RefreshRAM.Legal Q S A) (m : Memory w)
    (init : RefreshRAM.AtCursor Q S A m 0) (rs : List (Report w))
    (run : runSegment ((template RefreshRAM.visit 0).instantiate w Q).program 33
      (some 0) m (List.replicate S []) = some rs) :
    Scanned 0 S rs ∧ RefreshRAM.AtCursor Q S A (after m (eventLog rs)) S ∧
      Reads (LevelCell P) (eventLog rs) ∧ Writes (LevelCell P) (eventLog rs) := by
  have fit := segments_lt (P) room
  apply scan _ 33 0 S (fun j m ↦ RefreshRAM.AtCursor Q S A m j) (RefreshRAM.events Q)
    (LevelCell P) (LevelCell P) (fun j _ _ m ↦ RefreshRAM.visit_native Q m j) _ (Nat.zero_le _) m rs init
    (by simpa only [Nat.sub_zero,Nat.cast_zero] using run)
  intro j _ hj m' h
  let i : BurstRAM.Word w := j
  have hv : i.val = j := Nat.mod_eq_of_lt (hj.trans fit)
  have hi : i.val < S := hv ▸ hj
  have hb := (bundle_le Q i).trans_lt hi
  have hd : (RefreshRAM.destination Q m' i).val < S := destination_at h i hi ▸ legal.dst_lt i hi
  have out (c : Fin 8) (hc : c ≠ 0) := scratch_cell (P) room c hc i hi
  have bnd (c : Fin 8) (hc : c ≠ 0) := scratch_cell (P) room c hc (RefreshRAM.bundle Q i) hb
  have dst (c : Fin 8) (hc : c ≠ 0) := scratch_cell (P) room c hc (RefreshRAM.destination Q m' i) hd
  refine ⟨?_,?_,?_⟩
  · simpa only [RefreshRAM.events_after,hv] using RefreshRAM.cursor_step reg legal i hi (hv ▸ h)
  · intro addr v mem
    simp [RefreshRAM.events] at mem
    rcases mem with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    exacts [bnd 2 (by decide),bnd 3 (by decide),out 1 (by decide),bnd 4 (by decide)]
  · intro addr v mem
    simp [RefreshRAM.events] at mem
    rcases mem with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    exacts [out 5 (by decide),dst 6 (by decide),dst 7 (by decide),bnd 4 (by decide)]

end CompressorRecords.PortRefresh.FrontFrame

end VPVNP
end Computability
end OAI
