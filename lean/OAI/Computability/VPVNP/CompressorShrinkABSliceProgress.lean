import OAI.Computability.VPVNP.CompressorSliceIndexedStarts

/-!
# Local progress of the transposed AB scans

A bundle can be visited at a fixed count, interval or incidence ordinal
after any number of calls on other bundles. Its input fields and its own bank
suffice to continue the three stages from their verified prefixes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.IndexedStarts

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SliceRAM SliceSchedule
open private adj_vals adj_space pair_space from OAI.Computability.VPVNP.CompressorSliceIndexedStarts

variable {w : ℕ}

/-- The address belongs to one bundle's contiguous bank for the given old and new field counts. -/
def BankAt (B : Word w) (m n x : ℕ) : Prop := B.val ≤ x ∧ x < B.val+capacity m n

/-- The first `k` words of this bundle's slice bank have been reset to zero. -/
def Cleared (B : Word w) (k : ℕ) (mem : Memory w) : Prop := ∀ i < k, mem (B.val+i) = 0

/-- For the first `k` old/new field pairs, memory records each intersection length and both
offsets whenever that length is positive. -/
structure Frames (B : Word w) (old new : List ℕ) (k : ℕ) (mem : Memory w) : Prop where
  lengths : ∀ j, j < k → (mem (B.val+old.length+new.length+3*j+2)).val = (sliceAt old new j).length
  offsets : ∀ j, j < k → 0 < (sliceAt old new j).length →
    (mem (B.val+old.length+new.length+3*j)).val = (sliceAt old new j).sourceOffset ∧
    (mem (B.val+old.length+new.length+3*j+1)).val = (sliceAt old new j).targetOffset

/-- The old- and new-endpoint directories index the first `k` intersection frames, grouping
them by the old and new field ordinals respectively. -/
structure Dirs (B : Word w) (old new : List ℕ) (k : ℕ) (mem : Memory w) : Prop where
  oldRows : (oldBank (adj B old.length new.length)).Represents mem
    (fun j => (sliceAt old new j).length) (· / new.length) k
  newRows : (newBank (adj B old.length new.length)).Represents mem
    (fun j => (sliceAt old new j).length) (· % new.length) k

theorem Cleared.keep {B : Word w} {m n k : ℕ} {mem out : Memory w} (hk : k ≤ m+n)
    (h : Cleared B k mem) (eqn : ∀ x, BankAt B m n x → out x = mem x) : Cleared B k out := by
  intro i hi
  rw [eqn _ (by dsimp [BankAt,capacity]; omega)]
  exact h i hi

theorem Frames.keep {B : Word w} {old new : List ℕ} {k : ℕ} {mem out : Memory w}
    (hk : k ≤ old.length*new.length) (h : Frames B old new k mem)
    (eqn : ∀ x, BankAt B old.length new.length x → out x = mem x) : Frames B old new k out := by
  constructor
  · intro j hj; rw [eqn _ (by dsimp [BankAt,capacity]; omega)]; exact h.lengths j hj
  · intro j hj hl
    rw [eqn _ (by dsimp [BankAt,capacity]; omega),eqn _ (by dsimp [BankAt,capacity]; omega)]
    exact h.offsets j hj hl

variable {B : Word w} {old new : List ℕ} {input : Fin 4 → Word w}
variable (space : Space input B old.length new.length)
local notation "m₀" => old.length
local notation "n₀" => new.length

include space

theorem Dirs.keep {k : ℕ} {mem out : Memory w} (hk : k ≤ m₀*n₀) (h : Dirs B old new k mem)
    (eqn : ∀ x, BankAt B m₀ n₀ x → out x = mem x) : Dirs B old new k out := by
  obtain ⟨hn,hm,_,hc,hr,hc',hr'⟩ := adj_vals space
  let q := adj B m₀ n₀
  have fit := space.fits
  dsimp [capacity] at fit
  have ho : (oldBank q).Fits := by
    constructor <;> simp only [oldBank,q,AdjBank.stop,hn,hm,hc,hr] <;> omega
  have hh : (newBank q).Fits := by
    constructor <;> simp only [newBank,q,AdjBank.stop,hn,hm,hc',hr',Nat.mul_comm n₀ m₀] <;> omega
  constructor
  · apply AdjBank.represents_congr ho h.oldRows
    · intro v _
      change _ ≤ (adj B m₀ n₀ 0).val; rw [hn]; exact adjPrefix_old_le _ hk
    · intro x hx; simp only [q,oldBank,AdjBank.Inside,AdjBank.stop,hn,hm,hc,hr] at hx
      exact eqn _ (by dsimp [BankAt,capacity]; omega)
  · apply AdjBank.represents_congr hh h.newRows
    · intro v _
      change _ ≤ (adj B m₀ n₀ 1).val; rw [hm]; exact adjPrefix_new_le _ hk
    · intro x hx; simp only [q,newBank,AdjBank.Inside,AdjBank.stop,hn,hm,hc',hr',Nat.mul_comm n₀ m₀] at hx
      exact eqn _ (by dsimp [BankAt,capacity]; omega)

theorem Dirs.zero {mem : Memory w} (h : Cleared B (m₀+n₀) mem) : Dirs B old new 0 mem := by
  obtain ⟨hn,hm,_,hc,_,hc',_⟩ := adj_vals space
  have hf := space.fits
  dsimp [capacity] at hf
  constructor
  · intro v hv
    change v.val < (adj B m₀ n₀ 1).val at hv
    rw [hm] at hv
    have addr : ((oldBank (adj B m₀ n₀)).count v).val = B.val+v.val := by
      change (B.val+v.val) % (2^w) = _
      exact Nat.mod_eq_of_lt (by omega)
    simp [rowRepresents,adjPrefix,addr]; exact h v.val (by omega)
  · intro v hv
    change v.val < (adj B m₀ n₀ 0).val at hv
    rw [hn] at hv
    have addr : ((newBank (adj B m₀ n₀)).count v).val = B.val+(m₀+v.val) := by
      rw [newBank,AdjBank.count,Fin.val_add,hc',Nat.mod_eq_of_lt (by omega),Nat.add_assoc]
    simp [rowRepresents,adjPrefix,addr]; exact h (m₀+v.val) (by omega)

omit space

private theorem single_exec {C : Type*} {P : BurstRAM.Program w C} {f : ℕ} {s : Word w}
    {mem : Memory w} {r : Report w}
    (h : runSegment P f (some s) mem (List.replicate 1 []) = some [r]) :
    execute P f (P.start s) mem [] = some r := by
  cases he : execute P f (P.start s) mem [] <;> simp [runSegment,he] at h
  exact congrArg some h

private theorem single (rs : List (Report w)) (h : rs.length = 1) : ∃ r, rs = [r] := by
  cases rs with
  | nil => simp at h
  | cons r rs => exact ⟨r,by simp [List.eq_nil_iff_length_eq_zero.mpr (by simpa using h)]⟩

include space

theorem clear_one (k : Fin (m₀+n₀)) (mem : Memory w) (h : Cleared B k.val mem) :
    let idx := Fin.ofNat (2^w) k.val
    let M := (template clearOps 0).instantiate w (fun _ => B)
    ∃ r, execute M.program 8 (M.program.start idx) mem [] = some r ∧ r.result = some (idx+1) ∧
      Cleared B (k.val+1) (after mem r.events) ∧
      ∀ x, ¬ BankAt B m₀ n₀ x → after mem r.events x = mem x := by
  intro idx M
  have hf := space.fits
  dsimp [capacity] at hf
  have hi := k.isLt
  have hv : idx.val = k.val := Nat.mod_eq_of_lt (by omega)
  have ha : (B+idx).val = B.val+k.val := by rw [Fin.val_add,hv,Nat.mod_eq_of_lt (by omega)]
  refine ⟨clearReport B idx,clearVisit_native _ _ _,rfl,?_,?_⟩
  · intro j hj
    change writeMemory mem (B+idx) 0 (B.val+j) = 0
    by_cases he : j = k.val
    · simp [writeMemory,ha,he]
    · simpa [writeMemory,ha,he] using h j (by omega)
  · intro x hx
    change writeMemory mem (B+idx) 0 x = mem x
    exact ite_eq_right (fun e => hx (by rw [e,ha]; dsimp [BankAt,capacity]; omega))

theorem frame_one (k : Fin (m₀*n₀)) (mem : Memory w) (hs : old.sum < 2^w) (ht : new.sum < 2^w)
    (reads : Inputs (pair input B m₀ n₀) old new mem) (clear : Cleared B (m₀+n₀) mem)
    (h : Frames B old new k.val mem) :
    let idx := Fin.ofNat (2^w) k.val
    let M := IndexedPair.table.instantiate w (pair input B m₀ n₀)
    ∃ r, execute M.program 38 (M.program.start idx) mem [] = some r ∧ r.result = some (Fin.ofNat _ (k.val+1)) ∧
      (Cleared B (m₀+n₀) (after mem r.events) ∧ Frames B old new (k.val+1) (after mem r.events)) ∧
      ∀ x, ¬ BankAt B m₀ n₀ x → after mem r.events x = mem x := by
  intro idx M
  let p := pair input B m₀ n₀
  have hf := space.fits
  dsimp [capacity] at hf
  have hp : (p 5).val = B.val+m₀+n₀ := Nat.mod_eq_of_lt (by omega)
  have ready : FramesAt p old new mem mem k.val := by
    exact ⟨reads,fun j hj => hp ▸ h.lengths j hj,fun j hj hl => hp ▸ h.offsets j hj hl,fun _ _ => rfl⟩
  obtain ⟨rs,run,post,ret,len,_,_⟩ := frameSegment_run (pair_space space) hs ht ready 1 k.isLt
  obtain ⟨r,rfl⟩ := single rs len
  simp only [eventLog,List.flatMap_singleton] at post
  change FramesAt p old new mem (after mem r.events) (k.val+1) at post
  refine ⟨r,single_exec run,ret,⟨?_,?_⟩,?_⟩
  · intro j hj; rw [post.outside _ (Or.inl (by rw [hp]; omega))]; exact clear j hj
  · exact ⟨fun j hj => hp ▸ post.lengths j hj,fun j hj hl => hp ▸ post.offsets j hj hl⟩
  · intro x hx
    apply post.outside
    dsimp [BankAt,capacity] at hx
    rw [hp]; have := k.isLt; omega

theorem refs_one (k : Fin (m₀*n₀)) (mem : Memory w) (frames : Frames B old new (m₀*n₀) mem)
    (dirs : Dirs B old new k.val mem) :
    let idx := Fin.ofNat (2^w) k.val
    let M := adjTemplate.instantiate w (adj B m₀ n₀)
    ∃ r, execute M.program 36 (M.program.start idx) mem [] = some r ∧ r.result = some (Fin.ofNat _ (k.val+1)) ∧
      (Frames B old new (m₀*n₀) (after mem r.events) ∧ Dirs B old new (k.val+1) (after mem r.events)) ∧
      ∀ x, ¬ BankAt B m₀ n₀ x → after mem r.events x = mem x := by
  intro idx M
  let q := adj B m₀ n₀
  let len := fun j => (sliceAt old new j).length
  obtain ⟨hn,hm,hf,hc,hr,hc',hr'⟩ := adj_vals space
  have sq : AdjRegions q := adj_space space
  have ready : AdjAt q len mem mem k.val := by
    refine ⟨?_,?_,fun _ _ _ => rfl⟩
    · simpa only [q,hn] using dirs.oldRows
    · simpa only [q,hn] using dirs.newRows
  have lengths (j : ℕ) (hj : j < (q 1).val*(q 0).val) : (mem ((q 2).val+3*j+2)).val = len j := by
    simpa only [q,hf] using frames.lengths j (by simpa only [q,hm,hn] using hj)
  obtain ⟨rs,run,post,ret,size,_,_⟩ := adjSegment_run sq lengths ready 1 (by simpa only [q,hm,hn] using Nat.succ_le_of_lt k.isLt)
  obtain ⟨r,rfl⟩ := single rs size
  simp only [eventLog,List.flatMap_singleton] at post
  change AdjAt q len mem (after mem r.events) (k.val+1) at post
  have same (x : ℕ) (lo : B.val+m₀+n₀ ≤ x) (up : x < B.val+m₀+n₀+3*(m₀*n₀)) :
      after mem r.events x = mem x := post.frame_eq sq (by simpa only [q,hf] using lo)
        (by simpa only [q,hm,hn,hf] using up)
  refine ⟨r,single_exec run,ret,⟨?_,?_⟩,?_⟩
  · constructor
    · intro j hj; rw [same _ (by omega) (by omega)]; exact frames.lengths j hj
    · intro j hj hl; rw [same _ (by omega) (by omega),same _ (by omega) (by omega)]; exact frames.offsets j hj hl
  · exact ⟨by simpa only [q,hn] using post.oldRows,by simpa only [q,hn] using post.newRows⟩
  · intro x hx
    dsimp [BankAt,capacity] at hx
    apply post.outside <;>
      simp only [oldBank,newBank,q,AdjBank.Inside,AdjBank.stop,hn,hm,hc,hr,hc',hr',Nat.mul_comm n₀ m₀] <;> omega

end CompressorRecords.IndexedStarts

end VPVNP
end Computability
end OAI
