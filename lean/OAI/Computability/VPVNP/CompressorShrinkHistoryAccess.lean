import OAI.Computability.VPVNP.CompressorRecordsShrinkHistoryTrace

/-! # External read and write addresses of the selected shrinking rows -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkHistoryTrace

open BurstRAM OrdinalRun SourceTransport PrimedStackRAM
open scoped Fin.CommRing Classical

variable {w : ℕ}

private theorem placement_events (p : Fin 14 → Word w) (m : Memory w) (i : Word w) :
    Reads (fun x => ∃ c : Fin 4, x = ShrinkRAM.readAddr p c i) (ShrinkRAM.events p m i) ∧
      Writes (fun x => ∃ c : Fin 4, x = ShrinkRAM.outAddr p c i) (ShrinkRAM.events p m i) := by
  constructor <;> intro a v ha
  · simp [ShrinkRAM.events] at ha
    rcases ha with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  · simp [ShrinkRAM.events] at ha
    rcases ha with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

private theorem role_events (p : Fin 11 → Word w) (m : Memory w) (i : Word w) :
    Reads (fun x => ∃ c : Fin 6, x = DemandRAM.inputAddr p m i c) (DemandRAM.events p m i) ∧
      Writes (fun x => ∃ t : Fin 4, x = DemandRAM.fieldAddr p i t) (DemandRAM.events p m i) := by
  constructor <;> intro a v ha
  · simp [DemandRAM.events] at ha
    rcases ha with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨5,rfl⟩
  · simp [DemandRAM.events] at ha
    rcases ha with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

/-- The placement report group reads only the old color, offset, mate and
displacement addresses, and writes only the four new columns. -/
theorem placement_access (p : Fin 14 → Word w) (n : ℕ) (m : Memory w) (rs : List (Report w))
    (run : runSegment ((template ShrinkRAM.visit 0).instantiate w p).program 65 (some 0) m
      (List.replicate n []) = some rs) :
    Reads (fun x => ∃ j < n, ∃ c : Fin 4, x = ShrinkRAM.readAddr p c (j : Word w)) (eventLog rs) ∧
      Writes (fun x => ∃ j < n, ∃ c : Fin 4, x = ShrinkRAM.outAddr p c (j : Word w)) (eventLog rs) := by
  let M := (template ShrinkRAM.visit 0).instantiate w p
  apply OrdinalRun.footprint M.program 65 (fun j => (j : Word w)) n (fun _ _ => True) _ _ _ 0 _ m rs
    (by simp) trivial run
  intro j hj mem _ bits rep h
  have eqn := (execute_prefix_unique (ShrinkRAM.visit_native p mem (j : Word w))
    (show execute M.program 65 (M.program.start (j : Word w)) mem ([]++bits) = some rep from h)).2
  subst rep
  obtain ⟨rd,wr⟩ := placement_events p mem (j : Word w)
  exact ⟨by simp,trivial,fun a v ha => ⟨j,hj,rd a v ha⟩,fun a v ha => ⟨j,hj,wr a v ha⟩⟩

private theorem role_input_stable {p : Fin 11 → Word w} {old m : Memory w} {N : ℕ} {i : Word w}
    (reg : DemandRAM.Regions p old N) (hi : i.val < N) (done : DemandRAM.Written p old m i.val)
    (c : Fin 6) : DemandRAM.inputAddr p m i c = DemandRAM.inputAddr p old i c := by
  have read (j : Fin 6) : m (DemandRAM.inputAddr p old i j) = old (DemandRAM.inputAddr p old i j) :=
    done.frame _ fun u t hu => reg.input i u j t hi (hu.trans hi)
  have t : BundleRAM.targetSite p m i = BundleRAM.targetSite p old i := congrArg (fun v => ShrinkRAM.div v (p 0)) (read 0)
  have a : m (p 6+BundleRAM.sourceSite p i).val = old (p 6+BundleRAM.sourceSite p i).val := read 1
  have ends : DemandRAM.endpoints p m i = DemandRAM.endpoints p old i := by simp only [DemandRAM.endpoints,t,a]
  simp only [DemandRAM.inputAddr,t,ends]

open private Written.step from OAI.Computability.VPVNP.CompressorRecordsDemandScan

/-- Even the indirect role lookups refer to the addresses determined by the
original incidence columns at the start of this phase. -/
theorem role_access (p : Fin 11 → Word w) (n : ℕ) (old : Memory w) (rs : List (Report w))
    (reg : DemandRAM.Regions p old n)
    (run : runSegment ((template DemandRAM.visit 0).instantiate w p).program 65 (some 0) old
      (List.replicate n []) = some rs) :
    Reads (fun x => ∃ j < n, ∃ c : Fin 6, x = DemandRAM.inputAddr p old (j : Word w) c) (eventLog rs) ∧
      Writes (fun x => ∃ j < n, ∃ c : Fin 4, x = DemandRAM.fieldAddr p (j : Word w) c) (eventLog rs) := by
  let M := (template DemandRAM.visit 0).instantiate w p
  apply OrdinalRun.footprint M.program 65 (fun j => (j : Word w)) n (fun j mem => DemandRAM.Written p old mem j)
    _ _ _ 0 _ old rs (by simp) (DemandRAM.Written.start p old) run
  intro j hj mem inv bits rep h
  let i : Word w := j
  have val : i.val = j := Nat.mod_eq_of_lt (hj.trans_le reg.fits)
  have hi : i.val < n := val ▸ hj
  have atI : DemandRAM.Written p old mem i.val := val ▸ inv
  have eqn := (execute_prefix_unique (DemandRAM.visit_native p mem i)
    (show execute M.program 65 (M.program.start i) mem ([]++bits) = some rep from h)).2
  subst rep
  obtain ⟨rd,wr⟩ := role_events p mem i
  refine ⟨by simp [i],?_,?_,fun a v ha => ⟨j,hj,wr a v ha⟩⟩
  · rw [DemandRAM.visit_after]
    exact val ▸ Written.step reg hi atI
  · intro a v ha
    obtain ⟨c,hc⟩ := rd a v ha
    exact ⟨j,hj,c,hc.trans (role_input_stable reg hi atI c)⟩

open Compression SelectedArena
open private decoded_offsets from OAI.Computability.VPVNP.CompressorRecordsSelectedArena
open private demand_offsets from OAI.Computability.VPVNP.CompressorRecordsSelectedArenaDemand

/-- Lowest address among the old color, offset, mate and displacement columns supplied to the
shrinking pass. -/
def inputFloor (p : Fin 14 → Word w) := min (min (p 6).val (p 7).val) (min (p 8).val (p 9).val)

/-- Every event of the chronological placement and role scans lies in
its physical source or output interval. These estimates hold after selecting
either layout. -/
theorem selected_access {k : Type*} [_root_.Field k] {schedule : BlockSchedule k} (B : schedule.Templates)
    {a g : ℕ} (X : State a (packingLaneBits a g)) (term stride selectors : Word w)
    (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) (s : SelectedScore.Selection B X)
    (m : Memory w) (p : SelectedStage.Passes w) (exec : SelectedStage.Execution X term stride selectors p₀ T m p)
    (stored : SelectedStage.Stored B X term stride p₀ s m p) (old : OldInputs X term stride p₀ T)
    {initialSide : Bool} (hp : ShrinkRAM.Params p₀ a (Shrink.colors a) (Shrink.J a) g initialSide)
    (fit : Fits X term stride) :
    Reads (fun x => inputFloor p₀ ≤ x ∧ x < origin X term stride) (eventLog p.positions) ∧
    Writes (fun x => placementBase X term stride ≤ x ∧ x < roleBase X term stride) (eventLog p.positions) ∧
    Reads (fun x => (T.actualOut.val ≤ x ∧ x < origin X term stride) ∨
      (placementBase X term stride ≤ x ∧ x < roleBase X term stride)) (eventLog p.roles) ∧
    Writes (fun x => roleBase X term stride ≤ x ∧ x < endAddr X term stride) (eventLog p.roles) := by
  let sh := selectedWords X term stride p₀ (p.afterScores m)
  let role := demandWords X term stride p₀ T
  let bit := (p.afterScores m) (origin X term stride+2)
  let chosen := X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s
  have room : origin X term stride+3+4*positions X+4*DemandRAM.absoluteCount X < 2^w := fit
  have eo := DemandRAM.count_eq X
  have reg := demand_regions X term stride p₀ T bit (p.afterPositions m) chosen hp exec.incidenceBeforeRoles stored.placementBeforeRoles old fit
  obtain ⟨pr,pw⟩ := placement_access sh (positions X) (p.afterScores m) _ exec.positions
  obtain ⟨rr,rw'⟩ := role_access role (DemandRAM.oldCount X) (p.afterPositions m) _ reg exec.roles
  obtain ⟨pRange,rRange⟩ := selected_ranges X term stride p₀ T (p.afterScores m) hp fit
  have fbound (head off : Word w) {size : ℕ} (hold : head.val+size ≤ origin X term stride) (ho : off.val < size) :
      head.val ≤ (head+off).val ∧ (head+off).val < origin X term stride := by
    rw [Fin.val_add,Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · intro x v hx
    obtain ⟨j,hj,c,eq⟩ := pr x v hx
    rw [eq]
    let i : Word w := j
    have vi : i.val=j := Nat.mod_eq_of_lt (by omega)
    obtain ⟨base,arc⟩ := decoded_offsets X p₀ hp i (vi ▸ hj)
    have here (head off : Word w) {N : ℕ} (hl : inputFloor p₀ ≤ head.val) (hstart : head.val+N ≤ origin X term stride)
        (hoff : off.val < N) : inputFloor p₀ ≤ (head+off).val ∧ (head+off).val < origin X term stride := by
      obtain ⟨ha,hb⟩ := fbound head off hstart hoff
      exact ⟨hl.trans ha,hb⟩
    fin_cases c
    · exact here _ _ ((min_le_left ..).trans (min_le_left ..)) old.color base
    · exact here _ _ ((min_le_left ..).trans (min_le_right ..)) old.offset base
    · exact here _ _ ((min_le_right ..).trans (min_le_left ..)) old.mate arc
    · exact here _ _ ((min_le_right ..).trans (min_le_right ..)) old.displacement arc
  · intro x v hx
    obtain ⟨j,hj,c,eq⟩ := pw x v hx
    exact eq ▸ pRange j hj c
  · intro x v hx
    obtain ⟨j,hj,c,eq⟩ := rr x v hx
    rw [eq]
    let i : Word w := j
    have vi : i.val=j := Nat.mod_eq_of_lt (by omega)
    obtain ⟨src,dst,lo,hi⟩ := demand_offsets X role sh T (p.afterPositions m) chosen (inputs X term stride p₀ T bit)
      hp.degree exec.incidenceBeforeRoles stored.placementBeforeRoles (by omega) i (vi ▸ hj)
    have col (t : Fin 4) (off : Word w) (ho : off.val < positions X) :
        placementBase X term stride ≤ (placementWord X term stride t+off).val ∧
        (placementWord X term stride t+off).val < roleBase X term stride := by
      have ht := Nat.mul_le_mul_right (positions X) t.isLt
      rw [Nat.succ_mul] at ht
      change placementBase X term stride ≤ _ ∧ _ < placementBase X term stride + 4*positions X
      rw [Fin.val_add,column_value X term stride fit,Nat.mod_eq_of_lt (by unfold placementBase; omega)]
      omega
    fin_cases c
    · exact .inl (fbound T.actualOut i old.actualOut (vi ▸ hj))
    · exact .inr (col 1 _ src)
    · exact .inr (col 1 _ dst)
    · exact .inr (col 2 _ lo)
    · exact .inr (col 3 _ lo)
    · exact .inr (col 0 _ hi)
  · intro x v hx
    obtain ⟨j,hj,c,eq⟩ := rw' x v hx
    exact eq ▸ rRange j hj c

end CompressorRecords.ShrinkHistoryTrace

end VPVNP
end Computability
end OAI
