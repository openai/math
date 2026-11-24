import OAI.Computability.VPVNP.LiveHeaderFieldState
import OAI.Computability.VPVNP.LiveHeaderScanRows

/-!
# The full native incident-field suffix

The final sixteen scheduled stages alternate a private descriptor with a
bounded scan. The descriptors always run on the real width, mode and phase
words, and the scans read the original packed headers. Each accepted stage
hands off its actual final memory. Malformed padding yields a valid prefix
leading to a scan with no accepting continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.Fields

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderDescriptors
open ChainAssignments CutSchedule LiveHeader PrimedInputRAM

variable {s : Sizes} {base d w : ℕ} {hw : 4 ≤ w} {advice : Bits s.advice}
  {cuts : AllCuts s.h s.delta} {g : Fin (2^(s.h+1))} {tag : Mode.Tag}

/-- Public bounds for these sixteen stages. -/
structure Bounds (s : Sizes) (base d w : ℕ) : Prop where
  fit : limit s base < 2^w
  scratch : 2^d ≤ base
  sites : s.capacity .exterior ≤ 2^d
  exponents : 1+s.e ≤ s.delta
  config : 1+s.config ≤ s.delta

private theorem base_val (bounds : Bounds s base d w) : (Fin.ofNat (2^w) base).val = base := by
  have h := bounds.fit
  rw [limit_eq] at h
  exact Nat.mod_eq_of_lt (by omega)

private theorem transfer_at (bounds : Bounds s base d w) (id : Option StageId) (m : Memory w) (a : ℕ)
    (other : a ≠ base) : LiveStageLink.transferMemory (Fin.ofNat _ base) id m a = m a := by
  cases id with
  | none => rfl
  | some _ => exact ite_eq_right (by simpa only [base_val bounds] using other)

/-- The descriptor output contains the requested offset and length, with only the tag and those
two scratch cells allowed to change. -/
structure Prepared (s : Sizes) (base : ℕ) (iv : ℕ × ℕ) (before out : Memory w) : Prop where
  offset : (out (offsetAddr base)).val = iv.1
  count : (out (countAddr base)).val = iv.2
  frame : ∀ addr, addr ≠ base → addr ≠ offsetAddr base → addr ≠ countAddr base → out addr = before addr

private theorem descriptor_prefix (bounds : Bounds s base d w) {m : Memory w}
    (src : Sources s base d hw advice cuts g tag m) (k : Fin 8) :
    ∃ x out, x.Good s ∧ StagePrefix s base (some (descId k)) m [x] (some (scanId k)) out ∧
      Prepared s base (interval s g tag (key k).1 (key k).2) m out ∧
      Sources s base d hw advice cuts g tag out := by
  let side := (key k).1
  let f := (key k).2
  let W := incidentWidth (Δ := s.delta) side g
  have hblock : W = 0 ∨ s.delta ≤ W := width_ge_block _ _ _
  obtain ⟨o,l,hoff,hlen,run⟩ := descriptor_run s base side f m (by omega : 0 < w)
    (scalarFit_of_limit bounds.fit.le) W tag.code.val (firstHalfFlag g) (decide (g.val+1 = 2^s.h+1))
    (src.width side) src.mode src.half src.firstTail bounds.exponents bounds.config hblock
  obtain ⟨x,_,good,history⟩ := run.prefix (descId k) (stage_desc k) rfl
  rw [next_desc] at history
  let mid := writeMemory (writeMemory m (Fin.ofNat _ (offsetAddr base)) o) (Fin.ofNat _ (countAddr base)) l
  let out := LiveStageLink.transferMemory (Fin.ofNat _ base) (some (scanId k)) mid
  have fit := bounds.fit
  rw [limit_eq] at fit
  have ho : (Fin.ofNat (2^w) (offsetAddr base)).val = offsetAddr base := Nat.mod_eq_of_lt (by unfold offsetAddr; omega)
  have hc : (Fin.ofNat (2^w) (countAddr base)).val = countAddr base := Nat.mod_eq_of_lt (by unfold countAddr; omega)
  have prepared : Prepared s base (interval s g tag side f) m out := by
    constructor
    · rw [show out (offsetAddr base) = mid (offsetAddr base) from transfer_at bounds _ _ _ (by unfold offsetAddr; omega)]
      simp only [mid,writeMemory,ho,hc,ite_eq_right (show offsetAddr base ≠ countAddr base by unfold offsetAddr countAddr; omega),ite_true]
      exact hoff
    · rw [show out (countAddr base) = mid (countAddr base) from transfer_at bounds _ _ _ (by unfold countAddr; omega)]
      simp only [mid,writeMemory,hc,ite_true]
      exact hlen
    · intro a hb h₁ h₂
      rw [show out a = mid a from transfer_at bounds _ _ _ hb]
      simp only [mid,writeMemory,ho,hc,ite_eq_right h₁,ite_eq_right h₂]
  exact ⟨x,out,good,history,prepared,src.congr bounds.scratch (fun a hb h₁ h₂ _ => prepared.frame a hb h₁ h₂)⟩

private theorem scan_prefix {id : StageId} {st : Stage} (hid : stage id = st) {m : Memory w} {rs : List (Report w)}
    (run : runSegment ((stageTemplate st).2.instantiate w (rowData w s base st)).program 25
        (some 0) m (List.replicate (calls s st) []) = some rs)
    (last : endState (some 0) rs = none) (len : rs.length = calls s st)
    (hp : ∀ r ∈ rs, r.probes ≤ probes st) (frame : LiveStageLink.PreservesTag (Fin.ofNat _ base) rs) :
    ∃ x, x.Good s ∧ StagePrefix s base (some id) m [x] (next id)
      (LiveStageLink.transferMemory (Fin.ofNat _ base) (next id) (after m (eventLog rs))) := by
  let x : StageTrace w := ⟨id,25,List.replicate (calls s st) [],rs⟩
  have he : x.Exec s base m := by
    constructor
    · change runSegment ((stageTemplate (stage id)).2.instantiate w (rowData w s base (stage id))).program
        25 (some 0) m (List.replicate (calls s st) []) = some rs
      rw [hid]; exact run
    · exact last
    · exact frame.onReturns m
  have hgood : x.Good s := by
    change 25 ≤ 40 ∧ _ = List.replicate (calls s (stage id)) [] ∧ rs.length = calls s (stage id) ∧ _
    rw [hid]
    exact ⟨by decide,rfl,len,hp⟩
  exact ⟨x,hgood,StagePrefix.single he⟩

private theorem pair_prefix (bounds : Bounds s base d w) {m : Memory w}
    (src : Sources s base d hw advice cuts g tag m) (k : Fin 8)
    (valid : (key k).2 = .padding → ValidPadding s cuts g tag (key k).1) :
    ∃ xs out, (∀ x ∈ xs, x.Good s) ∧ StagePrefix s base (startId k.val) m xs (startId (k.val+1)) out ∧
      FieldEffect s base cuts g tag (key k).1 (key k).2 m out := by
  let side := (key k).1
  let f := (key k).2
  let iv := interval s g tag side f
  obtain ⟨x,mid,hx,pre,prepared,srcMid⟩ := descriptor_prefix bounds src k
  have inside : iv.1+iv.2 ≤ incidentWidth (Δ := s.delta) side g := interval_inside _ _ _ _ _ bounds.exponents bounds.config
  have sites : iv.1+iv.2 ≤ 2^d := inside.trans ((cut_width_le_capacity s _).trans bounds.sites)
  have hcap := interval_capacity s g tag side f
  have finish {y : StageTrace w} {out : Memory w} (hy : y.Good s)
      (second : StagePrefix s base (some (scanId k)) mid [y] (startId (k.val+1)) out)
      (effect : FieldEffect s base cuts g tag side f m out) :
      ∃ xs out, (∀ x ∈ xs, x.Good s) ∧ StagePrefix s base (startId k.val) m xs (startId (k.val+1)) out ∧
        FieldEffect s base cuts g tag side f m out := by
    refine ⟨[x]++[y],out,?_,by simpa only [start_at] using pre.append second,effect⟩
    intro z hz
    rcases List.mem_append.mp hz with a | b
    · exact (List.mem_singleton.mp a) ▸ hx
    · exact (List.mem_singleton.mp b) ▸ hy
  by_cases pad : f = .padding
  · have zero := (srcMid.headers.zeroSlice side iv sites inside).mpr (by change Physical.ZeroSlice _ (interval s g tag side f); rw [pad]; exact valid pad)
    obtain ⟨rs,run,last,hm,len,hp,frame⟩ := ScanRows.padding_run hw s base d bounds.fit bounds.scratch side
      mid iv sites (pad ▸ hcap) prepared.offset prepared.count zero
    have hid : stage (scanId k) = .scan side .padding := (stage_scan k).trans (congrArg (Stage.scan side) pad)
    obtain ⟨y,hy,second⟩ := scan_prefix (s := s) (base := base) hid run last len hp frame
    rw [next_scan] at second
    apply finish hy second
    constructor
    · exact fun hn => (hn pad).elim
    · intro a hb ho hc _
      rw [transfer_at bounds _ _ _ hb,hm,prepared.frame a hb ho hc]
  · obtain ⟨rs,run,last,copy,len,hp,frame⟩ := ScanRows.copy_run hw s base d bounds.fit bounds.scratch side f
      pad mid iv sites hcap prepared.offset prepared.count
    obtain ⟨y,hy,second⟩ := scan_prefix (s := s) (base := base) (stage_scan k) run last len hp frame
    rw [next_scan] at second
    have hd := before_destination s base side f pad
    have read := (copy.physical srcMid.headers side iv _ sites (bounds.scratch.trans (by omega))).1
    apply finish hy second
    constructor
    · intro _
      exact read.congr (fun j _ => transfer_at bounds _ _ _ (by omega))
    · intro a hb ho hc safe
      rw [transfer_at bounds _ _ _ hb,copy.frame a (safe.resolve_left pad),prepared.frame a hb ho hc]

/-- Execute all descriptor/scan pairs whose indices precede the cursor.
The reachable image is strong enough to continue at the next pair. -/
theorem reach (bounds : Bounds s base d w) {m : Memory w} (src : Sources s base d hw advice cuts g tag m)
    (n : ℕ) (le : n ≤ 8) (valid : ∀ k : Fin 8, k.val < n → (key k).2 = .padding → ValidPadding s cuts g tag (key k).1) :
    ∃ xs out, (∀ x ∈ xs, x.Good s) ∧ StagePrefix s base (startId 0) m xs (startId n) out ∧
      Sources s base d hw advice cuts g tag out ∧ Image s base cuts g tag n m out := by
  induction n with
  | zero => exact ⟨[],m,by simp,.nil _ _,src,Image.initial ..⟩
  | succ n ih =>
    let k : Fin 8 := ⟨n,by omega⟩
    obtain ⟨xs,mid,good,history,srcMid,img⟩ := ih (by omega) (fun j hj => valid j (by omega))
    obtain ⟨ys,out,good',second,effect⟩ := pair_prefix bounds srcMid k (valid k (by dsimp [k]; omega))
    refine ⟨xs++ys,out,?_,history.append second,srcMid.afterField bounds.scratch _ _ effect,img.advance k effect⟩
    intro z hz
    exact (List.mem_append.mp hz).elim (good z) (good' z)

/-- From the actual post-index, post-mode and post-primed memory, all sixteen
remaining stages accept on canonical padding, yielding every copied field
and the complete frame outside the occupied fields and three admin cells. -/
theorem suffix_native (bounds : Bounds s base d w) {m : Memory w} (src : Sources s base d hw advice cuts g tag m)
    (valid : ∀ side, ValidPadding s cuts g tag side) :
    ∃ xs out, (∀ x ∈ xs, x.Good s) ∧ StagePrefix s base (some (⟨15,by decide⟩ : StageId)) m xs none out ∧
      StageRuns s base (some (⟨15,by decide⟩ : StageId)) m xs ∧ Sources s base d hw advice cuts g tag out ∧
      Image s base cuts g tag 8 m out := by
  obtain ⟨xs,out,good,pre,source,img⟩ := reach bounds src 8 le_rfl (fun k _ _ => valid (key k).1)
  have final : StagePrefix s base (some (⟨15,by decide⟩ : StageId)) m xs none out := pre
  exact ⟨xs,out,good,final,by simpa using final.finish (.done out),source,img⟩

/-- Reach a malformed padding scan after a valid prefix. Its entry retains
the actual headers and the offset/count words of the failing descriptor. -/
theorem bad_prefix_at (bounds : Bounds s base d w) {m : Memory w} (src : Sources s base d hw advice cuts g tag m)
    (k : Fin 8) (pad : (key k).2 = .padding) (bad : ¬ ValidPadding s cuts g tag (key k).1)
    (earlier : ∀ i : Fin 8, i.val < k.val → (key i).2 = .padding → ValidPadding s cuts g tag (key i).1) :
    ∃ xs mid, (∀ x ∈ xs, x.Good s) ∧ StagePrefix s base (startId 0) m xs (some (scanId k)) mid ∧
      Sources s base d hw advice cuts g tag mid ∧
      (mid (offsetAddr base)).val = (interval s g tag (key k).1 .padding).1 ∧
      (mid (countAddr base)).val = (interval s g tag (key k).1 .padding).2 ∧
      ¬ Allocated.ZeroPad (cutSlot (key k).1) (interval s g tag (key k).1 .padding) mid := by
  obtain ⟨xs,m',hg,pre,src',_⟩ := reach bounds src k.val k.isLt.le earlier
  obtain ⟨x,mid,hx,desc,prepared,srcMid⟩ := descriptor_prefix bounds src' k
  rw [start_at k] at pre
  have inside := interval_inside s g tag (key k).1 .padding bounds.exponents bounds.config
  have sites := inside.trans ((cut_width_le_capacity s _).trans bounds.sites)
  refine ⟨xs++[x],mid,?_,pre.append desc,srcMid,?_,?_,?_⟩
  · intro y hy
    rcases List.mem_append.mp hy with prev | last
    · exact hg y prev
    · exact (List.mem_singleton.mp last) ▸ hx
  · simpa only [pad] using prepared.offset
  · simpa only [pad] using prepared.count
  · exact mt (srcMid.headers.zeroSlice (key k).1 _ sites inside).mp bad

/-- Choose the first malformed side in the actual public order. -/
theorem first_bad_padding (bad : ¬ ∀ side, ValidPadding s cuts g tag side) :
    ∃ k : Fin 8, (key k).2 = .padding ∧ ¬ ValidPadding s cuts g tag (key k).1 ∧
      ∀ i : Fin 8, i.val < k.val → (key i).2 = .padding → ValidPadding s cuts g tag (key i).1 := by
  by_cases left : ValidPadding s cuts g tag .left
  · have right : ¬ ValidPadding s cuts g tag .right := fun hr => bad (fun side => by cases side <;> assumption)
    refine ⟨7,rfl,right,?_⟩
    intro i hi he
    fin_cases i <;> first | exact left | contradiction
  · refine ⟨3,rfl,left,?_⟩
    intro i hi he
    fin_cases i <;> contradiction

/-- A malformed padding bit leads to a scheduled native scan at which no
choice tape and no fuel bound can produce an accepting exit. -/
theorem bad_prefix (bounds : Bounds s base d w) {m : Memory w} (src : Sources s base d hw advice cuts g tag m)
    (bad : ¬ ∀ side, ValidPadding s cuts g tag side) :
    ∃ (side : Side) (id : StageId) (xs : List (StageTrace w)) (mid : Memory w), stage id = .scan side .padding ∧ (∀ x ∈ xs, x.Good s) ∧
      StagePrefix s base (startId 0) m xs (some id) mid ∧
      ∀ fuel bits rs, runSegment ((stageTemplate (stage id)).2.instantiate w (rowData w s base (stage id))).program
        fuel (some 0) mid bits = some rs → endState (some 0) rs ≠ none := by
  obtain ⟨k,pad,invalid,earlier⟩ := first_bad_padding bad
  obtain ⟨xs,mid,good,pre,_,hoff,hcount,hbad⟩ := bad_prefix_at bounds src k pad invalid earlier
  let side := (key k).1
  let iv := interval s g tag side .padding
  have hid : stage (scanId k) = .scan side .padding := (stage_scan k).trans (congrArg (Stage.scan side) pad)
  refine ⟨side,scanId k,xs,mid,hid,good,pre,?_⟩
  intro fuel bits rs run last
  rw [hid] at run
  exact hbad (ScanRows.padding_sound_any hw s base d bounds.fit bounds.scratch side mid iv
    ((interval_inside s g tag side .padding bounds.exponents bounds.config).trans ((cut_width_le_capacity s _).trans bounds.sites))
    (interval_capacity s g tag side .padding) hoff hcount fuel bits run last)

end LiveHeaderProgram.Fields

end VPVNP
end Computability
end OAI
