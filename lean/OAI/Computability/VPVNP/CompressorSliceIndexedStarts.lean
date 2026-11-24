import OAI.Computability.VPVNP.CompressorSliceSchedule

/-!
# Interval frames from precomputed field starts

The sorted shrinking-bundle tables already contain field starts. Read them
directly during the pair scan, then index each positive frame at both ends.
A row occupies consecutive count cells, frames and endpoint-reference cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.IndexedStarts

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SliceRAM SliceSchedule

variable {w : ℕ}

/-- Workspace size for the endpoint counts, three-word pair frames, and references at both
endpoints. -/
def capacity (m n : ℕ) := m+n+5*(m*n)

/-- Public operands for the pair scan, including the four input columns and the base of the
output frames. -/
def pair (input : Fin 4 → Word w) (B : Word w) (m n : ℕ) : Fin 6 → Word w :=
  ![Fin.ofNat _ n,input 0,input 1,input 2,input 3,Fin.ofNat _ (B.val+m+n)]

/-- Public operands for indexing the pair frames in the source and target adjacency
directories. -/
def adj (B : Word w) (m n : ℕ) : Fin 7 → Word w :=
  ![Fin.ofNat _ n,Fin.ofNat _ m,Fin.ofNat _ (B.val+m+n),B,
    Fin.ofNat _ (B.val+m+n+3*(m*n)),Fin.ofNat _ (B.val+m),Fin.ofNat _ (B.val+m+n+4*(m*n))]

/-- The input columns end before the workspace and its exclusive end fits in a machine word. -/
structure Space (input : Fin 4 → Word w) (B : Word w) (m n : ℕ) : Prop where
  fits : B.val+capacity m n < 2^w
  reads : ∀ i : Fin 4, (input i).val+(if i.val < 2 then m else n) ≤ B.val

private theorem adj_vals {input : Fin 4 → Word w} {B : Word w} {m n : ℕ}
    (h : Space input B m n) :
    let p := adj B m n
    (p 0).val = n ∧ (p 1).val = m ∧ (p 2).val = B.val+m+n ∧ p 3 = B ∧
      (p 4).val = B.val+m+n+3*(m*n) ∧ (p 5).val = B.val+m ∧ (p 6).val = B.val+m+n+4*(m*n) := by
  have hf := h.fits
  unfold capacity at hf
  exact ⟨Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),rfl,
    Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)⟩

private theorem pair_space {input : Fin 4 → Word w} {B : Word w} {m n : ℕ}
    (h : Space input B m n) : FrameSpace (pair input B m n) m n := by
  have hf := h.fits
  unfold capacity at hf
  have hb : ((pair input B m n) 5).val = B.val+m+n := Nat.mod_eq_of_lt (by omega)
  constructor
  · exact Nat.mod_eq_of_lt (by omega)
  · omega
  · intro i; have hi := h.reads i; fin_cases i <;> exact hi.trans B.isLt.le
  · rw [hb]; omega
  · intro i; left
    rw [hb]
    have hi := h.reads i
    fin_cases i <;> exact hi.trans (by omega)

private theorem adj_space {input : Fin 4 → Word w} {B : Word w} {m n : ℕ}
    (h : Space input B m n) : AdjRegions (adj B m n) := by
  obtain ⟨n',m',a,b,c,d,e⟩ := adj_vals h
  have hf := h.fits
  dsimp [capacity] at hf
  constructor <;> simp only [oldBank,newBank,AdjBank.stop,n',m',a,b,c,d,e,Nat.mul_comm n m] <;> omega

/-- Logs of the count clearing, pair-frame construction, and endpoint indexing sweeps. -/
structure Reports (w : ℕ) where
  /-- Reports emitted while clearing the source and target count cells. -/
  clear : List (Report w)
  /-- Reports emitted while computing the copy frame for every field pair. -/
  pairs : List (Report w)
  /-- Reports emitted while appending positive-length frame references at both endpoints. -/
  refs : List (Report w)

/-- Memory after replaying the count-clearing sweep. -/
def Reports.cleared (rs : Reports w) (m : Memory w) := after m (eventLog rs.clear)
/-- Memory after the cleared workspace has been filled with the pair frames. -/
def Reports.framed (rs : Reports w) (m : Memory w) := after (rs.cleared m) (eventLog rs.pairs)
/-- Concatenate the clearing, frame, and reference reports in execution order. -/
def Reports.all (rs : Reports w) := rs.clear ++ rs.pairs ++ rs.refs

/-- The three native scans produce the supplied reports on empty choice tapes, each starting in
its predecessor's memory. -/
structure Native (input : Fin 4 → Word w) (B : Word w) (m n : ℕ)
    (mem : Memory w) (rs : Reports w) : Prop where
  clear : runSegment ((template clearOps 0).instantiate w (fun _ => B)).program 8 (some 0) mem
    (List.replicate (m+n) []) = some rs.clear
  pairs : runSegment (IndexedPair.table.instantiate w (pair input B m n)).program 38 (some 0)
    (rs.cleared mem) (List.replicate (m*n) []) = some rs.pairs
  refs : runSegment (adjTemplate.instantiate w (adj B m n)).program 36 (some 0)
    (rs.framed mem) (List.replicate (m*n) []) = some rs.refs

/-- All offsets and incidence lists of one completed row. Its frame fields
occupy three words at each source-major pair index. -/
structure Stored (B : Word w) (old new : List ℕ) (mem : Memory w) : Prop where
  lengths : ∀ k, k < old.length*new.length →
    (mem (B.val+old.length+new.length+3*k+2)).val = (sliceAt old new k).length
  offsets : ∀ k, k < old.length*new.length → 0 < (sliceAt old new k).length →
    (mem (B.val+old.length+new.length+3*k)).val = (sliceAt old new k).sourceOffset ∧
    (mem (B.val+old.length+new.length+3*k+1)).val = (sliceAt old new k).targetOffset
  oldRows : (oldBank (adj B old.length new.length)).Represents mem
    (fun k => (sliceAt old new k).length) (· / new.length) (old.length*new.length)
  newRows : (newBank (adj B old.length new.length)).Represents mem
    (fun k => (sliceAt old new k).length) (· % new.length) (old.length*new.length)

/-- All reads used by the interval record and both endpoint lists lie in the
row's allocated bank. Thus a subsequent disjoint row preserves the entire
stored interpretation. -/
theorem Stored.transfer {input : Fin 4 → Word w} {B : Word w} {old new : List ℕ} {s t : Memory w}
    (space : Space input B old.length new.length) (h : Stored B old new s)
    (same : ∀ x, B.val ≤ x → x < B.val+capacity old.length new.length → t x = s x) :
    Stored B old new t := by
  let q := adj B old.length new.length
  obtain ⟨hn,hm,hf,hc,hr,hc',hr'⟩ := adj_vals space
  have fit := space.fits
  dsimp [capacity] at fit
  have fitOld : (oldBank q).Fits := by
    constructor <;> simp only [oldBank,q,AdjBank.stop,hn,hm,hc,hr] <;> omega
  have fitNew : (newBank q).Fits := by
    constructor <;> simp only [newBank,q,AdjBank.stop,hn,hm,hc',hr',Nat.mul_comm new.length old.length] <;> omega
  constructor
  · intro k hk
    rw [same _ (by omega) (by unfold capacity; omega)]
    exact h.lengths k hk
  · intro k hk hpos
    rw [same _ (by omega) (by unfold capacity; omega),same _ (by omega) (by unfold capacity; omega)]
    exact h.offsets k hk hpos
  · apply AdjBank.represents_congr fitOld h.oldRows
    · intro v _
      change _ ≤ (adj B old.length new.length 0).val
      rw [hn]; exact adjPrefix_old_le _ le_rfl
    · intro x hx
      simp only [oldBank,q,AdjBank.Inside,AdjBank.stop,hn,hm,hc,hr] at hx
      exact same x (by omega) (by unfold capacity; omega)
  · apply AdjBank.represents_congr fitNew h.newRows
    · intro v _
      change _ ≤ (adj B old.length new.length 1).val
      rw [hm]; exact adjPrefix_new_le _ le_rfl
    · intro x hx
      simp only [newBank,q,AdjBank.Inside,AdjBank.stop,hn,hm,hc',hr',Nat.mul_comm new.length old.length] at hx
      exact same x (by omega) (by unfold capacity; omega)

/-- The clearing, intersection and directory passes are deterministic and
work from arbitrary stale output rows. The two input prefixes are reused. -/
theorem build (old new : List ℕ) (input : Fin 4 → Word w) (B : Word w) (mem : Memory w)
    (space : Space input B old.length new.length)
    (hs : old.sum < 2^w) (ht : new.sum < 2^w)
    (h : Inputs (pair input B old.length new.length) old new mem) :
    let m := old.length
    let n := new.length
    ∃ rs, Native input B m n mem rs ∧
      Stored B old new (after mem (eventLog rs.all)) ∧
      (∀ x, x < B.val ∨ B.val+capacity m n ≤ x → after mem (eventLog rs.all) x = mem x) ∧
      rs.all.length = m+n+2*(m*n) ∧
      (rs.all.map Report.probes).sum ≤ m+n+14*(m*n) ∧
      (rs.all.map fun r => r.events.length+1).sum ≤ 8*(m+n)+74*(m*n) := by
  intro m n
  let p := pair input B m n
  let q := adj B m n
  let len := fun k => (sliceAt old new k).length
  have hf := space.fits
  change B.val+(m+n+5*(m*n)) < 2^w at hf
  obtain ⟨hn,hm,hframe,hc,hr,hc',hr'⟩ := adj_vals space
  change (q 0).val = n at hn
  change (q 1).val = m at hm
  change (q 2).val = B.val+m+n at hframe
  change q 3 = B at hc
  change (q 4).val = B.val+m+n+3*(m*n) at hr
  change (q 5).val = B.val+m at hc'
  change (q 6).val = B.val+m+n+4*(m*n) at hr'
  obtain ⟨clear,cr,zero,cout,_,cl,cw⟩ := clearPass_run B (m+n) (by omega) (by omega) mem
  let initial := after mem (eventLog clear)
  have same (j : Fin 4) (i : ℕ) (hi : i < (if j.val < 2 then m else n)) :
      initial ((input j).val+i) = mem ((input j).val+i) := by
    have hfit := space.reads j
    apply cout
    left
    change (input j).val + (if j.val < 2 then m else n) ≤ B.val at hfit
    omega
  have hi : Inputs p old new initial := by
    constructor <;> intro i hi
    · exact (congrArg Fin.val (same 0 i hi)).trans (h.oldStart i hi)
    · exact (congrArg Fin.val (same 1 i hi)).trans (h.oldWidth i hi)
    · exact (congrArg Fin.val (same 2 i hi)).trans (h.newStart i hi)
    · exact (congrArg Fin.val (same 3 i hi)).trans (h.newWidth i hi)
  have start : FramesAt p old new initial initial 0 := ⟨hi,fun _ hj => by omega,fun _ hj _ => by omega,fun _ _ => rfl⟩
  obtain ⟨pairs,pr,fr,_,pl,pp,pi⟩ := frameSegment_run (pair_space space) hs ht start (m*n) (by simp [m,n])
  simp only [Nat.zero_add] at fr
  let mid := after initial (eventLog pairs)
  change FramesAt p old new initial mid (m*n) at fr
  have hhead : (p 5).val = B.val+m+n := Nat.mod_eq_of_lt (by omega)
  have sq := adj_space space
  change AdjRegions q at sq
  have lengths (k : ℕ) (hk : k < (q 1).val*(q 0).val) : (mid ((q 2).val+3*k+2)).val = len k := by
    rw [hframe,← hhead]
    exact fr.lengths k (by simpa only [hm,hn] using hk)
  have z₀ (i : Word w) (hi : i < q 1) : mid (adjOldCount q i).val = 0 := by
    have hv : i.val < m := lt_of_lt_of_eq (Fin.lt_def.mp hi) hm
    have eqn : (adjOldCount q i).val = B.val+i.val := by rw [adjOldCount,Fin.val_add,hc,Nat.mod_eq_of_lt (by omega)]
    rw [eqn,fr.outside _ (Or.inl (by rw [hhead]; omega))]
    exact zero _ (by omega) (by omega)
  have z₁ (i : Word w) (hi : i < q 0) : mid (adjNewCount q i).val = 0 := by
    have hv : i.val < n := lt_of_lt_of_eq (Fin.lt_def.mp hi) hn
    have eqn : (adjNewCount q i).val = B.val+m+i.val := by rw [adjNewCount,Fin.val_add,hc',Nat.mod_eq_of_lt (by omega)]
    rw [eqn,fr.outside _ (Or.inl (by rw [hhead]; omega))]
    exact zero _ (by omega) (by omega)
  obtain ⟨refs,rr,done,_,rl,rp,ri⟩ := adjPass_run sq lengths z₀ z₁
  change runSegment (adjTemplate.instantiate w q).program 36 (some 0) mid
    (List.replicate ((q 1).val*(q 0).val) []) = some refs at rr
  let post := after mid (eventLog refs)
  change AdjAt q len mid post ((q 1).val*(q 0).val) at done
  change refs.length = (q 1).val*(q 0).val at rl
  change RAMBuckets.cost Report.probes refs = 2*((q 1).val*(q 0).val)+6*adjNonempty len 0 ((q 1).val*(q 0).val) at rp
  change (refs.map fun r => r.events.length+1).sum = 12*((q 1).val*(q 0).val)+24*adjNonempty len 0 ((q 1).val*(q 0).val) at ri
  rw [hm,hn] at rr done rl rp ri
  let rs : Reports w := ⟨clear,pairs,refs⟩
  have replay : after mem (eventLog rs.all) = post := by
    simp only [rs,Reports.all,post,mid,initial,after,eventLog,List.flatMap_append,List.foldl_append]
  have live (x : ℕ) (lo : B.val+m+n ≤ x) (up : x < B.val+m+n+3*(m*n)) : post x = mid x := by
    exact done.frame_eq sq (by simpa only [hframe] using lo) (by simpa only [hm,hn,hframe] using up)
  refine ⟨rs,⟨cr,pr,rr⟩,?_,?_,?_,?_,?_⟩
  · rw [replay]
    constructor
    · intro k hk
      change k < m*n at hk
      rw [live _ (by dsimp [m,n]; omega) (by dsimp [m,n] at *; omega),← hhead]
      exact fr.lengths k hk
    · intro k hk hl
      change k < m*n at hk
      change (post (B.val+m+n+3*k)).val = _ ∧ (post (B.val+m+n+3*k+1)).val = _
      rw [live _ (by omega) (by omega),live _ (by omega) (by omega),← hhead]
      exact fr.offsets k hk hl
    · simpa only [hn] using done.oldRows
    · simpa only [hn] using done.newRows
  · intro x hx
    rw [replay]
    have out : ¬ (oldBank q).Inside x ∧ ¬ (newBank q).Inside x := by
      simp only [oldBank,newBank,AdjBank.Inside,AdjBank.stop,hm,hn,hc,hc',hr,hr',Nat.mul_comm n m]
      dsimp [capacity] at hx
      omega
    rw [done.outside _ out.1 out.2,fr.outside _ (by rw [hhead]; dsimp [capacity] at hx; omega)]
    exact cout _ (by dsimp [capacity] at hx; omega)
  · simp only [rs,Reports.all,List.length_append,cl,pl,rl]; omega
  · have cp : (clear.map Report.probes).sum = m+n := by
      rw [show clear.map Report.probes = List.replicate clear.length 1 from
        List.map_eq_replicate_iff.mpr (fun x hx => (cw x hx).1)]; simp [cl]
    have e := emitted_all old new
    have eb := copyRecords_length_le old new
    have ub : adjNonempty len 0 (m*n) ≤ m*n :=
      (List.length_filter_le ..).trans (by simp)
    rw [adjCost_eq_length_add_probes,rl] at rp
    change emitted old new 0 (m*n) = _ at e
    change (copyRecords old new).length ≤ m*n at eb
    change (pairs.map Report.probes).sum = 5*(m*n)+2*emitted old new 0 (m*n) at pp
    change (pairs.map fun r => r.events.length+1).sum = 34*(m*n)+4*emitted old new 0 (m*n) at pi
    simp only [rs,Reports.all,List.map_append,List.sum_append,cp]
    omega
  · have cc : (clear.map fun x => x.events.length+1).sum = (m+n)*8 := by
      rw [show (clear.map fun x => x.events.length+1) = List.replicate clear.length 8 from
        List.map_eq_replicate_iff.mpr (fun x hx => (cw x hx).2)]; simp [cl]
    have e := emitted_all old new
    have eb := copyRecords_length_le old new
    have ub : adjNonempty len 0 (m*n) ≤ m*n :=
      (List.length_filter_le ..).trans (by simp)
    change emitted old new 0 (m*n) = _ at e
    change (copyRecords old new).length ≤ m*n at eb
    change (pairs.map Report.probes).sum = 5*(m*n)+2*emitted old new 0 (m*n) at pp
    change (pairs.map fun r => r.events.length+1).sum = 34*(m*n)+4*emitted old new 0 (m*n) at pi
    simp only [rs,Reports.all,List.map_append,List.sum_append,cc]
    omega

end CompressorRecords.IndexedStarts

end VPVNP
end Computability
end OAI
