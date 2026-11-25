import OAI.Hierarchy.ProbeStageVisit

namespace OAI
/-! # A complete native subdivision level, from one parent matching to its child -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section

private theorem bank_frame {n w src : ℕ} {b : Bank} {f : Fin n → ℕ} {m o : Memory w}
    (resident : Resident b m f) (end_ : b.base+b.size ≤ src) (frame : ∀ a<src,o a=m a) :
    Resident b o f := by
  intro i
  change o (b.base+(i.val:Word w).val%b.size)=_
  have bounded : (i.val : Word w).val % b.size < b.size := Nat.mod_lt _ (Nat.two_pow_pos b.bits)
  exact (frame _ ((Nat.add_lt_add_left bounded b.base).trans_le end_)).trans (resident i)

theorem ParentStored.frame {h d j w : ℕ} {π : Equiv.Perm (Fin (2^h))} {m o : Memory w}
    (p : ParentStored d π j m) (frozen : ∀ a<phase h d copies j,o a=m a) :
    ParentStored d π j o :=
  ⟨bank_frame p.group (parent_end ..) frozen,bank_frame p.source (parent_end ..) frozen,
    bank_frame p.target (parent_end ..) frozen⟩

theorem geometry_interval {h d : ℕ} (x : GeometryCell h d) :
    bankBase h d copies x.1.val 3≤x.address copies ∧ x.address copies<allocatorBase h d copies x.1.val := by
  have lo := Nat.mul_le_mul_right (extent h d) (Nat.le_add_right 3 x.2.1.val)
  have hi := separate h d copies x.1.val (3+x.2.1.val) 11 (by omega)
  refine ⟨by unfold GeometryCell.address bankBase;omega,?_⟩
  exact (Nat.add_lt_add_left x.2.2.isLt _).trans_le hi

private theorem endpoint_frame {h d j w : ℕ} (m : Memory w) {a : ℕ}
    (off : a<allocatorBase h d copies j ∨ allocatorBase h d copies j+3*2^h≤a) :
    result (prepareRows h d j) m a=m a := by
  apply columns_frame
  simpa using off

private theorem emitted_frame {h d j w : ℕ} (m : Memory w) {a : ℕ}
    (off : a<output h d copies j ∨ output h d copies j+9*2^h≤a) : result (writeRows h d j) m a=m a := by
  apply columns_frame
  simpa using off

structure PhaseResult {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (m : Memory (wordBits h d copies)) : Prop where
  child : ParentStored d π (j.val+1) (levelImage h d j.val m)
  output : ∀ (r : Fin (2^h)) (k : Fin 9),levelImage h d j.val m (Native.output h d copies j.val+k.val*2^h+r.val)=
    (rowWords (history h d π j.val).tiles (radix_pos h d) (assigned j π) (history h d π j.val).encode r k : Word _)
  scans : ∀ r : Fin (2^h),rowScans h d j.val r.val (prior h d j.val m r.val)≤expectedScans h d π j.val r
  clears : ∀ r : Fin (2^h),rowClears h d j.val r.val (prior h d j.val m r.val)≤expectedClears h d π j.val r
  frame : ∀ a,a<phase h d copies j.val ∨ phase h d copies (j.val+1)≤a → levelImage h d j.val m a=m a

theorem phase_result {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (m : Memory (wordBits h d copies)) (geom : GeometryStored (h:=h) j m) (p : ParentStored d π j.val m)
    (arrays : allArrays h d _ j m) (body : RowCorrect hd π j) : PhaseResult π j m := by
  let pre := result (prepareRows h d j.val) m
  have preArr : allArrays h d _ j pre := by
    intro k i hi
    have space := allocator_end h d copies j.val
    have later : bankBase h d copies j.val 14≤region h d j.val k+i := by unfold region bankBase;omega
    exact (endpoint_frame m (Or.inr (space.trans later))).trans (arrays k i hi)
  have ids : EndpointWords π j pre := prepare_endpoint_words hd π j m geom p
  have v := visit_records hd π j pre (initial_prefix hd π j pre preArr) preArr.immutable ids body (2^h) le_rfl
  let last := records h d j.val pre (2^h)
  have early (a : ℕ) (low : a<phase h d copies j.val) : last a=m a := by
    have old : pre a=m a := endpoint_frame m (Or.inl (low.trans_le (Nat.le_add_right _ _)))
    exact (v.frame a (fun _ _ may => low.not_ge (mayWrite_region may).1)).trans old
  have slots : GeometryStored (h:=h) j last := by
    intro c i
    let x : GeometryCell h d := ⟨j,c,i⟩
    obtain ⟨lo,high⟩ := geometry_interval x
    have later : allocatorBase h d copies j.val≤bankBase h d copies j.val 14 :=
      (Nat.le_add_right _ _).trans (separate h d copies j.val 11 14 (by decide))
    have absent : ∀ (r : Fin (2^h)),r.val<2^h → ¬ MayWrite h d j.val r (x.address copies) := by
      intro r _ may
      rcases (mayWrite_region may).2.2 with small|big
      · exact (Nat.not_lt_of_ge lo) small
      · exact (high.trans_le later).not_ge big
    exact (v.frame _ absent).trans ((endpoint_frame m (Or.inl high)).trans (geom c i))
  obtain ⟨_,child,outputs⟩ := publish hd π j last slots (p.frame early) v.ranks
  refine ⟨child,outputs,fun r => v.scans _ r.isLt,fun r => v.clears _ r.isLt,?_⟩
  intro a bound
  have finish := output_end h d copies j.val
  obtain low|high := bound
  · have before : a<output h d copies j.val := low.trans_le (Nat.le_add_right _ _)
    exact (emitted_frame last (Or.inl before)).trans (early a low)
  · have e := (emitted_frame last (Or.inr (finish.trans high)))
    have r := v.frame a (fun _ _ hit => ((mayWrite_region hit).2.1).not_ge
      ((Nat.le_add_right _ _).trans (finish.trans high)))
    have before := allocator_end h d copies j.val
    have mid := separate h d copies j.val 14 (stride d copies-9) (by unfold stride;omega)
    change _≤output h d copies j.val at mid
    exact e.trans (r.trans (endpoint_frame m (Or.inr (by omega))))

end
end Hierarchy.ProbeStage.Native

end OAI
