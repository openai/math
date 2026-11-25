import OAI.Hierarchy.DescentTerminalPacketSlotFrame

namespace OAI
/-! # One native site-relative slot per stable-sorted terminal cohort -/
namespace Hierarchy.DescentTerminalPacketSlotRAM
open DescentTerminalExteriorPackets ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure Computability.BorderVNP.FragmentBucket
open scoped Classical Fin.CommRing
noncomputable section
variable {w n H : ℕ}

def program (b : Bank) (L : ProtocolRAMEndpointSort.Layout) (w n H : ℕ) :=
  (sortedProgram b L H n w).seq (scan w (out L n H) n (expr L n H))

private theorem read_bank (base slots : ℕ) (m : Memory w) (i : Fin slots) (fits : slots < 2^w) :
    (bank base slots).read m (i.val:Word w)=m (base+i.val) := by
  have small:=i.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) slots)
  simp only [Bank.read,Fin.val_cast_of_lt (i.isLt.trans fits),bank,Bank.size,Nat.mod_eq_of_lt small]

theorem slot_fit (L : ProtocolRAMEndpointSort.Layout) (fit : L.Fits w n H)
    (room : out L n H+n < 2^w) : (expr L n H).Fits w (out L n H) := by
  have a:=fit.src_safe;have b:=fit.count_safe;have c:=fit.prefix_safe
  have outRoom : out L n H < 2^w := (Nat.le_add_right (out L n H) n).trans_lt room
  have rowEnd : L.sorted + (bank 0 n).size ≤ out L n H :=
    Nat.le_add_right _ (bank 0 H).size
  have rowSize : (bank 0 n).size < 2^w :=
    ((Nat.le_add_left (bank 0 n).size L.sorted).trans rowEnd).trans_lt outRoom
  have siteSize : (bank 0 H).size < 2^w :=
    (Nat.le_add_left (bank 0 H).size (L.sorted + (bank 0 n).size)).trans_lt outRoom
  have nm (base : ℕ) (lt : base ≤ L.sorted) : (bank base n).Fits w (out L n H) :=
    ⟨Nat.two_pow_pos _,rowSize,(Nat.add_le_add_right lt _).trans rowEnd⟩
  have hm (base : ℕ) (lt : base ≤ L.sorted) : (bank base H).Fits w (out L n H) :=
    ⟨Nat.two_pow_pos _,siteSize,
      Nat.add_le_add_right (lt.trans (Nat.le_add_right L.sorted (bank 0 n).size)) _⟩
  simp only [expr,Expr.Fits]
  exact ⟨trivial,⟨⟨hm _ (by omega),nm _ (by omega),nm _ le_rfl,trivial⟩,
    hm _ (by omega),nm _ (by omega),nm _ le_rfl,trivial⟩⟩

private theorem follow {A B : Procedure w} {m mid z : Memory w} {a b : ℕ}
    (left : A.Exec m mid a ∧ CheapCode A) (right : B.Exec mid z b ∧ CheapCode B) :
    (A.seq B).Exec m z (a+b) ∧ CheapCode (A.seq B) :=
  ⟨Procedure.Exec.then left.1 right.1,@cheap_seq w A B left.2 right.2⟩

/-- The classifier and the slot scan execute for every incoming memory. -/
theorem run (b : Bank) (L : ProtocolRAMEndpointSort.Layout) (m : Memory w) (pos : 0 < H)
    (fit : SortRoom b L w n H) (room : out L n H+n < 2^w) :
    let mid:=sorted b L H n pos m
    (program b L w n H).Exec m (after L n H mid)
      ((4+n*(2*(guard b H).work+4))+ProtocolRAMEndpointSort.cost n H+(4+n*80)) ∧
      CheapCode (program b L w n H) := by
  unfold program
  apply follow (A:=sortedProgram b L H n w) (B:=scan w (out L n H) n (expr L n H))
      (mid:=sorted b L H n pos m) (sort_run b L H n m pos fit)
  exact ⟨@scan_exec w (out L n H) n (expr L n H) (sorted b L H n pos m)
    (slot_fit L fit.fits room) room,@scan_cheap w (out L n H) n (expr L n H)⟩

theorem fee (b : Bank) : (4+n*(2*(guard b H).work+4))+ProtocolRAMEndpointSort.cost n H+(4+n*80) ≤
    31+147*n+18*H := by have paid:=ticks (b:=b) (H:=H) (n:=n);omega

theorem buckets (L : ProtocolRAMEndpointSort.Layout) (fit : L.Fits w n H) (home : Fin n→Fin H)
    (m : Memory w) (s : Fin H) :
    let sorted_:=ProtocolRAMEndpointSort.image L home m
    sorted_ (L.starts+s.val)=((start home s.val+count home s:ℕ):Word w) ∧
    sorted_ (L.counts+s.val)=(count home s:Word w) := by
  have a:=fit.count_safe;have b:=fit.prefix_safe;have hs:=s.isLt
  let hist:=ProtocolRAMSiteCounts.image L.counts home m
  let pre:=ProtocolRAMEndpointPrefix.image L.starts (start home) hist H
  have cursor:=ProtocolRAMEndpointScatter.cursor home L.starts L.sorted pre (by omega)
    (fun t=>ProtocolRAMEndpointPrefix.read L.starts (start home) hist H t.val t.isLt.le) n le_rfl s
  change ProtocolRAMEndpointScatter.image home L.starts L.sorted pre n (L.starts+s.val) = _ ∧ _
  refine ⟨by simpa only [prior_end] using cursor,?_⟩
  exact ((ProtocolRAMEndpointScatter.frame home L.starts L.sorted pre n _ (Or.inl (by omega))
    (Or.inl (by omega))).trans (ProtocolRAMEndpointPrefix.frame L.starts (start home) hist H _
      (Or.inl (by omega)))).trans (ProtocolRAMSiteCounts.bin L.counts home m s)

theorem ordinal_lt (home : Fin n→Fin H) (u : Fin n) : prior home u.val (home u) < count home (home u) := by
  have bound : prior home (u.val+1) (home u) ≤ count home (home u):=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [prior_step home u (home u),ite_eq_left rfl] at bound
  omega

theorem endpoint_le (home : Fin n→Fin H) (s : Fin H) : start home s.val+count home s ≤ n := by
  have mon : Monotone (start home) := fun _ _ lt=>Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono lt) (fun _ _ _=>Nat.zero_le _)
  simpa only [start_step,start_end] using mon s.isLt

theorem relative (L : ProtocolRAMEndpointSort.Layout) (fit : L.Fits w n H) (home : Fin n→Fin H)
    (m : Memory w) (i : Fin n) :
    let u:=(dest home).symm i
    let s:=home u
    let t:=ProtocolRAMEndpointSort.image L home m
    prior home u.val s=i.val-((t (L.starts+s.val)).val-(t (L.counts+s.val)).val) := by
  let u:=(dest home).symm i
  let s:=home u
  have bound:=endpoint_le home s
  have room:=fit.room
  have row:=dest_val home u
  have eqn : (dest home u).val=i.val:=congrArg Fin.val ((dest home).apply_symm_apply i)
  obtain ⟨e,c⟩:=buckets L fit home m s
  dsimp only
  rw [e,c,Fin.val_cast_of_lt (by omega : start home s.val+count home s < 2^w),
    Fin.val_cast_of_lt (by omega : count home s < 2^w)]
  change prior home u.val s=i.val-(start home s.val+count home s-count home s)
  change (dest home u).val=start home s.val+prior home u.val s at row
  omega

theorem scan_read (L : ProtocolRAMEndpointSort.Layout) (fit : L.Fits w n H) (height : H < 2^w)
    (home : Fin n→Fin H) (m : Memory w) (keys_ : ∀u : Fin n,m (L.src+u.val)=((home u).val:Word w))
    (i : Fin n) :
    let u:=(dest home).symm i
    after L n H (ProtocolRAMEndpointSort.image L home m) (out L n H+i.val)=(prior home u.val (home u):Word w) := by
  let t:=ProtocolRAMEndpointSort.image L home m
  let u:=(dest home).symm i
  let s:=home u
  have a:=fit.src_safe;have c:=fit.count_safe;have d:=fit.prefix_safe;have e:=fit.room
  have nFit : n < 2^w:=by omega
  have ordinal : t (L.sorted+i.val)=(u.val:Word w):=ProtocolRAMEndpointSort.read L fit home m i
  have source : t (L.src+u.val)=(s.val:Word w):=by
    have hu:=u.isLt
    exact (ProtocolRAMEndpointSort.frame L fit home m _ (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))).trans (keys_ u)
  obtain ⟨last,cnt⟩:=buckets L fit home m s
  change t (L.starts+s.val) = _ at last
  change t (L.counts+s.val) = _ at cnt
  have emitted : after L n H t (out L n H+i.val)=(expr L n H).eval t (i.val:Word w) :=
    DescentTerminalChipRuntime.image_at t (out L n H) n (expr L n H) i
  rw [emitted]
  simp only [expr,Expr.eval,RowOp.opcode,BinaryOp.eval]
  rw [read_bank L.sorted n t i nFit,ordinal,read_bank L.src n t u nFit,source,
    read_bank L.starts H t s height,read_bank L.counts H t s height,last,cnt]
  have row:=dest_val home u
  have eqn : (dest home u).val=i.val:=congrArg Fin.val ((dest home).apply_symm_apply i)
  have ix : i.val=start home s.val+prior home u.val s:=eqn.symm.trans row
  change (i.val:Word w)-(((start home s.val+count home s:ℕ):Word w)-(count home s:Word w))=(prior home u.val s:Word w)
  rw [ix,Nat.cast_add,Nat.cast_add]
  abel

/-- Every raw memory has one relative rank per output cohort, strictly below
the physically retained population of its actual observed home. -/
theorem observed_slot (b : Bank) (L : ProtocolRAMEndpointSort.Layout) (m : Memory w) (pos : 0 < H)
    (fit : SortRoom b L w n H) (i : Fin n) :
    let home:=observed (n:=n) b H m pos
    let u:=(dest home).symm i
    let t:=sorted b L H n pos m
    after L n H t (out L n H+i.val)=(prior home u.val (home u):Word w) ∧
      (after L n H t (out L n H+i.val)).val < (t (L.counts+(home u).val)).val := by
  let home:=observed (n:=n) b H m pos
  let u:=(dest home).symm i
  have e:=scan_read L fit.fits fit.height home (keys b L H n m) (guarded_keys b L H n m pos fit.height) i
  refine ⟨e,?_⟩
  have last:=(buckets L fit.fits home (keys b L H n m) (home u)).2
  have gt:=ordinal_lt home u
  have cap:=endpoint_le home (home u)
  have room:=fit.fits.room
  change (after L n H (ProtocolRAMEndpointSort.image L home (keys b L H n m)) (out L n H+i.val)).val <
    ((ProtocolRAMEndpointSort.image L home (keys b L H n m)) (L.counts+(home u).val)).val
  rw [e,last,Fin.val_cast_of_lt (by omega : prior home u.val (home u) < 2^w),
    Fin.val_cast_of_lt (by omega : count home (home u) < 2^w)]
  exact gt

theorem truthful_slot (b : Bank) (L : ProtocolRAMEndpointSort.Layout) (m : Memory w) (pos : 0 < H)
    (fit : SortRoom b L w n H) (home : Fin n→Fin H)
    (source : ∀u,b.read m (u.val:Word w)=((home u).val:Word w)) (i : Fin n) :
    let u:=(dest home).symm i
    let t:=sorted b L H n pos m
    after L n H t (out L n H+i.val)=(prior home u.val (home u):Word w) ∧
      (after L n H t (out L n H+i.val)).val < (t (L.counts+(home u).val)).val := by
  have eqn : observed (n:=n) b H m pos=home := by
    funext j;apply Fin.ext
    simp [observed,source,Fin.val_cast_of_lt ((home j).isLt.trans fit.height),(home j).isLt]
  have h:=observed_slot b L m pos fit i
  dsimp only at h ⊢
  simpa only [eqn] using h

end
end Hierarchy.DescentTerminalPacketSlotRAM

end OAI
