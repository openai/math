import OAI.Hierarchy.DescentPackedEpochRetained

namespace OAI
/-! # Exact memory image of the packed epoch verifier, including rejected transcripts -/
namespace Hierarchy.DescentPackedEpochFold
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileValidity DescentTerminalEpochFlags
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {A : Type} {w : ℕ}

def score (s : Stage A) (z : A→ Bool) (m : Memory w) (i : Fin (rows s)) : ℕ :=
  bad s.source.C s.grain (cut s.grain (m s.banks.count.base).val i.val) (packed s.source.pin z s.grain i.val)

def checked (s : Stage A) (z : A→ Bool) (m : Memory w) :=
  fillSegment s.out (rows s+1) (SumScores.word s.out 1 (score s z m)) m

def nextImage (previous : ℕ) (s : Stage A) (z : A→ Bool) (m : Memory w) :=
  ProtocolRAM.image s.dest 1 (sticky previous (s.out+rows s) s.exterior) (checked s z m)

def finalImage (z : A→ Bool) (final : ℕ) : ℕ→ List (Stage A)→ Memory w→ Memory w
  | previous,[],m=>ProtocolRAM.image final 1 (sticky previous previous previous) m
  | previous,s::ss,m=>finalImage z final s.dest ss (nextImage previous s z m)

theorem check_exec {low : ℕ} (s : Stage A) (z : A→ Bool) (m : Memory w) (p : Paid w low s)
    (data_ : Reads s.banks m s.source.pin z s.grain) :
    (proc s.banks w s.grain s.source.seats s.out).Exec m (checked s z m) (fee s.banks s.grain s.source.seats) ∧
    checked s z m (s.out+rows s)=(if (view s m z).Valid then 0 else 1) ∧
    ∀a < s.out,checked s z m a=m a := by
  have sum : (∑i,score s z m i) ≤ rows s := by
    calc
      _ ≤ ∑_ : Fin (rows s),1 := Finset.sum_le_sum fun i _=>by dsimp [score,bad];split <;> decide
      _ = _ := by simp
  have fits : (checkExpr s.banks s.grain).Fits w s.out := by
    simp only [checkExpr,usedExpr,Expr.Fits]
    repeat' first | exact p.space.dictionary | exact p.space.shifts | exact p.space.starts | exact p.space.codes | exact p.space.count | trivial | constructor
  have room : s.out+(rows s+1) < 2^w:=p.space.end_
  have exact_ : (proc s.banks w s.grain s.source.seats s.out).Exec m (checked s z m) (fee s.banks s.grain s.source.seats) := Procedure.Spec.exec
    (SumScores.run s.out 1 _ (score s z m) fits room (by omega) (by omega)) m
    (DescentPackedProfileValidity.read s.banks s.source.pin z s.grain s.out m p.space data_)
  refine ⟨exact_,?_,fun a ha=>by simp [checked,fillSegment,Nat.not_le_of_gt ha]⟩
  unfold checked
  rw [SumScores.read_flag]
  have criteria : (∑i,score s z m i)=0 ↔ (view s m z).Valid := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _=>Nat.zero_le _)]
    have every := all_good s.source.pin z s.grain (m s.banks.count.base).val p.positive
    exact ⟨fun allRows => every.mp (fun i => allRows i (Finset.mem_univ i)),
      fun valid i _ => every.mpr valid i⟩
  by_cases good : (∑i,score s z m i)=0
  · simp [good,criteria.mp good]
  · rw [ite_eq_left (show 1 ≤ _ from Nat.pos_of_ne_zero good),ite_eq_right (mt criteria.mpr good)]

theorem next_exec (previous low : ℕ) (s : Stage A) (z : A→ Bool) (m : Memory w)
    (p : Paid w low s) (early : previous < s.out) (data_ : Reads s.banks m s.source.pin z s.grain) :
    let o:=nextImage previous s z m
    (single w previous s).Exec m o (singleCost previous s) ∧
    o s.dest=(if m previous=0 ∧ m s.exterior=0 ∧ (view s m z).Valid then 0 else 1) ∧
    ∀a < low,o a=m a := by
  have ⟨one,flag,held⟩:=check_exec s z m p data_
  have low_:=p.low;have mid_:=p.mid;have top:=p.end_;have bound:=p.ext
  have fits (a : ℕ) (ha : a < s.dest) : (Bank.mk a 0).Fits w s.dest := by
    change 0 < 1 ∧ 1 < 2^w ∧ a+1 ≤ s.dest;omega
  have two:=step_exec previous (s.out+rows s) s.exterior s.dest (checked s z m) (fits _ (by omega))
    (fits _ (by omega)) (fits _ (by omega)) p.end_
  refine ⟨one.then two.1,?_,fun a ha=>(two.2.2.2 a (by omega)).trans (held a (by omega))⟩
  have neq:=one_ne (w:=w) (by omega)
  rw [show nextImage previous s z m s.dest=_ from two.2.2.1,held previous early,flag,held s.exterior (by omega)]
  split_ifs <;> simp_all

theorem exact_run (low previous final : ℕ) (ss : List (Stage A)) (z : A→ Bool) (m : Memory w)
    (safe : Order w low previous final ss) (paid : ∀s∈ss,Paid w low s)
    (data_ : ∀s∈ss,Reads s.banks m s.source.pin z s.grain) :
    let o:=finalImage z final previous ss m
    (fold w previous final ss).Exec m o (bill previous final ss) ∧
    o final=(if m previous=0 ∧ ∀s∈ss,m s.exterior=0 ∧ (view s m z).Valid then 0 else 1) ∧
    ∀a < low,o a=m a := by
  induction ss generalizing previous m with
  | nil=>
    obtain ⟨less,base,space⟩:=safe
    have f : (Bank.mk previous 0).Fits w final:=by change 0 < 1 ∧ 1 < 2^w ∧ previous+1 ≤ final;omega
    have st:=step_exec previous previous previous final m f f f space
    exact ⟨st.1,by simpa [finalImage] using st.2.2.1,fun a ha=>st.2.2.2 a (by omega)⟩
  | cons s ss ih=>
    let mid:=nextImage previous s z m
    obtain ⟨early,rest⟩:=safe
    have p:=paid s (by simp)
    have head:=next_exec previous low s z m p early (data_ s (by simp))
    have pr : ∀q∈ss,Paid w low q:=fun q h=>paid q (by simp [h])
    have old : ∀q∈ss,Reads q.banks m q.source.pin z q.grain:=fun q h=>data_ q (by simp [h])
    have kept (q : Stage A) (h : q∈ss) := transfer q (pr q h) z head.2.2 (old q h)
    have tail:=ih s.dest mid rest pr (fun q h=>(kept q h).1)
    refine ⟨@Procedure.Exec.then w (single w previous s) (fold w s.dest final ss) m mid _ _ _ head.1 tail.1,?_,fun a ha=>(tail.2.2 a ha).trans (head.2.2 a ha)⟩
    have means : (∀q∈ss,mid q.exterior=0 ∧ (view q mid z).Valid) ↔ ∀q∈ss,m q.exterior=0 ∧ (view q m z).Valid := by
      have point (q : Stage A) (h : q∈ss) :
          (mid q.exterior=0 ∧ (view q mid z).Valid) ↔
          (m q.exterior=0 ∧ (view q m z).Valid) := by
        have same : view q mid z=view q m z := (kept q h).2
        have ext_ : mid q.exterior=m q.exterior := head.2.2 _ (pr q h).ext
        rw [same, ext_]
      exact ⟨fun h q hq => (point q hq).mp (h q hq),
        fun h q hq => (point q hq).mpr (h q hq)⟩
    have neq:=one_ne (w:=w) (by have :=p.end_;omega)
    change finalImage z final s.dest ss mid final=_
    rw [tail.2.1,show mid s.dest=_ from head.2.1]
    simp only [List.forall_mem_cons, means]
    by_cases prior : m previous=0 <;> by_cases exterior : m s.exterior=0 <;>
      by_cases valid : (view s m z).Valid <;> simp [prior,exterior,valid,neq]

theorem final_of_order {low previous final : ℕ} {ss : List (Stage A)}
    (safe : Order w low previous final ss) (paid : ∀s∈ss,Paid w low s) : previous < final := by
  induction ss generalizing previous with
  | nil => exact safe.1
  | cons s ss ih =>
    have h:=safe.1
    have after_:=ih safe.2 (fun q h=>paid q (by simp [h]))
    have mid:=(paid s (by simp)).mid
    omega

/-- High banks on the other side of the finite checking workspace retain their
physical words, including arbitrary exterior-matrix and terminal payload data. -/
theorem high_frame {low previous final a : ℕ} {ss : List (Stage A)} (z : A→ Bool) (m : Memory w)
    (safe : Order w low previous final ss) (paid : ∀s∈ss,Paid w low s) (beyond : final < a) :
    finalImage z final previous ss m a=m a := by
  induction ss generalizing previous m with
  | nil =>
    change ProtocolRAM.image final 1 _ m a=m a
    exact ite_eq_right (by omega : ¬(final ≤ a ∧ a < final+1))
  | cons s ss ih =>
    have tail : ∀q∈ss,Paid w low q:=fun q h=>paid q (by simp [h])
    have ends:=final_of_order safe.2 tail
    have mid:=(paid s (by simp)).mid
    change finalImage z final s.dest ss (nextImage previous s z m) a=_
    rw [ih _ safe.2 tail]
    simp only [nextImage,ProtocolRAM.image,checked,fillSegment,ite_false,
      show ¬(s.dest ≤ a ∧ a < s.dest+1) by omega,
      show ¬(s.out ≤ a ∧ a < s.out+(rows s+1)) by omega]


end
end Hierarchy.DescentPackedEpochFold

end OAI
