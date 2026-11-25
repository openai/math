import OAI.Hierarchy.DescentTerminalLastColumns

namespace OAI
/-! # One physical suffix for cutoffs, scalar counts, and the accumulated failure word -/
namespace Hierarchy.DescentTerminalLast
open DescentCensusRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w rows pool bins word cut stop : ℕ}

private theorem fits_later {dst dst' : ℕ} (h : dst≤dst') (e : Expr) (ok : e.Fits w dst) : e.Fits w dst' := by
  induction e with
  | row | lit=>trivial
  | lookup b _ r=>exact ⟨⟨ok.1.1,ok.1.2.1,ok.1.2.2.trans h⟩,r ok.2⟩
  | op _ _ _ a b=>exact ⟨a ok.1,b ok.2⟩
  | branch _ _ _ _ _ a b y n=>exact ⟨a ok.1,b ok.2.1,y ok.2.2.1,n ok.2.2.2⟩

private theorem old_word {a o n : ℕ} (e : Expr) (m : Memory w) (h : a<o) : image o n e m a=m a := by
  simp [image,fillSegment,not_le.mpr h]
private theorem new_word {o n : ℕ} (e : Expr) (m : Memory w) (i : Fin n) :
    image o n e m (o+i.val)=e.eval m (i.val:Word w) := by
  simp [image,fillSegment,show o+i.val<o+n by have:=i.isLt;omega,Nat.cast_add]

structure Output (L : Tape) (S : Banks w pool bins) (cut stop rows word : ℕ) (positive : 0<bins)
    (m o : Memory w) : Prop where
  frame : ∀a<cut,o a=m a
  cutoff : ∀i:Fin rows,o (cut+i.val)=(DescentTerminalLast.cutoff word (m L.whole.base).val (m L.tail.base).val i.val:Word w)
  histogram : ∀j : Fin bins,o (S.bins+j.val)=((Finset.univ.filter (fun i : Fin pool=>evalKey L positive m i=j)).card:Word w)
  failure : o stop=(badBit L m:Word w)

theorem run (L : Tape) (S : Banks w pool bins) (ready : Ready L S cut stop rows word) (m : Memory w) :
    ∃o : Memory w, (program L S cut stop rows word).Exec m o (ticks L S rows word) ∧
      CheapCode (program L S cut stop rows word) ∧ Output L S cut stop rows word ready.binsPos m o := by
  let mask:=clipped L.whole L.tail word
  let keys:=safeKey S L.keys
  let flag:=stopBit L.flags
  let m0:=image cut rows mask m
  have c0:=ready.clear
  have c1:=S.scratch
  have c2:=S.beforeTape
  have c3:=S.beforeBins
  have c4:=ready.counted
  have cf:=ready.final
  have fc : mask.Fits w cut := by
    simp only [mask,clipped,atZero,Expr.Fits]
    repeat' first | exact ready.inputs _ (by simp [Tape.inputs]) | trivial | constructor
  have fk : keys.Fits w cut := by
    simp only [keys,safeKey,Expr.Fits]
    repeat' first | exact ready.inputs _ (by simp [Tape.inputs]) | trivial | constructor
  have ff : flag.Fits w cut := by
    simp only [flag,stopBit,atZero,Expr.Fits]
    repeat' first | exact ready.inputs _ (by simp [Tape.inputs]) | trivial | constructor
  have r0 : (scan w cut rows mask).Exec m m0 (4+rows*(2*mask.work+4)) :=
    scan_exec cut rows mask m fc (by omega)
  have below (a : ℕ) (ha:a<cut) : m0 a=m a:=old_word _ _ ha
  let tag:=evalKey (pool:=pool) L ready.binsPos m
  have r1:=tally_exec S keys (.lit 1) tag (fun _=>1) m0
    (fits_later (by omega) _ fk) trivial (fun i=>
      (eval_below keys _ m m0 fk below).trans (safeKey_read L S ready m i)) (fun _=>rfl)
  obtain ⟨m1,go,hist,keep⟩:=r1
  let out:=image stop 1 flag m1
  have r2 : (scan w stop 1 flag).Exec m1 out (4+1*(2*flag.work+4)) :=
    scan_exec stop 1 flag m1 (fits_later (by omega) _ ff) cf
  refine ⟨out, Procedure.Exec.then (A:=(scan w cut rows mask).seq (tally S keys (.lit 1)))
    (B:=scan w stop 1 flag) (Procedure.Exec.then (A:=scan w cut rows mask)
    (B:=tally S keys (.lit 1)) @r0 @go) @r2, @cheap w pool bins L S cut stop rows word, ?_, ?_, ?_, ?_⟩
  · intro a ha;exact (old_word _ _ (by omega)).trans ((keep _ (by omega)).trans (below _ ha))
  · intro i
    have hi:=i.isLt
    exact (old_word _ _ (by omega)).trans ((keep _ (by omega)).trans
      ((new_word mask m i).trans (cutoff_read L S ready m i)))
  · intro j
    have hj:=j.isLt
    rw [show out (S.bins+j.val)=m1 (S.bins+j.val) from old_word _ _ (by omega),hist]
    simp [DescentCensusRAM.sumAt,Finset.sum_boole,tag]
  · have m1old (a : ℕ) (ha:a<cut) : m1 a=m a:=(keep _ (by omega)).trans (below _ ha)
    have v : out stop=flag.eval m1 0 := by simpa using (new_word (o:=stop) flag m1 (0:Fin 1))
    exact v.trans ((eval_below flag 0 m m1 ff m1old).trans (stop_read L m))

theorem bounded_clock (L : Tape) (S : Banks w pool bins) (rows word : ℕ) :
    ticks L S rows word≤200+100*rows+6*bins+300*pool := by
  simp [ticks,clipped,atZero,safeKey,stopBit,tallyCost,addCost,issueCost,DescentCensusRAM.slot,
    ProtocolRAMGeneratedWrite.work,Expr.work]
  omega

end
end Hierarchy.DescentTerminalLast

end OAI
