import OAI.Optimization.LinearProgramming.Compression.IngressIndex

/-! Make the four low address registers available as scratch by first moving their live
request words into a region above the entire incoming word string. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Ingress

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def saveOrder : Block :=
  .seq (.op (.incr 0 0)) (.seq (.op (.addrStore 0 1)) (.op (.decr 0 0)))

private theorem saveOrder_spec (P : K → Prop) (s : Memory K) (b : ℕ) (hb : 4 ≤ b)
    (hp : s.index 0=b) (hs : Good P s) :
    ∃ t, Block.Eval (Good P) saveOrder s 3 t ∧ t.data=s.data ∧
      ∀ i, t.index i=(if i=b+1 then s.index 1 else s.index i) := by
  let a := s.putIndex 0 (s.index 0+1)
  let c := a.putIndex (a.index 0) (a.index 1)
  let t := c.putIndex 0 (c.index 0-1)
  have ea : Block.Eval (Good P) (.op (.incr 0 0)) s 1 a := Block.Eval.op_incr _ _ _ hs hs
  have ec : Block.Eval (Good P) (.op (.addrStore 0 1)) a 1 c := Block.Eval.op_addrStore _ _ _ hs hs
  have et : Block.Eval (Good P) (.op (.decr 0 0)) c 1 t := Block.Eval.op_decr _ _ _ hs hs
  refine ⟨t,ea.seq (ec.seq et),rfl,?_⟩
  intro i
  by_cases it : i=0
  · subst i
    simp (disch := omega) [t,c,a,hp]
  · by_cases ib : i=b+1
    · subst i; simp (disch := omega) [t,c,a,hp]
    · simp (disch := omega) [t,c,a,hp,ib]

private theorem writeAt (P : K → Prop) (s : Memory K) (b src val : ℕ) (hb : 0 < b)
    (hp : s.index 0=b) (hv : s.index src=val) (hs : Good P s) :
    ∃ t, Block.Eval (Good P) (writeWord 0 src) s 2 t ∧ t.data=s.data ∧
      t.index 0=b+1 ∧ t.index b=val ∧
      ∀ i,i ≠ 0 → i ≠ b → t.index i=s.index i := by
  obtain ⟨t,et,hd,h0,hw,hf⟩ := writeWord_spec P s 0 src (by omega) hs
  exact ⟨t,et,hd,by simpa only [hp] using h0,by simpa only [hp,hv] using hw,
    fun i iz ib => hf i iz (hp ▸ ib)⟩

/-- Stage the request tag, order, and the old contents of address registers two and three.
With order zero the last two temporary writes are outside the two-word request. -/
def shieldPrefix : Block :=
  .seq saveOrder (.seq selectTag (.seq (writeWord 0 1)
    (.seq (.op (.incr 0 0)) (.seq (writeWord 0 2) (writeWord 0 3)))))

theorem shieldPrefix_spec (P : K → Prop) (s : Memory K) (b tag : ℕ) (hb : 4 ≤ b)
    (hbit : tag ≤ 1) (hp : s.index 0=b) (h6 : s.data 6=(tag:K)) (h3 : s.data 3=1)
    (hs : Good P s) :
    ∃ t, Block.Eval (Good P) shieldPrefix s 13 t ∧ t.data=s.data ∧ t.index 0=b+4 ∧
      t.index b=tag ∧ t.index (b+1)=s.index 1 ∧ t.index (b+2)=s.index 2 ∧
      t.index (b+3)=s.index 3 ∧ ∀ (i : ℕ), 4 ≤ i → i < b → t.index i=s.index i := by
  obtain ⟨a,ea,ad,ai⟩ := saveOrder_spec P s b hb hp hs
  obtain ⟨c,ec,cd,ct,cf⟩ := selectTag_spec P a tag hbit (ad ▸ h6) (ad ▸ h3) ea.safe_end
  have c0 : c.index 0=b := by rw [cf 0 (by decide),ai 0,ite_eq_right (by omega),hp]
  have cOrder : c.index (b+1)=s.index 1 := by rw [cf _ (by omega),ai _,ite_eq_left rfl]
  have cRaw (i : ℕ) (lo : 2 ≤ i) (hi : i < b) : c.index i=s.index i := by
    rw [cf i (by omega),ai i,ite_eq_right (by omega)]
  obtain ⟨d,ed,dd,d0,dTag,df⟩ := writeAt P c b 1 tag (by omega) c0 ct ec.safe_end
  let e := d.putIndex 0 (d.index 0+1)
  have ee : Block.Eval (Good P) (.op (.incr 0 0)) d 1 e := Block.Eval.op_incr _ _ _ ed.safe_end ed.safe_end
  have e0 : e.index 0=b+2 := by simp [e,d0]
  have ef0 (i : ℕ) (h : i ≠ 0) : e.index i=d.index i := by simp [e,h]
  have eRaw (i : ℕ) (lo : 2 ≤ i) (hi : i < b) : e.index i=s.index i :=
    (ef0 i (by omega)).trans ((df i (by omega) (by omega)).trans (cRaw i lo hi))
  obtain ⟨f,ef,fd,f0,fRow,ff⟩ := writeAt P e (b+2) 2 (s.index 2) (by omega) e0
    (eRaw 2 (by decide) (by omega)) ee.safe_end
  have fRaw (i : ℕ) (lo : 2 ≤ i) (hi : i < b) : f.index i=s.index i :=
    (ff i (by omega) (by omega)).trans (eRaw i lo hi)
  obtain ⟨t,et,td,t0,tRow,tf⟩ := writeAt P f (b+3) 3 (s.index 3) (by omega) f0
    (fRaw 3 (by decide) (by omega)) ef.safe_end
  refine ⟨t,ea.seq (ec.seq (ed.seq (ee.seq (ef.seq et)))),td.trans (fd.trans (dd.trans (cd.trans ad))),
    t0,?_,?_,(tf _ (by omega) (by omega)).trans fRow,tRow,?_⟩
  · exact (tf _ (by omega) (by omega)).trans ((ff _ (by omega) (by omega)).trans ((ef0 _ (by omega)).trans dTag))
  · exact (tf _ (by omega) (by omega)).trans ((ff _ (by omega) (by omega)).trans
      ((ef0 _ (by omega)).trans ((df _ (by omega) (by omega)).trans cOrder)))
  · intro i lo hi
    exact (tf i (by omega) (by omega)).trans (fRaw i (by omega) hi)

end Ingress
end Compression
end LinearProgramming
end Optimization
end OAI
