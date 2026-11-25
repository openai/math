import OAI.Optimization.LinearProgramming.Compression.ServiceTableOrder
import OAI.Optimization.LinearProgramming.Compression.UniformIndex

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

/-- Consume one comparison result while accumulating the strict lower rank and membership. -/
def accumulate : Block := .branch (.addrLT 23 0) (.op (.incr 19 19))
  (.branch (.addrLT 23 2) (.op (.addrConst 1 1)) .skip)

theorem accumulate_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {α : Type*} [LinearOrder α] (y q : α)
    (P : K → Prop) (s : Memory K) (hs : ∀ a, P (s.data a))
    (h0 : s.index 0=1) (h2 : s.index 2=2)
    (hf : s.index 23=(if y<q then 0 else if y=q then 1 else 2)) :
    ∃ t k, k≤4 ∧ Block.Eval (fun z => ∀ a,P (z.data a)) accumulate s k t ∧
      t.index 19=s.index 19+(if y<q then 1 else 0) ∧
      t.index 1=(if y=q then 1 else s.index 1) ∧ t.data=s.data ∧
      ∀ a, a≠1 → a≠19 → t.index a=s.index a := by
  let safe := fun z : Memory K => ∀ a,P (z.data a)
  by_cases hl : y<q
  · have hn := ne_of_lt hl
    let t := s.putIndex 19 (s.index 19+1)
    have e : Block.Eval safe (.op (.incr 19 19)) s 1 t := Block.Eval.op_incr _ _ _ hs hs
    refine ⟨t,3,by decide,.branchTrue (by simp [Cond.test,hf,hl,h0]) e,?_,?_,rfl,?_⟩
    · simp [t,hl]
    · simp [t,hn]
    · intro a _ h; simp [t,h]
  · by_cases he : y=q
    · let t := s.putIndex 1 1
      have e : Block.Eval safe (.op (.addrConst 1 1)) s 1 t := Block.Eval.op_addrConst _ _ _ hs hs
      refine ⟨t,4,by decide,.branchFalse (by simp [Cond.test,hf,he,h0])
        (.branchTrue (by simp [Cond.test,hf,he,h2]) e),?_,?_,rfl,?_⟩
      · simp [t,hl]
      · simp [t,he]
      · intro a h _; simp [t,h]
    · exact ⟨s,2,by decide,.branchFalse (by simp [Cond.test,hf,hl,he,h0])
        (.branchFalse (by simp [Cond.test,hf,hl,he,h2]) (.skip hs)),by simp [hl],by simp [he],rfl,fun _ _ _ => rfl⟩

/-- The matrix/table base, permanent lookup inputs, and incoming request words survive a scan. -/
def ScanKeep (a : ℕ) : Prop := a=14 ∨ a=17 ∨ a=18 ∨ a=21 ∨ a=22 ∨ 40≤a

theorem slotBase_ge_seven (n i : ℕ) : 7 ≤ slotBase n i := by unfold slotBase tableBase; omega

theorem SlotAt.frame {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
    {q : NonzeroPairMinor D E} {s t : Memory ℚ} {b : ℕ} (h : SlotAt D E q b s) (hb : 7≤b)
    (f : ∀ a, a≠0 → a≠5 → a≠6 → t.data a=s.data a) : SlotAt D E q b t := by
  apply h.transfer
  intro j _
  exact f (b+j) (by omega) (by omega) (by omega)

/-- A full traversal has a dimension-only upper bound, including testing a present key. -/
def scanBody (compareSlots : Block) : Block := .seq compareSlots (.seq accumulate
  (.seq (cellAddress 20 11 12 20 22 3 18) (.op (.incr 16 16))))

def scanLoop (compareSlots : Block) : Block := .loop (.addrLT 16 17) (scanBody compareSlots)

private structure ScanInvariant {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
    (q : NonzeroPairMinor D E) (keys : List (NonzeroPairMinor D E)) (P : ℚ → Prop)
    (start : Memory ℚ) (i : ℕ) (s : Memory ℚ) : Prop where
  safe : ∀ a,P (s.data a)
  counter : s.index 16=i
  ptr : s.index 20=slotBase n i
  rank : s.index 19=GeneratorTable.rank q (keys.take i)
  found : s.index 1=(if q∈keys.take i then 1 else 0)
  one : s.index 0=1
  two : s.index 2=2
  zero : s.index 3=0
  keep : ∀ a, ScanKeep a → s.index a=start.index a
  data : ∀ a, a≠0 → a≠5 → a≠6 → s.data a=start.data a

/-- Read every row of an actual scalar table with a verified comparator. The result is both
membership (address 1) and the insertion/lookup coordinate in the formal generator vector (19). -/
theorem scanLoop_spec (cmp : Block) (C : ℕ → ℕ) (hcmp : SlotComparatorSpec cmp C)
    {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (q : NonzeroPairMinor D E) (keys : List (NonzeroPairMinor D E)) (P : ℚ → Prop)
    (s : Memory ℚ) (hdim : d+e=n) (hkeys : Stored D E keys s)
    (hrequest : SlotAt D E q (slotBase n (keys.length+1)) s)
    (h17 : s.index 17=keys.length) (h18 : s.index 18=stride n)
    (h20 : s.index 20=tableBase n) (h21 : s.index 21=slotBase n (keys.length+1)) (h22 : s.index 22=n)
    (h0 : s.index 0=1) (h1 : s.index 1=0) (h2 : s.index 2=2) (h3 : s.index 3=0)
    (h16 : s.index 16=0) (h19 : s.index 19=0)
    (hs : ∀ a,P (s.data a)) (hnat : ∀ j≤4*(n+1)^2,P (j:ℚ)) :
    ∃ t k, k≤keys.length*(C n+4*stride n+12)+1 ∧
      Block.Eval (fun z => ∀ a,P (z.data a)) (scanLoop cmp) s k t ∧
      t.index 19=rank q keys ∧ t.index 1=(if q∈keys then 1 else 0) ∧
      t.index 20=slotBase n keys.length ∧ (∀ a, ScanKeep a → t.index a=s.index a) ∧
      ∀ a, a≠0 → a≠5 → a≠6 → t.data a=s.data a := by
  let I := ScanInvariant q keys P s
  have start : I 0 s := ⟨hs,h16,by simpa [slotBase] using h20,
    by simpa [rank] using h19,by simpa using h1,h0,h2,h3,fun _ _ => rfl,fun _ _ _ _ => rfl⟩
  have step (j : ℕ) (hj : j<keys.length) (m : Memory ℚ) (hm : I j m) :
      (Cond.addrLT 16 17).test m=true ∧ ∃ t k, k≤C n+4*stride n+10 ∧
        Block.Eval (fun z => ∀ a,P (z.data a)) (scanBody cmp) m k t ∧ I (j+1) t := by
    have m17 := (hm.keep 17 (by simp [ScanKeep])).trans h17
    have m18 := (hm.keep 18 (by simp [ScanKeep])).trans h18
    have m21 := (hm.keep 21 (by simp [ScanKeep])).trans h21
    have m22 := (hm.keep 22 (by simp [ScanKeep])).trans h22
    refine ⟨by simpa [Cond.test,hm.counter,m17] using hj,?_⟩
    let y := keys[j]
    have sy : SlotAt D E y (m.index 20) m := by
      rw [hm.ptr]
      exact (hkeys.slots ⟨j,hj⟩).frame (slotBase_ge_seven _ _) hm.data
    have sq : SlotAt D E q (m.index 21) m := by
      rw [m21]
      exact hrequest.frame (slotBase_ge_seven _ _) hm.data
    obtain ⟨b,k,hk,eb,hf,bi,bd⟩ := hcmp D E y q P m hdim m22 sy sq
      (hm.ptr ▸ slotBase_ge_seven _ _) (m21 ▸ slotBase_ge_seven _ _) hm.safe hnat
    have bix (a : ℕ) (ha : a<23) : b.index a=m.index a := bi a (Or.inl ha)
    obtain ⟨c,l,hl,ec,cr,cf,cd,ci⟩ := accumulate_spec y q P b eb.safe_end
      ((bix 0 (by decide)).trans hm.one) ((bix 2 (by decide)).trans hm.two) hf
    have cx (a : ℕ) (h₁ : a≠1) (h₂ : a≠19) (h₃ : a<23) : c.index a=m.index a :=
      (ci a h₁ h₂).trans (bix a h₃)
    have c3 := (cx 3 (by decide) (by decide) (by decide)).trans hm.zero
    have c18 := (cx 18 (by decide) (by decide) (by decide)).trans m18
    obtain ⟨v,ev,vd,vi,v20⟩ := cellAddress_spec (fun z => ∀ a,P (z a)) c ec.safe_end
      20 11 12 20 22 3 18 (by simp [CellScratchOK])
    rw [c3,c18] at ev v20
    simp only [Nat.zero_mul,Nat.add_zero,Nat.zero_add] at ev v20
    let t := v.putIndex 16 (v.index 16+1)
    have et : Block.Eval (fun z => ∀ a,P (z.data a)) (.op (.incr 16 16)) v 1 t :=
      Block.Eval.op_incr _ _ _ ev.safe_end ev.safe_end
    have vx (a : ℕ) (ha : a≠20) (hb : a≠11) (hc : a≠12) (hd : a≠1) (he : a≠19) (hf' : a<23) :
        v.index a=m.index a := (vi _ ha hb hc).trans (cx _ hd he hf')
    refine ⟨t,k+(l+(4*stride n+5+1)),by omega,eb.seq (ec.seq (ev.seq et)),et.safe_end,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [t,(vx 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),hm.counter]
    · simp [t,v20,cx 20 (by decide) (by decide) (by decide),hm.ptr,slotBase,Nat.add_mul,Nat.add_assoc]
    · rw [List.take_succ_eq_append_getElem hj,rank_snoc]
      simp [t,vi 19 (by decide) (by decide) (by decide),cr,bix 19 (by decide),hm.rank,y]
    · rw [List.take_succ_eq_append_getElem hj]
      rw [show t.index 1=v.index 1 by simp [t],vi 1 (by decide) (by decide) (by decide),cf,bix 1 (by decide),hm.found]
      simp only [List.mem_append,List.mem_singleton]
      by_cases h : q=keys[j]
      · rw [ite_eq_left (show y=q from h.symm),ite_eq_left (Or.inr h)]
      · rw [ite_eq_right (show y≠q from Ne.symm h)]
        simp [h]
    · simp [t,(vx 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),hm.one]
    · simp [t,(vx 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),hm.two]
    · simp [t,(vx 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),hm.zero]
    · intro a ha
      have h : a≠16 ∧ a≠20 ∧ a≠11 ∧ a≠12 ∧ a≠1 ∧ a≠19 ∧ (a<23 ∨ 40≤a) := by unfold ScanKeep at ha; omega
      obtain ⟨w₁,w₂,w₃,w₄,w₅,w₆,w₇⟩ := h
      simpa [t,w₁] using (vi a w₂ w₃ w₄).trans ((ci a w₅ w₆).trans ((bi a w₇).trans (hm.keep a ha)))
    · intro a ha hb hc
      change v.data a=s.data a
      rw [vd,cd,bd a ha hb hc,hm.data a ha hb hc]
  have stop (t : Memory ℚ) (ht : I keys.length t) : (Cond.addrLT 16 17).test t=false ∧ ∀ a,P (t.data a) := by
    exact ⟨by simp [Cond.test,ht.counter,(ht.keep 17 (by simp [ScanKeep])).trans h17],ht.safe⟩
  obtain ⟨t,k,hk,et,ht⟩ := Block.Eval.loop_invariant I s keys.length (C n+4*stride n+10) start step stop
  exact ⟨t,k,by simpa [Nat.add_assoc] using hk,et,by simpa using ht.rank,by simpa using ht.found,ht.ptr,ht.keep,ht.data⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
