import OAI.Optimization.LinearProgramming.Compression.IngressCore
import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan

/-! Clear a bounded physical address window before the nested numerical call.
The protected odd metadata words are captured before any volatile register is erased. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceClean

open RAM GeneratorTable

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def savedSlots : List ℕ := [93,95,97,99,101,103,105,107,109,111,113]

structure Metadata (live src g n rank member cap : ℕ) (m : Memory K) : Prop where
  length : m.index 101=live
  source : m.index 103=src
  count : m.index 105=g
  columns : m.index 107=n
  position : m.index 109=rank
  present : m.index 111=member
  capacity : m.index 113=cap

structure TableWords (base stride stop next : ℕ) (m : Memory K) : Prop where
  baseWord : m.index 93=base
  strideWord : m.index 95=stride
  stopWord : m.index 97=stop
  nextWord : m.index 99=next

private def savePlan : List AddressSet :=
  [.read 93 14,.read 95 18,.read 97 20,.read 99 21,.read 101 7,.read 103 5,.read 105 17,.read 107 22,.read 109 19,.read 111 1,.read 113 27]

def capture : Block := addressPlan savePlan

theorem capture_spec (P : K → Prop) (s : Memory K) (hs : ∀ i,P (s.data i)) :
    ∃ t, Block.Eval (fun m => ∀ i,P (m.data i)) capture s 11 t ∧ t.data=s.data ∧
      Metadata (s.index 7) (s.index 5) (s.index 17) (s.index 22) (s.index 19) (s.index 1) (s.index 27) t ∧
      TableWords (s.index 14) (s.index 18) (s.index 20) (s.index 21) t := by
  let t := applyPlan savePlan s
  have run := addressPlan_spec (fun f : ℕ → K => ∀ i,P (f i)) savePlan s hs
  refine ⟨t,run,rfl,?_,?_⟩ <;> constructor <;> simp [t,savePlan,applyPlan,AddressSet.apply]

private def zeroSlots : List ℕ → Block
  | [] => .skip
  | r::rs => .seq (.op (.addrConst r 0)) (zeroSlots rs)

private theorem zeroSlots_spec (P : K → Prop) (s : Memory K) (rs : List ℕ) (hs : ∀ i,P (s.data i)) :
    ∃ t, Block.Eval (fun m => ∀ i,P (m.data i)) (zeroSlots rs) s rs.length t ∧ t.data=s.data ∧
      ∀ i, t.index i=if i∈rs then 0 else s.index i := by
  induction rs generalizing s with
  | nil => exact ⟨s,.skip hs,rfl,fun _ => by simp⟩
  | cons r rs ih =>
    let a := s.putIndex r 0
    have ea : Block.Eval (fun m => ∀ i,P (m.data i)) (.op (.addrConst r 0)) s 1 a :=
      Block.Eval.op_addrConst _ _ _ hs hs
    obtain ⟨t,et,td,ti⟩ := ih a ea.safe_end
    refine ⟨t,by simpa [zeroSlots,Nat.one_add] using ea.seq et,td,?_⟩
    intro i
    by_cases ir : i=r <;> by_cases mem : i∈rs <;> simp [ti,a,ir,mem]

private def low := (List.range 114).filter fun i => decide (i∉savedSlots)
private def highInit : List AddressSet := [.fix 2 114,.fix 4 0,.next 6 113]
private def highBody : Block := .seq (.op (.addrStore 2 4)) (.op (.incr 2 2))
private def high : Block := .seq (addressPlan highInit) (.loop (.addrLT 2 6) highBody)

private theorem high_spec (P : K → Prop) (s : Memory K) (cap : ℕ) (hc : 114 ≤ cap) (h113 : s.index 113=cap)
    (hs : ∀ i,P (s.data i)) :
    ∃ t, Block.Eval (fun m => ∀ i,P (m.data i)) high s (3+((cap+1-114)*4+1)) t ∧
      t.data=s.data ∧ ∀ i, i ≠ 2 → i ≠ 4 → i ≠ 6 →
        t.index i=if 114 ≤ i ∧ i ≤ cap then 0 else s.index i := by
  let a := applyPlan highInit s
  have ea : Block.Eval (fun m => ∀ i,P (m.data i)) (addressPlan highInit) s 3 a :=
    addressPlan_spec (fun f : ℕ → K => ∀ i,P (f i)) highInit s hs
  let I (j : ℕ) (m : Memory K) := m.data=s.data ∧ m.index 2=114+j ∧ m.index 4=0 ∧ m.index 6=cap+1 ∧
    ∀ i, i ≠ 2 → i ≠ 4 → i ≠ 6 → m.index i=if 114 ≤ i ∧ i < 114+j then 0 else s.index i
  have base : I 0 a := by
    refine ⟨rfl,by simp [a,highInit,applyPlan,AddressSet.apply],
      by simp [a,highInit,applyPlan,AddressSet.apply],by simp [a,highInit,applyPlan,AddressSet.apply,h113],?_⟩
    intro i i2 i4 i6
    have empty : ¬(114 ≤ i ∧ i < 114+0) := by omega
    rw [ite_eq_right empty]
    simp (disch := omega) [a,highInit,applyPlan,AddressSet.apply]
  have one (j : ℕ) (hj : j < cap+1-114) (m : Memory K) (h : I j m) :
      (Cond.addrLT 2 6).test m=true ∧ ∃ t, Block.Eval (fun z => ∀ i,P (z.data i)) highBody m 2 t ∧ I (j+1) t := by
    obtain ⟨hd,h2,h4,h6,hf⟩ := h
    have hm (i : ℕ) : P (m.data i) := by rw [hd]; exact hs i
    refine ⟨by simp [Cond.test,h2,h6]; omega,?_⟩
    let b := m.putIndex (m.index 2) (m.index 4)
    let t := b.putIndex 2 (b.index 2+1)
    have eb : Block.Eval (fun z => ∀ i,P (z.data i)) (.op (.addrStore 2 4)) m 1 b :=
      Block.Eval.op_addrStore _ _ _ hm hm
    have et : Block.Eval (fun z => ∀ i,P (z.data i)) (.op (.incr 2 2)) b 1 t := Block.Eval.op_incr _ _ _ hm hm
    refine ⟨t,eb.seq et,hd,by simp (disch := omega) [t,b,h2,Nat.add_assoc],
      by simp (disch := omega) [t,b,h2,h4],by simp (disch := omega) [t,b,h2,h6],?_⟩
    intro i i2 i4 i6
    by_cases hit : i=114+j
    · subst i
      simp (disch := omega) [t,b,h2,h4]
    · rw [show t.index i=m.index i by simp [t,b,i2,h2,hit],hf i i2 i4 i6]
      split_ifs <;> first | rfl | omega
  have stop (m : Memory K) (h : I (cap+1-114) m) :
      (Cond.addrLT 2 6).test m=false ∧ ∀ i,P (m.data i) := by
    obtain ⟨hd,h2,_,h6,_⟩ := h
    refine ⟨by simp [Cond.test,h2,h6]; omega, ?_⟩
    intro i
    rw [hd]
    exact hs i
  obtain ⟨t,run,td,_,_,_,ti⟩ :=
    Block.Eval.loop_invariant_exact I a (cap+1-114) 2 base one stop
  refine ⟨t,ea.seq run,td,?_⟩
  intro i i2 i4 i6
  rw [ti i i2 i4 i6]
  split_ifs <;> first | rfl | omega

def clearAddresses : Block := .seq high (zeroSlots low)

def addressClearCost (cap : ℕ) := 3+((cap+1-114)*4+1)+low.length

theorem addressClearCost_le (cap : ℕ) : addressClearCost cap ≤ 4*cap+122 := by
  have h : low.length ≤ 114 := by decide
  unfold addressClearCost
  omega

theorem clearAddresses_spec (P : K → Prop) (s : Memory K) (cap : ℕ)
    (hc : 114 ≤ cap) (h113 : s.index 113=cap) (hs : ∀ i,P (s.data i)) :
    ∃ t, Block.Eval (fun m => ∀ i,P (m.data i)) clearAddresses s
        (addressClearCost cap) t ∧ t.data=s.data ∧
      (∀ i∈savedSlots, t.index i=s.index i) ∧ ∀ i ≤ cap, i∉savedSlots → t.index i=0 := by
  obtain ⟨a,ea,ad,ai⟩ := high_spec P s cap hc h113 hs
  obtain ⟨t,et,td,ti⟩ := zeroSlots_spec P a low ea.safe_end
  refine ⟨t,ea.seq et,td.trans ad,?_,?_⟩
  · intro i hi
    have slots : 93 ≤ i ∧ i < 114 := by
      simp only [savedSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      omega
    have h' : i∉low := by simp [low,hi]
    rw [ti,ite_eq_right h',ai i (by omega) (by omega) (by omega),ite_eq_right (by omega)]
  · intro i hi hnot
    by_cases lower : i < 114
    · have mem : i∈low := by simp [low,lower,hnot]
      rw [ti,ite_eq_left mem]
    · have outside : i∉low := by simp [low,lower]
      rw [ti,ite_eq_right outside,ai i (by omega) (by omega) (by omega),ite_eq_left (by omega)]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem Metadata.transfer {s t : Memory K} {L F g n r m cap : ℕ}
    (h : Metadata L F g n r m cap s) (fr : ∀ i∈savedSlots,t.index i=s.index i) :
    Metadata L F g n r m cap t := by
  constructor
  · exact (fr _ (by decide)).trans h.length
  · exact (fr _ (by decide)).trans h.source
  · exact (fr _ (by decide)).trans h.count
  · exact (fr _ (by decide)).trans h.columns
  · exact (fr _ (by decide)).trans h.position
  · exact (fr _ (by decide)).trans h.present
  · exact (fr _ (by decide)).trans h.capacity

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem TableWords.transfer {s t : Memory K} {b w endPos next : ℕ}
    (h : TableWords b w endPos next s) (fr : ∀ i∈savedSlots,t.index i=s.index i) :
    TableWords b w endPos next t :=
  ⟨(fr _ (by decide)).trans h.baseWord,(fr _ (by decide)).trans h.strideWord,
   (fr _ (by decide)).trans h.stopWord,(fr _ (by decide)).trans h.nextWord⟩

end ServiceClean
end Compression
end LinearProgramming
end Optimization
end OAI
