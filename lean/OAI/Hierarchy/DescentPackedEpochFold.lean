import OAI.Hierarchy.DescentPackedProfileInstall
import OAI.Hierarchy.DescentTerminalEpochChart
import OAI.Hierarchy.DescentTerminalEpochFlags

namespace OAI
/-! # Final sticky failure over the compact profile banks and true reached counters -/
namespace Hierarchy.DescentPackedEpochFold
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileValidity DescentTerminalEpochFlags
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

structure Stage (A : Type) where
  source : Source A
  banks : Banks
  grain : ℕ
  exterior : ℕ
  out : ℕ
  dest : ℕ

variable {A : Type} {w : ℕ}
def rows (s : Stage A) := slots s.source.seats s.grain
def view (s : Stage A) (m : Memory w) (z : A→Bool) : Observation :=
  ⟨s.source.C,(m s.banks.count.base).val,s.source.seats,DescentTerminalEpochBits.raw (z∘s.source.pin)⟩

def single (w previous : ℕ) (s : Stage A) :=
  (proc s.banks w s.grain s.source.seats s.out).seq (step w previous (s.out+rows s) s.exterior s.dest)

def singleCost (previous : ℕ) (s : Stage A) :=
  DescentPackedProfileValidity.fee s.banks s.grain s.source.seats+
    (4+1*(2*(sticky previous (s.out+rows s) s.exterior).work+4))

def bill (previous final : ℕ) : List (Stage A)→ℕ
  | [] => 4+1*(2*(sticky previous previous previous).work+4)
  | s::ss=>singleCost previous s+bill s.dest final ss

theorem singleCost_eq (previous : ℕ) (s : Stage A) :
    singleCost previous s=68+170*(rows s+1) := by
  change (4+(rows s+1)*170)+64=_
  omega

theorem bill_eq (previous final : ℕ) (ss : List (Stage A)) :
    bill previous final ss=64+238*ss.length+170*(ss.map rows).sum := by
  induction ss generalizing previous with
  | nil=>rfl
  | cons s ss ih=>
    rw [bill,singleCost_eq,ih]
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

def fold (w previous final : ℕ) : List (Stage A)→Procedure w
  | []=>step w previous previous previous final
  | s::ss=>(single w previous s).seq (fold w s.dest final ss)

structure Paid (w floor : ℕ) (s : Stage A) : Prop where
  space : Room s.banks w s.source.C s.source.seats s.grain s.out
  positive : 0 < s.grain
  low : floor ≤ s.out
  ext : s.exterior < floor
  mid : s.out+rows s+1 ≤ s.dest
  end_ : s.dest+1 < 2^w
  retained : ∀b∈[s.banks.source,s.banks.starts,s.banks.shifts,s.banks.dictionary,s.banks.count],b.base+b.size ≤ floor

def Order (w low previous final : ℕ) : List (Stage A)→Prop
  | []=>previous < final ∧ low ≤ final ∧ final+1 < 2^w
  | s::ss=>previous < s.out ∧ Order w low s.dest final ss

theorem one_ne (high : 1 < 2^w) : (1:Word w)≠0 := by
  intro eqn
  have e:=congrArg Fin.val eqn
  simp [Nat.mod_eq_of_lt high] at e

theorem single_run (previous low : ℕ) (s : Stage A) (z : A→Bool) (m : Memory w)
    (p : Paid w low s) (early : previous < s.out) (data_ : Reads s.banks m s.source.pin z s.grain) :
    (single w previous s).Spec (·=m) (fun _ o=>
      (o s.dest=if m previous=0 ∧ m s.exterior=0 ∧ (view s m z).Valid then 0 else 1) ∧
      ∀a < low,o a=m a) (singleCost previous s) ∧ CheapCode (single w previous s) := by
  obtain ⟨test,cheap⟩:=DescentPackedProfileValidity.run s.banks s.source.pin z s.grain s.out m p.space data_ p.positive
  have a:=p.mid
  have b:=p.end_
  have c:=p.low
  have d:=p.ext
  have fits (i : ℕ) (small : i < s.dest) : (Bank.mk i 0).Fits w s.dest := by
    change 0 < 1 ∧ 1 < 2^w ∧ i+1 ≤ s.dest;omega
  let check:=s.out+rows s
  have last : (step w previous check s.exterior s.dest).Spec (fun _=>True) (fun mid o=>
      o s.dest=(if mid previous=0 ∧ mid check=0 ∧ mid s.exterior=0 then 0 else 1) ∧
      ∀a,a≠s.dest → o a=mid a) (4+1*(2*(sticky previous check s.exterior).work+4)) := by
    intro P R K machine pc reg pub exit inst «public» cfg mid entry _
    have ass:=step_exec previous check s.exterior s.dest mid (fits _ (by omega)) (fits _ (by dsimp [check];omega))
      (fits _ (by omega)) p.end_
    obtain ⟨t,ht,state,o,act,done,eqn⟩:=ass.1 machine pc reg pub exit inst «public» cfg mid entry rfl
    subst o
    exact ⟨t,ht,state,_,act,done,ass.2.2⟩
  let firstP := DescentPackedProfileValidity.proc s.banks w s.grain s.source.seats s.out
  let lastP := step w previous check s.exterior s.dest
  refine ⟨?_,@cheap_seq w firstP lastP (@cheap)
    (@ProtocolRAM.scan_cheap w s.dest 1 (sticky previous check s.exterior))⟩
  refine Procedure.Spec.mono (A:=firstP.seq lastP)
    (Procedure.Spec.seq (A:=firstP) (B:=lastP) (@test) (@last) (fun _ _ _=>trivial))
    (fun _ h=>h) ?_ le_rfl
  rintro _ o ⟨mid,stage,done⟩
  refine ⟨?_,fun i hi=>(done.2 i (by omega)).trans (stage.2 i (Or.inl (by omega)))⟩
  have hold := one_ne (w:=w) (by omega)
  have flag : mid check=(if (view s m z).Valid then 0 else 1) := by
    by_cases valid : (view s m z).Valid
    · rw [ite_eq_left valid]
      exact stage.1.trans (ite_eq_left valid)
    · rw [ite_eq_right valid]
      exact stage.1.trans (ite_eq_right valid)
  rw [done.1,flag,stage.2 previous (Or.inl early),stage.2 s.exterior (Or.inl (by omega))]
  by_cases valid : (view s m z).Valid <;> simp [valid,hold]

theorem transfer {low : ℕ} (s : Stage A) (p : Paid w low s) (z : A→Bool) {m mid : Memory w}
    (frame : ∀a < low,mid a=m a) (input : Reads s.banks m s.source.pin z s.grain) :
    Reads s.banks mid s.source.pin z s.grain ∧ view s mid z=view s m z := by
  have at_ (b : Bank) (in_ : b∈[s.banks.source,s.banks.starts,s.banks.shifts,s.banks.dictionary,s.banks.count])
      (j : ℕ) (small : j < b.size) : mid (b.base+j)=m (b.base+j) := by
    have lb:=p.retained b in_;apply frame;omega
  have count_ : mid s.banks.count.base=m s.banks.count.base := by
    simpa only [Nat.add_zero] using at_ s.banks.count (by simp) 0 p.space.count.1
  refine ⟨⟨?_,?_,?_,?_⟩,by simp [view,count_]⟩
  · intro i
    exact (at_ s.banks.source (by simp) i.val (i.isLt.trans_le p.space.sourceSize)).trans (input.source i)
  · intro i
    exact (at_ s.banks.starts (by simp) i.val (i.isLt.trans_le p.space.startsSize)).trans (input.starts i)
  · intro u h
    exact (at_ s.banks.shifts (by simp) u ((Nat.lt_succ_of_le h).trans_le p.space.shiftsSize)).trans
      (input.shifts u h)
  · intro u hu key
    let K:=2^(DescentTerminalEpochBits.width s.source.C*s.grain)
    have hk : key.val < K:=key.isLt
    have hmul:=Nat.mul_le_mul_right K hu
    have inside : bankShift s.source.C s.grain u+key.val < tariff s.source.C s.grain := by
      change u*K+key.val < (s.grain+1)*K
      rw [Nat.add_mul,Nat.one_mul]
      omega
    exact (at_ s.banks.dictionary (by simp) (bankShift s.source.C s.grain u+key.val)
      (inside.trans_le p.space.dictSize)).trans (input.dictionary u hu key)

private theorem joinedCheap {first after : Procedure w} {P Q : Prop}
    (head : P ∧ CheapCode first) (tail : Q ∧ CheapCode after) : CheapCode (first.seq after) :=
  @cheap_seq w first after head.2 tail.2

theorem run (low previous final : ℕ) (ss : List (Stage A)) (z : A→Bool) (m : Memory w)
    (safe : Order w low previous final ss) (paid : ∀s∈ss,Paid w low s)
    (data_ : ∀s∈ss,Reads s.banks m s.source.pin z s.grain) :
    (fold w previous final ss).Spec (·=m) (fun _ o=>
      (o final=if m previous=0 ∧ ∀s∈ss,m s.exterior=0 ∧ (view s m z).Valid then 0 else 1) ∧
      ∀i < low,o i=m i) (bill previous final ss) ∧ CheapCode (fold w previous final ss) := by
  induction ss generalizing previous m with
  | nil=>
    obtain ⟨small,top,space⟩:=safe
    have f : (Bank.mk previous 0).Fits w final:=by change 0 < 1 ∧ 1 < 2^w ∧ previous+1 ≤ final;omega
    have st:=step_exec previous previous previous final m f f f space
    refine ⟨?_,st.2.1⟩
    refine @Procedure.Spec.mono w (step w previous previous previous final) (·=m) (·=m)
      (fun _ o=>o=image final 1 (sticky previous previous previous) m) _ _ _
      st.1 (fun _ h=>h) ?_ le_rfl
    intro _ o eqn
    subst o
    exact ⟨by simpa using st.2.2.1,fun i hi=>st.2.2.2 i (by omega)⟩
  | cons s ss ih=>
    obtain ⟨earlier,rest⟩:=safe
    have ps:=paid s (by simp)
    have hd:=single_run previous low s z m ps earlier (data_ s (by simp))
    let next (mid : Memory w) := (mid s.dest=if m previous=0 ∧ m s.exterior=0 ∧ (view s m z).Valid then 0 else 1) ∧
      ∀a < low,mid a=m a
    let post (mid o : Memory w):=(o final=if mid s.dest=0 ∧ ∀b∈ss,mid b.exterior=0 ∧ (view b mid z).Valid then 0 else 1) ∧
      ∀i < low,o i=mid i
    have ps' : ∀q∈ss,Paid w low q:=fun q h=>paid q (by simp [h])
    have ds' : ∀q∈ss,Reads q.banks m q.source.pin z q.grain:=fun q h=>data_ q (by simp [h])
    let firstP := single w previous s
    let restP := fold w s.dest final ss
    have restRun (src : Memory w) (stored : ∀q∈ss,Reads q.banks src q.source.pin z q.grain) :
        restP.Spec (·=src) (fun _ o=>post src o) (bill s.dest final ss) ∧ CheapCode restP :=
      ih s.dest src rest ps' stored
    have tail : restP.Spec next post (bill s.dest final ss) := by
      intro P R K machine pc reg pub exit inst «public» cfg mid entry started
      have ds : ∀q∈ss,Reads q.banks mid q.source.pin z q.grain:=fun q h=>
        (transfer q (ps' q h) z started.2 (ds' q h)).1
      exact (restRun mid ds).1 machine pc reg pub exit inst «public» cfg mid entry rfl
    have program : (firstP.seq restP).Spec (·=m) (fun _ o=>∃mid,next mid ∧ post mid o)
        (singleCost previous s + bill s.dest final ss) :=
      @Procedure.Spec.seq w firstP restP (·=m) next (fun _ mid=>next mid) post
        (singleCost previous s) (bill s.dest final ss) hd.1 (@tail) (fun _ _ h=>h)
    change _ ∧ CheapCode (firstP.seq restP)
    refine ⟨?_,@joinedCheap w firstP restP _ _ hd (restRun m ds')⟩
    refine @Procedure.Spec.mono w (firstP.seq restP) (·=m) (·=m) (fun _ o=>∃mid,next mid ∧ post mid o) _
      (singleCost previous s + bill s.dest final ss) (bill previous final (s::ss)) (@program)
      (fun _ h=>h) ?_ le_rfl
    rintro _ o ⟨mid,head,done⟩
    refine ⟨?_,fun i hi=>(done.2 i hi).trans (head.2 i hi)⟩
    have terms : (∀q∈ss,mid q.exterior=0 ∧ (view q mid z).Valid) ↔ ∀q∈ss,m q.exterior=0 ∧ (view q m z).Valid := by
      constructor <;> intro keep q h <;> have eqn:=(transfer q (ps' q h) z head.2 (ds' q h)).2 <;>
        have ext_:=head.2 _ (ps' q h).ext
      · simpa only [eqn,ext_] using keep q h
      · simpa only [eqn,ext_] using keep q h
    have nonzero:=one_ne (w:=w) (by have :=ps.end_;omega)
    rw [done.1,head.1]
    simp only [List.forall_mem_cons,terms]
    by_cases prior : m previous=0 <;> by_cases exterior : m s.exterior=0 <;>
      by_cases valid : (view s m z).Valid <;> simp [prior,exterior,valid,nonzero]

end
end Hierarchy.DescentPackedEpochFold

end OAI
