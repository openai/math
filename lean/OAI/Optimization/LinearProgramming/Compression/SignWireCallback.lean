import OAI.Optimization.LinearProgramming.Compression.SignWireRead
import OAI.Optimization.LinearProgramming.Compression.SignWireReply
import OAI.Optimization.LinearProgramming.NativePrice.BitRAM
import OAI.Optimization.LinearProgramming.BitRAM.ServiceRaw

/-! Decode a BitRAM lattice query and return its three-way sign through the
public scalar-bit packet interface. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM RAM.Callable NativePrice _root_.OAI.Optimization.LinearProgramming.Lattice

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def Protected (m t : Memory K) : Prop :=
  ∀ i, 31 ≤ i → i%2=1 → i ≠ 47 → i ≠ 49 → t.index i=m.index i

/-- The numerical service receives a contiguous integer input row and returns
the raw three-way native comparison tag in address 14. -/
def ReadsTagged {p : ℕ} (code : Fragment) (order : (Fin p → ℤ) → Ordering) (out bound : ℕ)
    (P : K → Prop) (env : Memory K → Prop) (allowed : (Fin p → ℤ) → Prop) : Prop :=
  ∀ (row : Fin p → ℤ), allowed row → ∀ m, m.AllData P → env m → m.index 53=out →
    (∀ i, m.data (out+i.val)=(row i:K)) →
    ∃ t, code.Run P m bound t ∧ t.index 14=comparisonTag (order row) ∧
      3 ≤ t.index 47 ∧ Protected m t

/-- A sign service may also return its exact application state to the enclosing
bit-program controller after producing the tag. -/
def ReadsTaggedWith {p : ℕ} (code : Fragment) (order : (Fin p → ℤ) → Ordering) (out bound : ℕ)
    (P : K → Prop) (env : Memory K → Prop) (allowed : (Fin p → ℤ) → Prop)
    (post : (Fin p → ℤ) → Memory K → Memory K → Prop) : Prop :=
  ∀ (row : Fin p → ℤ), allowed row → ∀ m, m.AllData P → env m → m.index 53=out →
    (∀ i, m.data (out+i.val)=(row i:K)) →
    ∃ t, code.Run P m bound t ∧ t.index 14=comparisonTag (order row) ∧
      3 ≤ t.index 47 ∧ Protected m t ∧ post row m t

theorem ReadsTaggedWith.forget {p out bound : ℕ} {code : Fragment} {order : (Fin p → ℤ) → Ordering}
    {P : K → Prop} {env : Memory K → Prop} {allowed : (Fin p → ℤ) → Prop} {post}
    (h : ReadsTaggedWith code order out bound P env allowed post) : ReadsTagged code order out bound P env allowed := by
  intro row permit m hm e ptr values
  obtain ⟨t,r,tag,base,frame,_⟩ := h row permit m hm e ptr values
  exact ⟨t,r,tag,base,frame⟩

structure WireReadFrame (m u : Memory K) (out p : ℕ) : Prop where
  data : ∀ i, (i < 3 ∨ 8 < i) → (i < out ∨ out+p ≤ i) → u.data i=m.data i
  index : ∀ i, (i < 3 ∨ 6 < i) → i ≠ 10 → i ≠ 11 → i ≠ 12 → u.index i=m.index i

structure ReplyWriteFrame (y t : Memory K) : Prop where
  base : t.index 47=y.index 47
  index : ∀ i, i ≠ 16 → i ≠ 18 → i ≠ 46 → i ≠ 49 → t.index i=y.index i
  data : ∀ i, 2 ≤ i → i ≠ y.index 47 → i ≠ y.index 47+1 → t.data i=y.data i

/-- Set the dimension and row destination from the service's two scratch
header registers. -/
def wireRowSetup : Block := .straight [.addrCopy 10 51,.addrCopy 12 53]

def wordSignFragment (compare : Fragment) : Fragment :=
  .seq (.ofBlock wireRowSetup) (.seq (.ofBlock signRowReadBlock)
    (.seq compare (.ofBlock signReplyBlock)))

theorem wordSignFragment_rawReply_capture {p : ℕ} (P : K → Prop) (row : Fin p → ℤ)
    (order : (Fin p → ℤ) → Ordering) (compare : Fragment) (B base out : ℕ)
    (m : Memory K) (hm : m.AllData P) (hp0 : P 0) (hp1 : P 1)
    (hbase : m.index 43=base) (hlen : m.index 37=(signRowWord row).length)
    (hdim : m.index 51=p) (hout : m.index 53=out) (hlo : 9 ≤ base)
    (hsep : base+(signRowWord row).length ≤ out)
    (hw : BitRAM.ScalarPacket m base (signRowWord row))
    (hP : ∀ i, ∀ z : ℕ, z ≤ 2^(row i).natAbs.bits.length → P (z:K))
    (hrow : ∀ i, P (row i:K)) (env : Memory K → Prop)
    (carry : ∀ s : Memory K, s.AllData P →
      (∀ i, (i < 3 ∨ 8 < i) → (i < out ∨ out+p ≤ i) → s.data i=m.data i) →
      (∀ i, (i < 3 ∨ 6 < i) → i ≠ 10 → i ≠ 11 → i ≠ 12 → s.index i=m.index i) → env s)
    (allowed : (Fin p → ℤ) → Prop) (ha : allowed row)
    (post : (Fin p → ℤ) → Memory K → Memory K → Prop)
    (hc : ReadsTaggedWith compare order out B P env allowed post) :
    ∃ t, BitRAM.NativeService.RawReply (wordSignFragment compare) P m
      (16*(signRowWord row).length+13*p+B+19) (signReply (order row)) t ∧
      ∃ u y, WireReadFrame m u out p ∧ post row u y ∧ ReplyWriteFrame y t := by
  let u := m.putIndex 10 (m.index 51)
  let v := u.putIndex 12 (u.index 53)
  have hu : u.AllData P := hm
  have hv : v.AllData P := hu
  have setup : Block.Eval (Memory.AllData P) wireRowSetup m 2 v :=
    (Block.Eval.op_addrCopy m 10 51 hm hu).seq ((Block.Eval.op_addrCopy u 12 53 hu hv).seq (.skip hv))
  obtain ⟨s,k,hk,er,_,_,rs,df,af⟩ := signRowReadBlock_spec P row v base out hv hp0
    (by simpa [v,u] using hbase) (by simpa [v,u] using hlen) (by simp [v,u,hdim])
    (by simp [v,u,hout]) hlo hsep ((scalarPacket_iff_wordAt m base _).mp hw) hP hrow
  have fa (i : ℕ) (hi : i < 3 ∨ 6 < i) (h10 : i ≠ 10) (h11 : i ≠ 11) (h12 : i ≠ 12) :
      s.index i=m.index i := by simpa [v,u,h10,h12] using af i hi h11 h12
  obtain ⟨y,ec,tag,space,frame,effect⟩ := hc row ha s er.safe_end (carry s er.safe_end df fa)
    ((fa _ (by decide) (by decide) (by decide) (by decide)).trans hout) rs
  obtain ⟨t,j,hj,ew,reply,rb,rl,fi,fd⟩ := signReplyBlock_spec P (order row) y (y.index 47)
    ec.safe_end tag rfl (by omega) hp0 hp1
  refine ⟨t,⟨?_,?_,?_,?_⟩,s,y,⟨df,fa⟩,effect,rb,fi,fd⟩
  · exact ((Fragment.Run.ofBlock setup).seq ((Fragment.Run.ofBlock er).seq
      (ec.seq (Fragment.Run.ofBlock ew)))).mono (by omega)
  · change BitRAM.ScalarPacket t (t.index 47) _
    rw [rb]
    exact (scalarPacket_iff_wordAt _ _ _).mpr reply
  · change t.index 49=_
    simpa using rl
  · intro i low odd hb hl
    change i ≠ 47 at hb
    change i ≠ 49 at hl
    exact (fi i (by omega) (by omega) (by omega) hl).trans
      ((frame i low odd hb hl).trans (fa i (by omega) (by omega) (by omega) (by omega)))

theorem wordSignFragment_rawReply {p : ℕ} (P : K → Prop) (row : Fin p → ℤ)
    (order : (Fin p → ℤ) → Ordering) (compare : Fragment) (B base out : ℕ)
    (m : Memory K) (hm : m.AllData P) (hp0 : P 0) (hp1 : P 1)
    (hbase : m.index 43=base) (hlen : m.index 37=(signRowWord row).length)
    (hdim : m.index 51=p) (hout : m.index 53=out) (hlo : 9 ≤ base)
    (hsep : base+(signRowWord row).length ≤ out)
    (hw : BitRAM.ScalarPacket m base (signRowWord row))
    (hP : ∀ i, ∀ z : ℕ, z ≤ 2^(row i).natAbs.bits.length → P (z:K))
    (hrow : ∀ i, P (row i:K)) (env : Memory K → Prop)
    (carry : ∀ s : Memory K,
      (∀ i, (i < 3 ∨ 8 < i) → (i < out ∨ out+p ≤ i) → s.data i=m.data i) →
      (∀ i, (i < 3 ∨ 6 < i) → i ≠ 10 → i ≠ 11 → i ≠ 12 → s.index i=m.index i) → env s)
    (allowed : (Fin p → ℤ) → Prop) (ha : allowed row)
    (hc : ReadsTagged compare order out B P env allowed) :
    ∃ t, BitRAM.NativeService.RawReply (wordSignFragment compare) P m
      (16*(signRowWord row).length+13*p+B+19) (signReply (order row)) t := by
  have full : ReadsTaggedWith compare order out B P env allowed (fun _ _ _ => True) := by
    intro r permit z hz e ptr vals
    obtain ⟨t,run,tag,base',fr⟩ := hc r permit z hz e ptr vals
    exact ⟨t,run,tag,base',fr,trivial⟩
  obtain ⟨t,reply,_⟩ := wordSignFragment_rawReply_capture P row order compare B base out m hm hp0 hp1
    hbase hlen hdim hout hlo hsep hw hP hrow env (fun z _ => carry z) allowed ha _ full
  exact ⟨t,reply⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
