import OAI.Computability.VPVNP.PrimedInputRAMOpcodePortResult
import OAI.Computability.VPVNP.PrimedInputRAMPortRun

/-!
# Word-level correctness of the rectangular input dispatcher

The opcode table compares each flat position against the prefix, address,
header and incident-port boundaries. It returns a literal or a source address
together with the bit's first-pass owner flag. Only private register operations
are performed between the parameter loads and the final choice or copy.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Opcodes

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM RAMLayout

/-- Values required at dispatch entry, including the packed literal prefix
and the arithmetic bounds for the exclusive ends of the input fields. -/
structure DispatchInput (L : Lengths) (n r H w base P g v j : ℕ) (prefixAt : ℕ → Bool)
    (pub : Pub → Word w) (rs : Regs w 48) : Prop where
  header : HeaderRegisters rs L base n r P g v (rs 25).val
  sites : (rs 7).val = 2^r
  incidentWidth : (rs 13).val = width r H w
  bit : (rs 24).val = j
  validSite : v < 2^r
  prefixMatches : ∀ t < P, (rs 17).val.testBit t = prefixAt t
  boundaryFits : P+r+4+width r H w < 2^w
  portBlock : (pub 13).val = blockBits H w
  portFirst : (pub 14).val = 8*w
  portBase : (pub 15).val = 16*w

/-- Registers 26, 27 and 28 return the payload, fetch flag and owner.
All registers below 32 other than temporary offset 25 have their specified
field-result values, including the next cursor and write destination. -/
def DispatchOutput {w : ℕ} (before after : Regs w 48) (d : RawCopy × Bool) : Prop :=
  ∀ i : Reg, i.val < 32 → i ≠ 25 → after i = fieldResult before d i

private theorem output_field {w : ℕ} {rs tmp : Regs w 48} (d : RawCopy × Bool)
    (hp : ∀ i : Reg, i.val < 32 → i ≠ 25 → tmp i = rs i) :
    DispatchOutput rs (fieldResult tmp d) d := by
  intro i hi h25
  by_cases h26 : i = 26
  · subst i; simp
  by_cases h27 : i = 27
  · subst i; simp
  by_cases h28 : i = 28
  · subst i; simp
  rw [fieldResult_other _ _ _ h26 h27 h28, fieldResult_other _ _ _ h26 h27 h28]
  exact hp i hi h25

private abbrev Ticks {w : ℕ} (pub : Pub → Word w) (state : Word w) (m : Memory w)
    (a : Code) (rs : Regs w 48) (cost : ℕ) (out : Regs w 48) :=
  Flow.Exec pub state a rs m (List.replicate cost .tick) out m

private theorem seqTicks {w : ℕ} {pub : Pub → Word w} {state : Word w} {m : Memory w}
    {a b : Code} {rs middle final : Regs w 48} {x y : ℕ}
    (ha : Ticks pub state m a rs x middle) (hb : Ticks pub state m b middle y final) :
    Ticks pub state m (a.seq b) rs (x+y) final := by simpa [Ticks] using ha.seq hb

private theorem yesTicks {w : ℕ} {pub : Pub → Word w} {state : Word w} {m : Memory w}
    {a b : Code} {rs out : Regs w 48} {t : ℕ} {l q : Reg} (test : rs l < rs q)
    (ha : Ticks pub state m a rs t out) : Ticks pub state m (.ifLt l q a b) rs (t+1) out :=
  Flow.Exec.ifLtYes test ha

private theorem noTicks {w : ℕ} {pub : Pub → Word w} {state : Word w} {m : Memory w}
    {a b : Code} {rs out : Regs w 48} {t : ℕ} {l q : Reg} (test : ¬rs l < rs q)
    (hb : Ticks pub state m b rs t out) : Ticks pub state m (.ifLt l q a b) rs (t+1) out :=
  Flow.Exec.ifLtNo test hb

private theorem binTicks {w : ℕ} (pub : Pub → Word w) (state : Word w) (m : Memory w)
    (op : BinaryOp) (dst lhs rhs : Reg) (rs : Regs w 48) :
    Ticks pub state m (bin op dst lhs rhs) rs 1
      (Function.update rs dst (op.eval (rs lhs) (rs rhs))) := .line rfl

private theorem addVal {w : ℕ} (x y : Word w) (h : x.val + y.val < 2^w) :
    (BinaryOp.add.eval x y).val = x.val + y.val := Fin.val_add_eq_of_add_lt h

private theorem subVal {w : ℕ} (x y : Word w) (h : y.val ≤ x.val) :
    (BinaryOp.sub.eval x y).val = x.val - y.val := Fin.sub_val_of_le h

private theorem changeHeader {w : ℕ} {rs tmp : Regs w 48} {L : Lengths} {base n r P g v old j : ℕ}
    (h : HeaderRegisters rs L base n r P g v old)
    (hp : ∀ i : Reg, i.val < 25 → tmp i = rs i) (hj : (tmp 25).val = j) :
    HeaderRegisters tmp L base n r P g v j := by
  rcases h with ⟨h0,h1,h2,h3,hn,hr,hb,hP,hi,ha,hm,hl,hM,hR,hg,hv,_⟩
  constructor <;> first | exact hj | (rwa [hp _ (by decide)])

private theorem port_exec {w : ℕ} (pub : Pub → Word w) (state : Word w) (rs : Regs w 48)
    (m : Memory w) {L : Lengths} {n r H base P g v k : ℕ}
    (ih : HeaderRegisters rs L base n r P g v k) (hR : (rs 7).val = 2^r)
    (hv : v < 2^r) (hk : k < width r H w) (hb : (pub 13).val = blockBits H w)
    (h₁ : (pub 14).val = 8*w) (h₂ : (pub 15).val = 16*w) :
    ∃ cost out, Ticks pub state m (sequence PortCode.program [portResult]) rs cost out ∧
      cost ≤ 3*r+33 ∧ DispatchOutput rs out (dispatchPort base n r H w P g v k).1 := by
  let u : Fin (2^r) := ⟨v,hv⟩
  let i : Fin (width r H w) := ⟨k,hk⟩
  have hp : PortCode.Input r H u i pub rs :=
    ⟨ih.zero, ih.one, ih.two, hR, ih.site, ih.offset, hb, h₁, h₂⟩
  obtain ⟨a,mid,hmid,ha,hm⟩ := PortCode.program_exec (state := state) (m := m) u i rs hp
  have keep := PortCode.program_preserves hmid
  have hr : PortResultRegisters mid base n r P g v k := by
    rcases ih with ⟨hz,ho,_,h3,hn,hs,hbase,hP,_,_,_,_,_,_,hg,hv',hk'⟩
    constructor <;> rwa [keep _ (by decide)]
  obtain ⟨b,ht,hout⟩ := exec_portResult pub state mid m hr hm
  refine ⟨a+b,_,seqTicks hmid hout,by omega,output_field _ (fun j hj _ ↦ keep j hj)⟩

private theorem output_trans {w : ℕ} {rs mid out : Regs w 48} {d : RawCopy × Bool}
    (h : DispatchOutput mid out d) (hkeep : ∀ i : Reg, i.val < 32 → i ≠ 25 → mid i = rs i) :
    DispatchOutput rs out d := fun i hi h25 ↦ (h i hi h25).trans (output_field d hkeep i hi h25)

/-- The complete dispatcher computes the paper's scalar decision with
finite word instructions. Its trace has no external probes and uses only
private ticks, even at a missing port or on inconsistent message data. -/
theorem dispatch_exec {w : ℕ} (pub : Pub → Word w) (state : Word w) (rs : Regs w 48) (m : Memory w)
    {L : Lengths} {n r H base P g v j : ℕ} {prefixAt : ℕ → Bool}
    (I : DispatchInput L n r H w base P g v j prefixAt pub rs) :
    ∃ cost out, Flow.Exec pub state (dispatch PortCode.program) rs m (List.replicate cost .tick) out m ∧
      cost ≤ 3*r+128 ∧ DispatchOutput rs out (dispatchRow L n r H w base P prefixAt g v j).1 := by
  let ih := I.header
  have hw : 0 < w := by
    have h := (rs 1).isLt
    rw [ih.one] at h
    by_contra hz
    have he : w = 0 := by omega
    simp [he] at h
  have hone : rs 1 = 1 := by
    apply Fin.ext
    simpa [Fin.val_one, Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')] using ih.one
  have hb := I.boundaryFits
  by_cases hprefix : j < P
  · have test : rs 24 < rs 12 := by simpa [Fin.lt_def, I.bit, ih.prefixWidth] using hprefix
    have hh := exec_literalBit pub state rs m hw hone 17 24
    rw [I.bit, I.prefixMatches j hprefix] at hh
    rw [dispatchRow, ite_eq_left hprefix]
    exact ⟨5,_,Flow.Exec.ifLtYes test hh,by omega,output_field _ (fun _ _ _ ↦ rfl)⟩
  have testPrefix : ¬ rs 24 < rs 12 := by simpa [Fin.lt_def, I.bit, ih.prefixWidth] using hprefix
  let a := Function.update rs (35 : Reg) (BinaryOp.add.eval (rs 12) (rs 8))
  have ha := binTicks pub state m .add 35 12 8 rs
  have av : (a 35).val = P+r := by
    change (BinaryOp.add.eval (rs 12) (rs 8)).val = _
    rw [addVal,ih.prefixWidth,ih.siteBits]
    rw [ih.prefixWidth,ih.siteBits]; omega
  by_cases haddr : j < P+r
  · have test : a 24 < a 35 := by change (rs 24).val < (a 35).val; rw [I.bit,av]; exact haddr
    let b := Function.update a (25 : Reg) (BinaryOp.sub.eval (a 24) (a 12))
    have hsub := binTicks pub state m .sub 25 24 12 a
    have bv : (b 25).val = j-P := by
      change (BinaryOp.sub.eval (rs 24) (rs 12)).val = _
      rw [subVal, I.bit, ih.prefixWidth]
      rw [I.bit, ih.prefixWidth]; omega
    have hh := exec_literalBit pub state b m hw (show b 1 = 1 from hone) 23 25
    rw [bv, show (b 23).val = v from ih.site] at hh
    rw [dispatchRow, ite_eq_right hprefix, ite_eq_left haddr]
    refine ⟨8,_,noTicks testPrefix (seqTicks ha (yesTicks test (seqTicks hsub hh))),by omega,
      output_field _ ?_⟩
    intro i hi h25
    have h35 : i ≠ 35 := fun he ↦ by subst i; omega
    simp [a,b,h25,h35]
  have testAddress : ¬a 24 < a 35 := by
    change ¬ (rs 24).val < (a 35).val
    rw [I.bit,av]; exact haddr
  let b := Function.update a (25 : Reg) (BinaryOp.sub.eval (a 24) (a 35))
  let c := Function.update b (35 : Reg) (BinaryOp.add.eval (b 35) (b 3))
  let e := Function.update c (35 : Reg) (BinaryOp.add.eval (c 35) (c 1))
  have hbc := seqTicks (binTicks pub state m .sub 25 24 35 a) (binTicks pub state m .add 35 35 3 b)
  have hbe := seqTicks hbc (binTicks pub state m .add 35 35 1 c)
  have b25 : (b 25).val = j-(P+r) := by
    change (BinaryOp.sub.eval (rs 24) (a 35)).val = _
    rw [subVal, I.bit, av]
    rw [I.bit,av]; omega
  have c35 : (c 35).val = P+r+3 := by
    change (BinaryOp.add.eval (a 35) (rs 3)).val = _
    rw [addVal, av, ih.three]
    rw [av,ih.three]; omega
  have e35 : (e 35).val = P+r+4 := by
    change (BinaryOp.add.eval (c 35) (rs 1)).val = _
    rw [addVal, c35, ih.one]
    rw [c35,ih.one]; omega
  have keepE (i : Reg) (hi : i.val < 32) (h25 : i ≠ 25) : e i = rs i := by
    have h35 : i ≠ 35 := by intro he; subst i; omega
    simp [a,b,c,e,h25,h35]
  by_cases hhead : j < P+r+4
  · have test : e 24 < e 35 := by change (rs 24).val < _; rw [I.bit,e35]; exact hhead
    have heh := changeHeader ih
      (tmp := e) (fun i hi ↦ keepE i (by omega) (fun h ↦ by subst i; omega))
      (j := j-(P+r)) (show (e 25).val = _ from b25)
    obtain ⟨t,ht,hh⟩ := exec_headerFields pub state e m heh (by omega)
    rw [dispatchRow, ite_eq_right hprefix, ite_eq_right haddr, ite_eq_left hhead]
    have hmax : headerFields.length ≤ 100 := by decide
    refine ⟨_,_,noTicks testPrefix (seqTicks ha (noTicks testAddress (seqTicks hbe (yesTicks test hh)))),
      ?_,output_field _ keepE⟩
    omega
  have testHeader : ¬e 24 < e 35 := by change ¬ (rs 24).val < _; rw [I.bit,e35]; exact hhead
  let f := Function.update e (25 : Reg) (BinaryOp.sub.eval (e 24) (e 35))
  let z := Function.update f (35 : Reg) (BinaryOp.add.eval (f 35) (f 13))
  have hfz := seqTicks (binTicks pub state m .sub 25 24 35 e) (binTicks pub state m .add 35 35 13 f)
  have z25 : (z 25).val = j-(P+r+4) := by
    change (BinaryOp.sub.eval (rs 24) (e 35)).val = _
    rw [subVal, I.bit, e35]
    rw [I.bit,e35]; omega
  have z35 : (z 35).val = P+r+4+width r H w := by
    change (BinaryOp.add.eval (e 35) (rs 13)).val = _
    rw [addVal, e35, I.incidentWidth]
    rw [e35,I.incidentWidth]; exact hb
  have keepZ (i : Reg) (hi : i.val < 32) (h25 : i ≠ 25) : z i = rs i := by
    have h35 : i ≠ 35 := by intro he; subst i; omega
    simp [z,f,h35,h25,keepE i hi h25]
  by_cases hport : j < P+r+4+width r H w
  · have test : z 24 < z 35 := by change (rs 24).val < _; rw [I.bit,z35]; exact hport
    have heh := changeHeader ih
      (tmp := z) (fun i hi ↦ keepZ i (by omega) (fun h ↦ by subst i; omega)) z25
    obtain ⟨t,out,hr,ht,hd⟩ := port_exec pub state z m heh (show (z 7).val = _ from I.sites)
      I.validSite (by omega) I.portBlock I.portFirst I.portBase
    rw [dispatchRow, ite_eq_right hprefix, ite_eq_right haddr, ite_eq_right hhead, ite_eq_left hport]
    refine ⟨_,out,noTicks testPrefix (seqTicks ha (noTicks testAddress (seqTicks hbe (noTicks testHeader
      (seqTicks hfz (yesTicks test hr)))))),?_,output_trans hd keepZ⟩
    omega
  · have test : ¬ z 24 < z 35 := by change ¬ (rs 24).val < _; rw [I.bit,z35]; exact hport
    rw [dispatchRow, ite_eq_right hprefix, ite_eq_right haddr, ite_eq_right hhead, ite_eq_right hport]
    exact ⟨13,_,noTicks testPrefix (seqTicks ha (noTicks testAddress (seqTicks hbe (noTicks testHeader
      (seqTicks hfz (noTicks test (exec_literalZero pub state z m))))))),by omega,output_field _ keepZ⟩

end PrimedInputRAM.Opcodes

end VPVNP
end Computability
end OAI
