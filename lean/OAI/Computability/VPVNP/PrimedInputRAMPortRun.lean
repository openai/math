import OAI.Computability.VPVNP.PrimedInputRAMPortCode
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval

/-!
# Private register execution of the primed transcript port block

The triangular scan stops at the unique phase containing the exchange ordinal.
Every executed instruction produces a tick and leaves external memory untouched.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.PortCode

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM RAMLayout

variable {w : ℕ} {pub : Fin 16 → Word w} {state : Word w} {m : Memory w}

/-- The port block executes for exactly `k` private ticks, takes the given initial registers to
the specified final registers and preserves external memory. -/
abbrev Ticks (pub : Fin 16 → Word w) (state : Word w) (m : Memory w) (a : Block)
    (rs : Regs w 48) (k : ℕ) (out : Regs w 48) : Prop :=
  Flow.Exec pub state a rs m (List.replicate k .tick) out m

private theorem seqTicks {a b : Block} {rs s t : Regs w 48} {j k : ℕ}
    (x : Ticks pub state m a rs j s) (y : Ticks pub state m b s k t) :
    Ticks pub state m (.seq a b) rs (j+k) t := by simpa [Ticks] using x.seq y

private theorem copyTicks (pub : Fin 16 → Word w) (state : Word w) (m : Memory w)
    (dst src : Fin 48) (rs : Regs w 48) :
    Ticks pub state m (copy dst src) rs 1 (Function.update rs dst (rs src)) :=
  .line rfl

private theorem opTicks (pub : Fin 16 → Word w) (state : Word w) (m : Memory w)
    (op : BinaryOp) (dst lhs rhs : Fin 48) (rs : Regs w 48) :
    Ticks pub state m (binary op dst lhs rhs) rs 1
      (Function.update rs dst (op.eval (rs lhs) (rs rhs))) := .line rfl

private theorem pubTicks (pub : Fin 16 → Word w) (state : Word w) (m : Memory w)
    (dst : Fin 48) (j : Fin 16) (rs : Regs w 48) :
    Ticks pub state m (publicWord dst j) rs 1 (Function.update rs dst (pub j)) :=
  .line rfl

/-- With `gap` rows still to remove, the loop uses exactly `3*gap+1`
instructions. It preserves every register outside its two counters. -/
theorem scan_exec (pub : Fin 16 → Word w) (state : Word w) (m : Memory w)
    {d : ℕ} (l : Layer d) (gap p : ℕ) (hend : p + gap = l.phase) (rs : Regs w 48)
    (h₁ : (rs 1).val = 1) (hp : (rs 41).val = p)
    (hres : layerCount p + (rs 40).val = l.ordinal.val) :
    ∃ out, Ticks pub state m scan rs (3 * gap + 1) out ∧ (out 41).val = l.phase ∧
      (out 40).val = l.step ∧ ∀ i : Fin 48, i ≠ 40 → i ≠ 41 → out i = rs i := by
  change layerCount p + (rs 40).val = layerCount l.phase + l.step at hres
  induction gap generalizing p rs with
  | zero =>
    have hphase : p = l.phase := by omega
    rw [hphase] at hres
    have hstep := l.step_le
    refine ⟨rs, Flow.Exec.whileDone ?_, by omega, by omega, fun _ _ _ ↦ rfl⟩
    change ¬ (rs 41).val < (rs 40).val
    omega
  | succ gap ih =>
    have hnext : layerCount (p+1) ≤ layerCount l.phase := layerCount_mono (by omega)
    rw [layerCount_next] at hnext
    have htest : rs 41 < rs 40 := by change (rs 41).val < (rs 40).val; omega
    have hadd : (rs 41).val + (rs 1).val < 2 ^ w := by
      have := (rs 40).isLt
      omega
    let a := Function.update rs (41 : Fin 48) (BinaryOp.add.eval (rs 41) (rs 1))
    let b := Function.update a (40 : Fin 48) (BinaryOp.sub.eval (a 40) (a 41))
    have ha : (a 41).val = p + 1 := by
      simp [a, BinaryOp.eval, Fin.val_add_eq_of_add_lt hadd, hp, h₁]
    have ha40 : a 40 = rs 40 := by simp [a]
    have hle : a 41 ≤ a 40 := by change (a 41).val ≤ (a 40).val; rw [ha, ha40]; omega
    have hb : (b 40).val = (rs 40).val - (p + 1) := by
      rw [show b 40 = a 40 - a 41 by simp [b, BinaryOp.eval], Fin.sub_val_of_le hle, ha40, ha]
    have hb41 : (b 41).val = p + 1 := by simpa [b, Function.update_apply] using ha
    have hb1 : (b 1).val = 1 := by simpa [b, a, Function.update_apply] using h₁
    have hstep : Ticks pub state m scanStep rs 2 b :=
      seqTicks (opTicks pub state m .add 41 41 1 rs) (opTicks pub state m .sub 40 40 41 a)
    obtain ⟨out, ho, hphase, hval, hkeep⟩ := ih (p+1) (by omega) b hb1 hb41
      (by rw [layerCount_next, hb]; omega)
    refine ⟨out, ?_, hphase, hval, fun i hi hj ↦ ?_⟩
    · have hrun := Flow.Exec.whileStep htest hstep ho
      change Flow.Exec pub state scan rs m (List.replicate _ _) out m
      rw [show 3 * (gap+1) + 1 = (2 + (3 * gap + 1)) + 1 by omega, List.replicate_succ,
        List.replicate_add]
      exact hrun
    · rw [hkeep _ hi hj]
      simp [b, a, Function.update_of_ne hi, Function.update_of_ne hj]

private theorem div_val (x y : Word w) :
    (BinaryOp.div.eval x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt x.isLt)

private theorem mod_val (x y : Word w) :
    (BinaryOp.mod.eval x y).val = x.val % y.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le _ _).trans_lt x.isLt)

private theorem sub_val (x y : Word w) (h : y.val ≤ x.val) :
    (BinaryOp.sub.eval x y).val = x.val - y.val := Fin.sub_val_of_le h

private theorem receive_exec {d : ℕ} (l : Layer d) (rs : Regs w 48)
    (hzero : (rs 0).val = 0) (hone : (rs 1).val = 1) (htwo : (rs 2).val = 2)
    (hord : (rs 38).val / 2 = l.ordinal.val) (hpos : (rs 32).val = 1)
    (hk : (rs 37).val ≤ (rs 25).val) (hw : d ≤ w) (hv : (rs 23).val < 2 ^ d) :
    ∃ out, Ticks pub state m receiveSort rs (3 * l.phase + 7) out ∧
      result out = some (RAMSort.partner l.siteBit (rs 23).val, (rs 25).val - (rs 37).val) := by
  let a := Function.update rs (40 : Fin 48) (BinaryOp.div.eval (rs 38) (rs 2))
  let b := Function.update a (41 : Fin 48) (a 0)
  have hb40 : (b 40).val = l.ordinal.val := by simp [b, a, div_val, htwo, hord]
  obtain ⟨s,hs,hphase,hstep,hkeep⟩ := scan_exec pub state m l l.phase 0 (by omega) b
    (by simpa [b, a] using hone) (by simpa [b, a] using hzero)
    (by change 0 + (b 40).val = _; omega)
  have keep (i : Fin 48) (h₄₀ : i ≠ 40) (h₄₁ : i ≠ 41) : s i = rs i := by
    rw [hkeep _ h₄₀ h₄₁]
    simp [b, a, Function.update_of_ne h₄₀, Function.update_of_ne h₄₁]
  let c := Function.update s (42 : Fin 48) (BinaryOp.sub.eval (s 41) (s 40))
  let e := Function.update c (42 : Fin 48) (BinaryOp.shiftLeft.eval (c 1) (c 42))
  let f := Function.update e (33 : Fin 48) (BinaryOp.bitXor.eval (e 23) (e 42))
  let out := Function.update f (34 : Fin 48) (BinaryOp.sub.eval (f 25) (f 37))
  have hle : (s 40).val ≤ (s 41).val := by rw [hphase,hstep]; exact l.step_le
  have hc42 : (c 42).val = l.siteBit := by simp [c, sub_val _ _ hle, hstep,hphase, Layer.siteBit]
  have hc1 : (c 1).val = 1 := by simpa [c, keep] using hone
  have hbit : l.siteBit < w := l.siteBit_lt.trans_le hw
  have hpow := Nat.pow_lt_pow_right (by decide : 1 < 2) hbit
  have he42 : (e 42).val = 2 ^ l.siteBit := by
    simp [e, BinaryOp.eval, hc42, hbit, Nat.shiftLeft_eq, hc1, Nat.mod_eq_of_lt hpow]
  have he23 : e 23 = rs 23 := by simp [e,c,keep]
  have hxor : (e 23).val ^^^ (e 42).val < 2 ^ w := by
    rw [he23,he42]
    exact Nat.xor_lt_two_pow (hv.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hw)) hpow
  have hf33 : (f 33).val = RAMSort.partner l.siteBit (rs 23).val := by
    change (BinaryOp.bitXor.eval (e 23) (e 42)).val = _
    rw [show (BinaryOp.bitXor.eval (e 23) (e 42)).val = (e 23).val ^^^ (e 42).val from Nat.mod_eq_of_lt hxor, he23, he42]
    rfl
  have hf25 : f 25 = rs 25 := by simp [f,e,c,keep]
  have hf37 : f 37 = rs 37 := by simp [f,e,c,keep]
  have hsub : (f 37).val ≤ (f 25).val := by rwa [hf37,hf25]
  refine ⟨out, ?_, ?_⟩
  · have run := seqTicks (opTicks pub state m .div 40 38 2 rs) <|
      seqTicks (copyTicks pub state m 41 0 a) <|
      seqTicks hs <| seqTicks (opTicks pub state m .sub 42 41 40 s) <|
      seqTicks (opTicks pub state m .shiftLeft 42 1 42 c) <|
      seqTicks (opTicks pub state m .bitXor 33 23 42 e) (opTicks pub state m .sub 34 25 37 f)
    change Ticks pub state m receiveSort rs (1+(1+((3*l.phase+1)+(1+(1+(1+1)))))) out at run
    rw [show 3*l.phase+7 = 1+(1+((3*l.phase+1)+(1+(1+(1+1))))) by omega]
    exact run
  · have ho32 : (out 32).val = 1 := by simpa [out,f,e,c,keep] using hpos
    have ho33 : (out 33).val = RAMSort.partner l.siteBit (rs 23).val := by simpa [out] using hf33
    have ho34 : (out 34).val = (rs 25).val - (rs 37).val := by
      change (BinaryOp.sub.eval (f 25) (f 37)).val = _
      rw [sub_val _ _ hsub, hf25,hf37]
    simp [result, ho32,ho33,ho34]

private structure Prepared {d H : ℕ} {v : Fin (2 ^ d)} {k : Fin (width d H w)}
    (pub : Fin 16 → Word w) (rs : Regs w 48) : Prop extends Input d H v k pub rs where
  present : (rs 32).val = 1
  u : (rs 33).val = v.val
  t : (rs 34).val = k.val
  firstReg : (rs 35).val = 8 * w
  baseReg : (rs 36).val = 16 * w

private theorem sort_exec {d H : ℕ} (v : Fin (2 ^ d)) (l : Layer d) (dir : Fin 2)
    (j : Fin (blockBits H w)) (rs : Regs w 48)
    (I : Prepared (H := H) (v := v) (k := offset d H w (.inr (l,dir,j))) pub rs) :
    ∃ cost out, Ticks pub state m sort rs cost out ∧ cost ≤ 3 * d + 12 ∧
      result out = some ((if dir = 0 then v else l.partner v).val,
        (offset d H w (.inr (l,0,j))).val) := by
  let k := (offset d H w (.inr (l,dir,j))).val
  have hr : (rs 25).val = k := I.offset
  have hk : k = 16 * w + l.ordinal.val * (2 * blockBits H w) + dir.val * blockBits H w + j.val :=
    offset_sort ..
  have hbase : 16 * w ≤ k := by omega
  have hsub : k - 16 * w = blockBits H w * (2 * l.ordinal.val + dir.val) + j.val := by
    rw [hk, show 16 * w + l.ordinal.val * (2 * blockBits H w) + dir.val * blockBits H w + j.val =
      16 * w + (blockBits H w * (2 * l.ordinal.val + dir.val) + j.val) by ring, Nat.add_sub_cancel_left]
  have hchunk : (k - 16 * w) / blockBits H w = 2 * l.ordinal.val + dir.val := by
    rw [hsub, Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  let a := Function.update rs (37 : Fin 48) (pub 13)
  let b := Function.update a (38 : Fin 48) (BinaryOp.sub.eval (a 25) (a 36))
  let c := Function.update b (38 : Fin 48) (BinaryOp.div.eval (b 38) (b 37))
  let s := Function.update c (39 : Fin 48) (BinaryOp.mod.eval (c 38) (c 2))
  have hle : (a 36).val ≤ (a 25).val := by simpa [a, I.baseReg, hr] using hbase
  have hb : (b 38).val = k - 16 * w := by
    change (BinaryOp.sub.eval (a 25) (a 36)).val = _
    rw [sub_val _ _ hle]
    simp [a, I.baseReg, hr]
  have hb37 : (b 37).val = blockBits H w := by simp [a,b,I.block]
  have hc : (c 38).val = 2 * l.ordinal.val + dir.val := by
    change (BinaryOp.div.eval (b 38) (b 37)).val = _
    rw [div_val,hb,hb37,hchunk]
  have hs39 : (s 39).val = dir.val := by
    change (BinaryOp.mod.eval (c 38) (c 2)).val = _
    rw [mod_val, hc, show (c 2).val = 2 by simp [c,b,a,I.two]]
    omega
  have hzero : (s 0).val = 0 := by simp [s,c,b,a,I.zero]
  have hone : (s 1).val = 1 := by simp [s,c,b,a,I.one]
  have htwo : (s 2).val = 2 := by simp [s,c,b,a,I.two]
  have hpos : (s 32).val = 1 := by simp [s,c,b,a,I.present]
  have hsite : (s 23).val = v.val := by simp [s,c,b,a,I.site]
  have hport : (s 25).val = k := by simp [s,c,b,a,hr]
  have hblock : (s 37).val = blockBits H w := by simp [s,c,b,a,I.block]
  have hs38 : (s 38).val = 2 * l.ordinal.val + dir.val := by simpa [s] using hc
  let prefixRun {out : Regs w 48} {cnt : ℕ}
      (h : Ticks pub state m (.ifEq 39 0 (copy 32 1) receiveSort) s cnt out) :
      Ticks pub state m sort rs (1+(1+(1+(1+cnt)))) out :=
    seqTicks (pubTicks pub state m 37 13 rs) <|
    seqTicks (opTicks pub state m .sub 38 25 36 a) <|
    seqTicks (opTicks pub state m .div 38 38 37 b) <|
    seqTicks (opTicks pub state m .mod 39 38 2 c) h
  by_cases hd : dir = 0
  · subst dir
    let out := Function.update s (32 : Fin 48) (s 1)
    have he : s 39 = s 0 := Fin.ext (hs39.trans hzero.symm)
    have run : Ticks pub state m (.ifEq 39 0 (copy 32 1) receiveSort) s 2 out :=
      .ifEqYes he (copyTicks pub state m 32 1 s)
    refine ⟨6,out,prefixRun run,by omega,?_⟩
    have h33 : (out 33).val = v.val := by simp [out,s,c,b,a,I.u]
    have h34 : (out 34).val = k := by simp [out,s,c,b,a,I.t,k]
    simp [result, show (out 32).val = 1 by simpa [out] using hone, h33,h34,k]
  · have hd1 : dir.val = 1 := by
      have hne : dir.val ≠ 0 := fun h ↦ hd (Fin.ext h)
      have := dir.isLt
      omega
    have he : s 39 ≠ s 0 := fun e ↦ by have := congrArg Fin.val e; omega
    have hlarge : d ≤ w := by
      by_contra hn
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show w ≤ d by omega)
      have hword := (rs 7).isLt
      rw [I.sites] at hword
      omega
    have hwidth : (s 37).val ≤ (s 25).val := by rw [hblock,hport,hk,hd1,Nat.one_mul]; omega
    obtain ⟨out,ho,hresult⟩ := receive_exec (pub := pub) (state := state) (m := m) l s hzero hone htwo
      (by rw [hs38,hd1]; omega) hpos hwidth hlarge (by rw [hsite]; exact v.isLt)
    have hrun : Ticks pub state m (.ifEq 39 0 (copy 32 1) receiveSort) s (3*l.phase+7+1) out :=
      .ifEqNo he ho
    refine ⟨_, out, prefixRun hrun, by have := l.phase_lt; omega, ?_⟩
    rw [hresult,hsite,hport,hblock,ite_eq_right hd,offset_sort,hk,hd1]
    simp [Layer.partner, Nat.add_assoc]
    omega

private abbrev route : Block := .ifLt 25 35 successorSend (.ifLt 25 36 successorReceive sort)

private theorem route_exec {d H : ℕ} (v : Fin (2 ^ d)) (k : Fin (width d H w)) (rs : Regs w 48)
    (I : Prepared (H := H) (v := v) (k := k) pub rs) :
    ∃ cost out, Ticks pub state m route rs cost out ∧ cost ≤ 3*d+14 ∧
      result out = (rawSource d H w v.val k.val).1 := by
  obtain ⟨p, rfl⟩ := (offset d H w).surjective k
  rw [rawSource_offset]
  rcases p with ⟨dir,j⟩ | ⟨l,dir,j⟩
  · fin_cases dir
    · have hj := j.isLt
      have hport : (rs 25).val = j.val := by simpa [offset_successor] using I.offset
      have hfirst : rs 25 < rs 35 := by change (rs 25).val < (rs 35).val; rw [hport,I.firstReg]; exact hj
      let a := Function.update rs (37 : Fin 48) (BinaryOp.sub.eval (rs 7) (rs 1))
      have hle : (rs 1).val ≤ (rs 7).val := by rw [I.one,I.sites]; exact Nat.two_pow_pos d
      have ha37 : (a 37).val = 2 ^ d - 1 := by
        change (BinaryOp.sub.eval (rs 7) (rs 1)).val = _
        rw [sub_val _ _ hle,I.sites,I.one]
      have ha23 : (a 23).val = v.val := by simpa [a] using I.site
      have ha33 : (a 33).val = v.val := by simpa [a] using I.u
      have ha34 : (a 34).val = j.val := by simpa [a,offset_successor] using I.t
      by_cases hv : v.val + 1 < 2 ^ d
      · let out := Function.update a (32 : Fin 48) (a 1)
        have ht : a 23 < a 37 := by change (a 23).val < (a 37).val; omega
        have hh : Ticks pub state m (.ifLt 23 37 (copy 32 1) (copy 32 0)) a 2 out :=
          .ifLtYes ht (copyTicks pub state m 32 1 a)
        refine ⟨4,out,Flow.Exec.ifLtYes hfirst (seqTicks (opTicks pub state m .sub 37 7 1 rs) hh),by omega,?_⟩
        have ho : (out 32).val = 1 := by simp [out,a,I.one]
        have ho33 : (out 33).val = v.val := by simpa [out] using ha33
        have ho34 : (out 34).val = j.val := by simpa [out] using ha34
        simp [result,ho,sourcePort,hv,ho33,ho34,offset_successor]
      · let out := Function.update a (32 : Fin 48) (a 0)
        have ht : ¬ a 23 < a 37 := by change ¬ (a 23).val < (a 37).val; omega
        have hh : Ticks pub state m (.ifLt 23 37 (copy 32 1) (copy 32 0)) a 2 out :=
          .ifLtNo ht (copyTicks pub state m 32 0 a)
        refine ⟨4,out,Flow.Exec.ifLtYes hfirst (seqTicks (opTicks pub state m .sub 37 7 1 rs) hh),by omega,?_⟩
        have ho : (out 32).val = 0 := by simp [out,a,I.zero]
        simp [result,ho,sourcePort,hv]
    · have hj := j.isLt
      have hport : (rs 25).val = 8*w + j.val := by simpa [offset_successor] using I.offset
      have hfirst : ¬ rs 25 < rs 35 := by change ¬ (rs 25).val < (rs 35).val; rw [I.firstReg]; omega
      have hbase : rs 25 < rs 36 := by change (rs 25).val < (rs 36).val; rw [I.baseReg]; omega
      by_cases hv : 0 < v.val
      · have ht : rs 23 ≠ rs 0 := fun h ↦ by have := congrArg Fin.val h; rw [I.site,I.zero] at this; omega
        let a := Function.update rs (33 : Fin 48) (BinaryOp.sub.eval (rs 23) (rs 1))
        let out := Function.update a (34 : Fin 48) (BinaryOp.sub.eval (a 25) (a 35))
        have run : Ticks pub state m successorReceive rs 3 out := Flow.Exec.ifEqNo ht
          (seqTicks (opTicks pub state m .sub 33 23 1 rs) (opTicks pub state m .sub 34 25 35 a))
        refine ⟨5,out,Flow.Exec.ifLtNo hfirst (Flow.Exec.ifLtYes hbase run),by omega,?_⟩
        have ho32 : (out 32).val = 1 := by simp [out,a,I.present]
        have ha33 : (a 33).val = v.val - 1 := by
          change (BinaryOp.sub.eval (rs 23) (rs 1)).val = _
          rw [sub_val _ _ (by rw [I.one,I.site]; omega),I.site,I.one]
        have ha25 : (a 25).val = 8*w + j.val := by simpa [a] using hport
        have ha35 : (a 35).val = 8*w := by simpa [a] using I.firstReg
        have ho34 : (out 34).val = j.val := by
          change (BinaryOp.sub.eval (a 25) (a 35)).val = _
          rw [sub_val _ _ (by omega),ha25,ha35,Nat.add_sub_cancel_left]
        have ho33 : (out 33).val = v.val-1 := by simpa [out] using ha33
        simp [result,ho32,ho33,ho34,sourcePort,hv,offset_successor]
      · have ht : rs 23 = rs 0 := Fin.ext (by rw [I.site,I.zero]; omega)
        let out := Function.update rs (32 : Fin 48) (rs 0)
        have run : Ticks pub state m successorReceive rs 2 out := .ifEqYes ht (copyTicks pub state m 32 0 rs)
        refine ⟨4,out,Flow.Exec.ifLtNo hfirst (Flow.Exec.ifLtYes hbase run),by omega,?_⟩
        have ho32 : (out 32).val = 0 := by simp [out,I.zero]
        simp [result,ho32,sourcePort,hv]
  · have hk := offset_sort l dir j (d := d)
    have hfirst : ¬ rs 25 < rs 35 := by change ¬ (rs 25).val < (rs 35).val; rw [I.offset,I.firstReg]; omega
    have hbase : ¬ rs 25 < rs 36 := by change ¬ (rs 25).val < (rs 36).val; rw [I.offset,I.baseReg]; omega
    obtain ⟨k,out,run,hcost,ho⟩ := sort_exec (state := state) (m := m) v l dir j rs I
    refine ⟨k+1+1,out,Flow.Exec.ifLtNo hfirst (Flow.Exec.ifLtNo hbase run),by omega,?_⟩
    simpa [sourcePort] using ho

/-- The actual fixed register program reaches its normal exit with the
calculated raw address. Its event trace contains private ticks only. -/
theorem program_exec {d H : ℕ} (v : Fin (2 ^ d)) (k : Fin (width d H w)) (rs : Regs w 48)
    (I : Input d H v k pub rs) :
    ∃ cost out, Ticks pub state m program rs cost out ∧ cost ≤ 3*d+19 ∧
      result out = (rawSource d H w v.val k.val).1 := by
  let a := Function.update rs (32 : Fin 48) (rs 1)
  let b := Function.update a (33 : Fin 48) (a 23)
  let c := Function.update b (34 : Fin 48) (b 25)
  let e := Function.update c (35 : Fin 48) (pub 14)
  let s := Function.update e (36 : Fin 48) (pub 15)
  have hi : Prepared (H := H) (v := v) (k := k) pub s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases I with ⟨h0,h1,h2,h7,h23,h25,h13,h14,h15⟩
      constructor <;> simp_all [s,e,c,b,a]
    all_goals simp [s,e,c,b,a,I.one,I.site,I.offset,I.first,I.base]
  obtain ⟨cnt,out,hr,hc,ho⟩ := route_exec (state := state) (m := m) v k s hi
  refine ⟨1+(1+(1+(1+(1+cnt)))),out,?_,by omega,ho⟩
  exact seqTicks (copyTicks pub state m 32 1 rs) <| seqTicks (copyTicks pub state m 33 23 a) <|
    seqTicks (copyTicks pub state m 34 25 b) <| seqTicks (pubTicks pub state m 35 14 c) <|
    seqTicks (pubTicks pub state m 36 15 e) hr

private def untouched (i : Fin 48) : Block → Prop
  | .line op => op.destination ≠ some i
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b | .branch a b => untouched i a ∧ untouched i b
  | .whileLt _ _ body => untouched i body

private theorem exec_untouched {a : Block} {rs out : Regs w 48} {m' es}
    (h : Flow.Exec pub state a rs m es out m') (i : Fin 48) (hi : untouched i a) : out i = rs i := by
  induction h with
  | @line op regs mem e next final he =>
    apply trace_preserves (pub := pub) (state := state) (ops := [op]) (i := i) (mem := mem) (m := final) (es := [e])
    · simpa [untouched] using hi
    · simp [trace, he]
  | seq _ _ ih₁ ih₂ => exact (ih₂ hi.2).trans (ih₁ hi.1)
  | ifEqYes _ _ ih | ifLtYes _ _ ih | branchYes _ ih => exact ih hi.1
  | ifEqNo _ _ ih | ifLtNo _ _ ih | branchNo _ ih => exact ih hi.2
  | whileDone _ => rfl
  | whileStep _ _ _ ih₁ ih₂ => exact (ih₂ hi).trans (ih₁ hi)

/-- All registers below the return registers retain their entry values. -/
theorem program_preserves {rs out : Regs w 48} {cost : ℕ}
    (h : Ticks pub state m program rs cost out) (i : Fin 48) (hi : i.val < 32) : out i = rs i := by
  apply exec_untouched h i
  simp only [untouched, program, successorSend, successorReceive, sort, receiveSort, scan, scanStep,
    copy, binary, publicWord, Op.destination, Option.some.injEq, ne_eq, Fin.ext_iff]
  norm_num
  omega

end PrimedInputRAM.PortCode

end VPVNP
end Computability
end OAI
