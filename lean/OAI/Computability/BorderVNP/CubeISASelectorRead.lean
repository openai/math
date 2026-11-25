import OAI.Computability.BorderVNP.CubeISALengthScan
import OAI.Computability.BorderVNP.RoutingISARegisterFrame
import OAI.Computability.BorderVNP.DiagonalTallyPacketRecipe
import OAI.Computability.VPVNP.LiveHeaderBits

/-! # Reading the little-endian selector of one physical cube packet

Register 24 contains the packet prefix base, 41 the number of bits, and 42 the
exclusive number of valid selector ranks. The decoded rank returns in 43.
The loop visits the input positions backwards, accumulating high bits first.
Any nonbinary memory word or spare rank takes an actual rejection instruction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.SelectorRead

open RoutingISA VPVNP.BurstRAM VPVNP.RAMSerialization Finset

/-- Interpret a possibly malformed word array by testing each addressed word for one.
The native test checks binarity separately, so this defines a value on every input. -/
def decoded (mem : ℕ → ℕ) (base width : ℕ) : Word width :=
  (wordBits width).symm (fun j => decide (mem (base+j.val) = 1))

/-- All input words are bits and the ordinal they encode lies in the selector range. -/
def Valid (mem : ℕ → ℕ) (base width count : ℕ) : Prop :=
  (∀ j < width, mem (base+j) < 2) ∧ (decoded mem base width).val < count

private theorem digit (mem : ℕ → ℕ) (base width k : ℕ) (hk : k < width) :
    (if mem (base+k) = 1 then 1 else 0) = (decoded mem base width).val / 2^k % 2 := by
  let a := decoded mem base width
  have h : a.val.testBit k = decide (mem (base+k)=1) :=
    (VPVNP.LiveHeader.testBit_wordBits a ⟨k,hk⟩).trans (congrFun ((wordBits width).apply_symm_apply _) ⟨k,hk⟩)
  rw [Nat.testBit_eq_decide_div_mod_eq] at h
  have e : a.val/2^k%2 = 1 ↔ mem (base+k)=1 := by simpa only [decide_eq_decide] using h
  change _ = a.val/2^k%2
  split <;> omega

/-- The two increments are the cursor and the two-valued alphabet limit. -/
def init : RoutingISA.Code := .block [.constant 50 0,.constant 43 0,.constant 51 1,.constant 52 2]

/-- Reject a nonbinary word. A one increments the doubled accumulator. -/
def appendBit : RoutingISA.Code := .ifLt 54 52
  (.ifEq 54 51 (.binary .add 43 43 51) .nop) .reject

/-- Read the next reverse-indexed input word and double the accumulated prefix. -/
def fetchBit : RoutingISA.Code := .block [.binary .sub 53 41 51,.binary .sub 53 53 50,
  .binary .add 53 24 53,.load 54 53,.binary .add 43 43 43]

/-- Read one addressed source word, starting at the most significant position. -/
def step : RoutingISA.Code := .seq fetchBit (.seq appendBit (.binary .add 50 50 51))

/-- The final unsigned comparison rejects unused ranks. -/
def reader : RoutingISA.Code := .seq init (.seq (.whileLt 50 41 step) (requireLt 43 42))

private theorem append_eval (p : Arg → ℕ) (mem : ℕ → ℕ) (reg : Reg → ℕ)
    (one : reg 51 = 1) (two : reg 52 = 2) :
    appendBit.evalNat p mem reg =
      if reg 54 = 1 then Function.update reg 43 (reg 43+1) else reg := by
  by_cases h : reg 54 = 1 <;> simp [appendBit,Code.evalNat,addressOp,one,two,h]

private theorem append_safe {w : ℕ} (p : Arg → ℕ) (mem : ℕ → ℕ) (reg : Reg → ℕ)
    (one : reg 51 = 1) (two : reg 52 = 2) (fits : reg 54 = 1 → reg 43+1 < 2^w) :
    appendBit.safeReadOnly w p mem reg ↔ reg 54 < 2 := by
  by_cases h : reg 54 = 1
  · simp [appendBit,Code.safeReadOnly,addressOpFits,one,two,h,fits h]
  · simp [appendBit,Code.safeReadOnly,one,two,h]

private theorem append_fit {w : ℕ} (p : Arg → ℕ) (mem : ℕ → ℕ) (reg : Reg → ℕ)
    (one : reg 51 = 1) (two : reg 52 = 2) (fits : reg 54 = 1 → reg 43+1 < 2^w) :
    appendBit.relaxReject.safeReadOnly w p mem reg := by
  by_cases h : reg 54 = 1
  · simp [appendBit,Code.relaxReject,Code.safeReadOnly,addressOpFits,one,two,h,fits h]
  · simp [appendBit,Code.relaxReject,Code.safeReadOnly,one,two,h]

private structure At (mem : ℕ → ℕ) (base width count i : ℕ) (z : NatState) : Prop where
  memory : z.mem = mem
  packet : z.reg 24 = base
  bits : z.reg 41 = width
  choices : z.reg 42 = count
  ordinal : z.reg 43 = (decoded mem base width).val / 2^(width-i)
  cursor : z.reg 50 = i
  one : z.reg 51 = 1
  two : z.reg 52 = 2

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem step_test (mem : ℕ → ℕ) (base width count i : ℕ) (s : Bank w) (m : Memory w)
    (room : base+width ≤ 2^w) (word : width ≤ w) (hi : i < width)
    (hs : At mem base width count i (.ofWords s m)) :
    TestRun pub mac step s m step.slots (mem (base+(width-1-i)) < 2) (At mem base width count (i+1)) := by
  let k := width-1-i
  let q := (decoded mem base width).val
  let a := q/2^(k+1)
  let x := mem (base+k)
  have h24 : readings s 24 = base := hs.packet
  have h41 : readings s 41 = width := hs.bits
  have h42 : readings s 42 = count := hs.choices
  have prev : k+1 = width-i := by dsimp [k]; omega
  have h43 : readings s 43 = a := by change readings s 43 = q/2^(k+1); rw [prev]; exact hs.ordinal
  have h50 : readings s 50 = i := hs.cursor
  have h51 : readings s 51 = 1 := hs.one
  have h52 : readings s 52 = 2 := hs.two
  have hm : readings m = mem := hs.memory
  have hk : k < width := by dsimp [k]; omega
  have pfit : base+k < 2^w := by omega
  have ifit : i+1 < 2^w := lt_of_le_of_lt hi (h41 ▸ (s 41).isLt)
  have qfit : q < 2^w := (decoded mem base width).isLt.trans_le (Nat.pow_le_pow_right (by decide) word)
  have readBit := digit mem base width k hk
  have next : a+a+(if x = 1 then 1 else 0) = q/2^k := by
    rw [show (if x = 1 then 1 else 0) = q/2^k%2 from readBit]
    dsimp [a]
    rw [pow_succ,← Nat.div_div_eq_div_mul]
    omega
  have nfit : q/2^k < 2^w := (Nat.div_le_self ..).trans_lt qfit
  have dbl : a+a < 2^w := by omega
  have plus : x = 1 → a+a+1 < 2^w := by intro hx; rw [ite_eq_left hx] at next; omega
  let t := fetchBit.evalNat (readings pub) (readings m) (readings s)
  have ht : t = Function.update (Function.update (Function.update (readings s) 53 (base+k)) 54 x) 43 (a+a) := by
    simp (config := {decide := true}) [t,fetchBit,Code.block,Code.evalNat,addressOp,h24,h41,h50,h51,h43,hm,k,x]
  have t54 : t 54 = x := by simp (config := {decide := true}) [ht]
  have t43 : t 43 = a+a := by simp [ht]
  have t51 : t 51 = 1 := by simp (config := {decide := true}) [ht,h51]
  have t52 : t 52 = 2 := by simp (config := {decide := true}) [ht,h52]
  have ok := append_safe (w := w) (readings pub) (readings m) t t51 t52 (by rw [t54,t43]; exact plus)
  have fit := append_fit (w := w) (readings pub) (readings m) t t51 t52 (by rw [t54,t43]; exact plus)
  have vals := append_eval (readings pub) (readings m) t t51 t52
  rw [t54,t43] at vals
  rw [t54] at ok
  have small : 1 ≤ width := by omega
  have sub : i ≤ width-1 := by omega
  change base+(width-1-i) < 2^w at pfit
  have same : width-(i+1) = k := by dsimp [k]; omega
  have fetch : fetchBit.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [fetchBit,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,
      h24,h41,h50,h51,h43,pfit,small,sub,dbl]
  let z := appendBit.evalNat (readings pub) (readings m) t
  have zz : z = Function.update t 43 (q/2^k) := by
    dsimp only [z]
    rw [vals,← next]
    by_cases hx : x = 1
    · simp [hx]
    · simp [hx,← t43]
  have inc : addressOpFits w .add (z 50) (z 51) := by
    simpa (config := {decide := true}) [zz,ht,addressOpFits,h50,h51] using ifit
  apply CubeLengths.readTest _ s m _ _ (by decide)
  · change fetchBit.safeReadOnly w _ _ _ ∧ appendBit.relaxReject.safeReadOnly w _ _ t ∧
      addressOpFits w .add ((appendBit.relaxReject.evalNat (readings pub) (readings m) t) 50)
        ((appendBit.relaxReject.evalNat (readings pub) (readings m) t) 51)
    exact ⟨fetch,fit,by simpa only [Code.evalNat_relaxReject] using inc⟩
  · change (fetchBit.safeReadOnly w _ _ _ ∧ appendBit.safeReadOnly w _ _ t ∧
      addressOpFits w .add (z 50) (z 51)) ↔ x < 2
    simp only [fetch,ok,inc,true_and,and_true]
  · let out := Function.update z (50 : Reg) (z 50+z 51)
    change At mem base width count (i+1) ⟨out,readings m⟩
    refine ⟨hm,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      simp (config := {decide := true}) [out,zz,ht,h24,h41,h42,h50,h51,h52,same,q]

/-- Registers changed by the selector reader. All other words survive. -/
def Scratch (j : Reg) : Prop := j = 43 ∨ j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54

private theorem keeps (j : Reg) (h : ¬ Scratch j) : reader.keeps j = true := by
  simp only [Scratch,not_or] at h
  obtain ⟨h43,h50,h51,h52,h53,h54⟩ := h
  simp [reader,step,fetchBit,appendBit,init,requireLt,Code.block,Code.keeps,h43,h50,h51,h52,h53,h54]

/-- The actual fixed selector reader returns exactly on valid binary, in-range
inputs and outputs the precise rank. The two static words are the selector bit
width and count. Registers outside the declared scratch bank and all memory survive. -/
theorem reader_run (s : Bank w) (m : Memory w) (base width count : ℕ)
    (hb : readings s 24 = base) (hw : readings s 41 = width) (hc : readings s 42 = count)
    (two : 2 < 2^w) (word : width ≤ w) (room : base+width ≤ 2^w) :
    TestRun pub mac reader s m (init.slots+width*(step.slots+1)+1+(requireLt 43 42).slots)
      (Valid (readings m) base width count) (fun z => z.mem = readings m ∧
        z.reg 43 = (decoded (readings m) base width).val ∧ ∀ j, ¬ Scratch j → z.reg j = readings s j) := by
  let mem := readings m
  let I := At mem base width count
  let good i := mem (base+(width-1-i)) < 2
  have one : 1 < 2^w := by omega
  have zero : (decoded mem base width).val/2^width = 0 := Nat.div_eq_of_lt (decoded mem base width).isLt
  have start : TestRun pub mac init s m init.slots True (I 0) := by
    apply CubeLengths.readTest _ s m _ _ (by decide)
    · change init.safeReadOnly _ _ _ _
      simp [init,Code.block,Code.safeReadOnly,one,two]
    · simp [init,Code.block,Code.safeReadOnly,one,two]
    · refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_⟩ <;>
        simp (config := {decide := true}) [init,Code.block,Code.evalNat,hb,hw,hc,zero]
  have loop (u : Bank w) (mu : Memory w) (hs : I 0 (.ofWords u mu)) :
      TestRun pub mac (.whileLt 50 41 step) u mu (width*(step.slots+1)+1)
        (∀ j < width, mem (base+j) < 2) (I width) := by
    apply (test_counted_loop 50 41 step width (fun _ => step.slots) good I
      (fun _ _ hz => ⟨hz.cursor,hz.bits⟩) (fun i hi t mt hz => step_test mem base width count i t mt
        room word hi hz) 0 (Nat.zero_le _) u mu hs).mono (by simp) ?_ (fun _ hz => hz)
    constructor
    · intro h j hj
      have rev : width-1-(width-1-j) = j := by omega
      simpa only [good,rev] using h (width-1-j) (Nat.zero_le _) (by omega)
    · intro h j _ hj
      exact h (width-1-j) (by omega)
  have finish (u : Bank w) (mu : Memory w) (hs : I width (.ofWords u mu)) :
      TestRun pub mac (requireLt 43 42) u mu (requireLt 43 42).slots
        ((decoded mem base width).val < count) (I width) := by
    have h43 : readings u 43 = (decoded mem base width).val := by simpa [NatState.ofWords] using hs.ordinal
    have h42 : readings u 42 = count := hs.choices
    apply CubeLengths.readTest _ u mu _ _ (by decide)
    · simp [requireLt,Code.relaxReject,Code.safeReadOnly]
    · simp [requireLt,Code.safeReadOnly,h42,h43]
    · simpa [NatState.ofWords,requireLt,Code.evalNat] using hs
  have all := (start.seq fun u mu hz => (loop u mu hz).seq finish).mono
    (cost' := init.slots+width*(step.slots+1)+1+(requireLt 43 42).slots)
    (ok' := Valid mem base width count) (Q := I width) (by omega) (by simp [Valid]) (fun _ hp => hp)
  have post {es t mt} (r : Runs pub mac reader s m es t mt) (h : I width (.ofWords t mt)) :
      readings mt = mem ∧ readings t 43 = (decoded mem base width).val ∧
        ∀ j, ¬ Scratch j → readings t j = readings s j :=
    ⟨h.memory,by simpa [NatState.ofWords] using h.ordinal,fun j hj => congrArg Fin.val (r.keepsReg (keeps j hj))⟩
  constructor
  · intro valid
    obtain ⟨es,t,mt,r,cap,h⟩ := all.complete valid
    exact ⟨es,t,mt,r,cap,post r h⟩
  · intro es t mt r
    obtain ⟨valid,h⟩ := all.sound r
    exact ⟨valid,post r h⟩

open Tally

variable {n K h : ℕ}

/-- Concrete physical bits of an actual selector in its fixed-width prefix. -/
def Stored (mem : ℕ → ℕ) (base : ℕ) (u : Selector n K h) : Prop :=
  ∀ j : Fin (selectorWidth n K h), mem (base+j.val) =
    (wordBits _ ⟨(selectorOrder n K h u).val,
      (selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩ j).toNat

/-- The RAM prefix decodes to the selector's actual mixed-radix rank. -/
theorem Stored.rank {mem : ℕ → ℕ} {base : ℕ} {u : Selector n K h} (stored : Stored mem base u) :
    (decoded mem base (selectorWidth n K h)).val = (selectorOrder n K h u).val := by
  let x : Word (selectorWidth n K h) := ⟨(selectorOrder n K h u).val,
    (selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩
  have e : decoded mem base (selectorWidth n K h) = x := by
    apply (VPVNP.RAMSerialization.wordBits _).injective
    rw [decoded,Equiv.apply_symm_apply]
    funext j
    rw [stored j]
    change decide ((wordBits _ x j).toNat=1) = wordBits _ x j
    cases wordBits _ x j <;> decide
  exact congrArg Fin.val e

/-- The accepted raw prefixes are exactly the unique encodings of valid physical
selectors, including an empty range, a zero-bit field, and unused binary codes. -/
theorem valid_iff_existsUnique (mem : ℕ → ℕ) (base : ℕ) :
    Valid mem base (selectorWidth n K h) (Fintype.card (Selector n K h)) ↔
      ∃! u : Selector n K h, Stored mem base u := by
  constructor
  · rintro ⟨bits,rank⟩
    let v := decoded mem base (selectorWidth n K h)
    let u := (selectorOrder n K h).symm ⟨v.val,rank⟩
    have he : (selectorOrder n K h u).val = v.val := by simp [u]
    refine ⟨u,fun j => ?_,fun t ht => (selectorOrder n K h).injective (Fin.ext (ht.rank.symm.trans he.symm))⟩
    have wordEq : (⟨(selectorOrder n K h u).val,he ▸ v.isLt⟩ : Word (selectorWidth n K h)) = v := Fin.ext he
    change mem (base+j.val) = (VPVNP.RAMSerialization.wordBits (selectorWidth n K h)
      ⟨(selectorOrder n K h u).val,he ▸ v.isLt⟩ j).toNat
    rw [wordEq]
    have hb := bits j.val j.isLt
    have e : wordBits _ v j = decide (mem (base+j.val)=1) := congrFun ((VPVNP.RAMSerialization.wordBits _).apply_symm_apply _) j
    rw [e]
    by_cases one : mem (base+j.val)=1 <;> simp [one]
    omega
  · rintro ⟨u,stored,_⟩
    refine ⟨fun j hj => ?_,stored.rank ▸ (selectorOrder n K h u).isLt⟩
    rw [stored ⟨j,hj⟩]
    exact Nat.lt_succ_of_le (Bool.toNat_le _)

/-- On a physical selector bank, the checked native reader returns its true
ordinal to the packet decoder while preserving its caller's data. -/
theorem physical_run (s : Bank w) (m : Memory w) (base : ℕ) (u : Selector n K h)
    (stored : Stored (readings m) base u)
    (hb : readings s 24 = base) (hw : readings s 41 = selectorWidth n K h)
    (hc : readings s 42 = Fintype.card (Selector n K h)) (two : 2 < 2^w)
    (room : base+selectorWidth n K h ≤ 2^w) :
    BoundedRun pub mac reader s m (init.slots+selectorWidth n K h*(step.slots+1)+1+(requireLt 43 42).slots)
      (fun z => z.mem = readings m ∧ z.reg 43 = (selectorOrder n K h u).val ∧
        ∀ j, ¬ Scratch j → z.reg j = readings s j) := by
  have word : selectorWidth n K h ≤ w := Nat.clog_le_of_le_pow (hc ▸ (s 42).isLt.le)
  have run := reader_run (pub := pub) (mac := mac) s m base _ _ hb hw hc two word room
  have valid : Valid (readings m) base (selectorWidth n K h) (Fintype.card (Selector n K h)) := by
    refine ⟨fun j hj => ?_,stored.rank ▸ (selectorOrder n K h u).isLt⟩
    rw [stored ⟨j,hj⟩]
    exact Nat.lt_succ_of_le (Bool.toNat_le _)
  exact (run.complete valid).mono le_rfl (fun _ hz => ⟨hz.1,hz.2.1.trans stored.rank,hz.2.2⟩)

end Cube.SelectorRead

end BorderVNP
end Computability
end OAI
