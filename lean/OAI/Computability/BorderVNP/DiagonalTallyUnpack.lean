import OAI.Computability.BorderVNP.DiagonalTallyRAMStage

/-! # Bit serialization of the global tally words

The Fourier query circuit consumes one word per Boolean input. A fixed loop takes
the quotient and remainder of the output offset by the bit width, reads the named
counter, then shifts and masks it. The least significant bit occupies offset zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyUnpack

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM

/-- Select the source word and digit corresponding to the current output offset. -/
def selectBit : Code := .block [.binary .div 54 52 49, .binary .mod 55 52 49,
  .binary .add 54 48 54, .load 56 54, .binary .add 57 50 52]

/-- Read the selected bit using one shift and one mask, then write it. -/
def storeBit : Code := .block [.binary .shiftRight 56 56 55, .binary .bitAnd 56 56 63,
  .store 57 56, .binary .add 52 52 63]

/-- One iteration has a fixed instruction count. -/
def body : Code := .seq selectBit storeBit

/-- Flatten the coordinate-major, little-endian bit array. Registers 48,49,50,51,52
hold the source base, bit width, destination base, total bit count, and current offset. -/
def unpack : Code := .whileLt 52 51 body

variable {w : ℕ}

/-- The chosen word, its bit width, and both physical memory intervals. -/
structure Frame where
  /-- Word address of the first input tally. -/
  src : ℕ
  /-- Bit width to be supplied per coordinate. -/
  width : ℕ
  /-- Word address of the first Boolean output bit. -/
  dst : ℕ
  /-- Number of coordinates times the bit width. -/
  total : ℕ

/-- Registers fixed throughout the loop. -/
def Frame.loaded (f : Frame) (s : Bank w) : Prop :=
  (s 48).val = f.src ∧ (s 49).val = f.width ∧ (s 50).val = f.dst ∧
    (s 51).val = f.total ∧ (s 63).val = 1

/-- In-bounds disjoint layout, including the final sentinel. -/
def Frame.fits (f : Frame) (w : ℕ) : Prop :=
  0 < f.width ∧ f.width ≤ w ∧ f.src+f.total/f.width+1 < 2^w ∧ f.dst+f.total < 2^w ∧
    (f.src+f.total/f.width+1 ≤ f.dst ∨ f.dst+f.total ≤ f.src)

/-- Bit at a flattened coordinate of the output array, expressed in the original memory. -/
def Frame.digit (f : Frame) (m : Memory w) (i : ℕ) : Bool :=
  (m (f.src+i/f.width)).val.testBit (i%f.width)

private theorem storedBit_value (a b one : Word w) (hb : b.val < w) (ho : one.val = 1) :
    BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval a b) one =
      word w ((a.val.testBit b.val).toNat) := by
  have hd : (a.val >>> b.val) < 2^w :=
    (by rw [Nat.shiftRight_eq_div_pow]; exact (Nat.div_le_self ..).trans_lt a.isLt)
  rw [Nat.shiftRight_eq_div_pow] at hd
  simp only [BinaryOp.eval, hb, ite_true, Fin.val_ofNat, ho, Nat.and_one_is_mod,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hd]
  by_cases h : a.val / 2^b.val % 2 = 1
  · simp [h,word]
  · have he : a.val / 2^b.val % 2 = 0 := by omega
    simp [he,word]

private theorem body_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (f : Frame) (hl : f.loaded s) (hf : f.fits w) {i : ℕ} (hi : i < f.total) (hs : (s 52).val = i) :
    ∃ es t, Runs pub mac body s m es t
        (Function.update m (f.dst+i) (word w (f.digit m i).toNat)) ∧ traceCost es ≤ 9 ∧
      f.loaded t ∧ (t 52).val = i+1 := by
  obtain ⟨s48,s49,s50,s51,s63⟩ := hl
  obtain ⟨hw,hw',hsrc,hdst,_⟩ := hf
  have hdiv : i/f.width ≤ f.total/f.width := Nat.div_le_div_right hi.le
  have hsrc' : f.src+i/f.width < 2^w := by omega
  have hdst' : f.dst+i < 2^w := by omega
  have his : i+1 < 2^w := by omega
  have ha : selectBit.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [selectBit,Code.block,Code.safeReadOnly,Code.evalNat,readings,addressOpFits,addressOp,
      Function.update,s48,s49,s50,hs,hw,hsrc',hdst']
  obtain ⟨es,t,hr,hc,ht⟩ := Code.runReadOnly selectBit pub mac m s ha
  have H : (t 55).val = i%f.width ∧ t 56 = m (f.src+i/f.width) ∧ (t 57).val = f.dst+i ∧
      f.loaded t ∧ (t 52).val = i := by
    have hh : readings t 55 = i%f.width ∧ readings t 56 = (m (f.src+i/f.width)).val ∧
        readings t 57 = f.dst+i ∧ readings t 48 = f.src ∧ readings t 49 = f.width ∧
        readings t 50 = f.dst ∧ readings t 51 = f.total ∧ readings t 63 = 1 ∧ readings t 52 = i := by
      rw [ht]
      simp [selectBit,Code.block,Code.evalNat,readings,addressOp,Function.update,s48,s49,s50,s51,s63,hs]
    exact ⟨hh.1, Fin.ext hh.2.1, hh.2.2.1, ⟨hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2.1,
      hh.2.2.2.2.2.2.1,hh.2.2.2.2.2.2.2.1⟩,hh.2.2.2.2.2.2.2.2⟩
  obtain ⟨t55,t56,t57,tFrame,t52⟩ := H
  obtain ⟨t48,t49,t50,t51,t63⟩ := tFrame
  have he : BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval (t 56) (t 55)) (t 63) =
      word w (f.digit m i).toNat := by
    rw [storedBit_value _ _ _ (by rw [t55]; exact (Nat.mod_lt _ hw).trans_le hw') t63, t56,t55]
    rfl
  let e := effect false t m storeBit
  have run := effect_runs pub mac false t m storeBit (by decide)
  have info : e.mem = Function.update m (f.dst+i) (word w (f.digit m i).toNat) ∧
      f.loaded e.bank ∧ (e.bank 52).val = i+1 ∧ TraceOK e.trace [] 4 := by
    have hadd : (t 52+t 63).val = i+1 := by rw [Fin.val_add,t52,t63,Nat.mod_eq_of_lt his]
    simp [e,storeBit,Code.block,effect,Frame.loaded,Function.update,t48,t49,t50,t51,t63,t57,
      TraceOK,tick,BinaryOp.eval] at hadd ⊢
    all_goals first | exact hadd | simp_all [BinaryOp.eval,Frame.digit]
  change Runs pub mac storeBit t m e.trace e.bank e.mem at run
  rw [info.1] at run
  refine ⟨_,_,.seq hr run, ?_, info.2.1, info.2.2.1⟩
  rw [show traceCost (es++e.trace) = traceCost es+traceCost e.trace from VPVNP.RAMBuckets.cost_append ..,
    DiagonalTallyRAM.ordinary_cost (by decide) run,info.2.2.2.1]
  have hslt : selectBit.slots = 5 := by decide
  omega

/-- Memory after writing a consecutive slice of the flattened Boolean output. -/
def writeSlice (dst : ℕ) (g : ℕ → Bool) (m : Memory w) (i : ℕ) : ℕ → Memory w
  | 0 => m
  | n+1 => writeSlice dst g (Function.update m (dst+i) (word w (g i).toNat)) (i+1) n

/-- Decode any suffix of the coordinate-major bit array. It costs at most ten
native ticks per bit and one final test, with all previous words recorded. -/
theorem unpack_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (f : Frame)
    (s : Bank w) (m : Memory w) (i n : ℕ) (hf : f.fits w) (hl : f.loaded s)
    (hi : (s 52).val = i) (hlen : i+n = f.total) :
    ∃ es t, Runs pub mac unpack s m es t (writeSlice f.dst (f.digit m) m i n) ∧
      traceCost es ≤ 10*n+1 ∧ f.loaded t ∧ (t 52).val = f.total := by
  induction n generalizing i s m with
  | zero =>
    have ht := hl.2.2.2.1
    have hid : i = f.total := by omega
    refine ⟨_,_, .whileDone (by change ¬(s 52).val < (s 51).val; omega), ?_, hl, hi.trans hid⟩
    simp [traceCost,VPVNP.RAMBuckets.cost,tick,TeamTranscript.Action.extra]
  | succ n ih =>
    have hj : i < f.total := by omega
    have hg : s 52 < s 51 := by
      change (s 52).val < (s 51).val
      rw [hi,hl.2.2.2.1]
      exact hj
    obtain ⟨es,t,step,hc,ht,hti⟩ := body_runs pub mac s m f hl hf hj hi
    let m' := Function.update m (f.dst+i) (word w (f.digit m i).toNat)
    obtain ⟨fs,z,loop,hc',hz,hzi⟩ := ih t m' (i+1) ht hti (by omega)
    have he (j : ℕ) (h : j < f.total) : f.digit m' j = f.digit m j := by
      have hdiv : j/f.width ≤ f.total/f.width := Nat.div_le_div_right h.le
      have hsep := hf.2.2.2.2
      have hne : f.src+j/f.width ≠ f.dst+i := by
        rcases hsep with h₁ | h₂
        · exact ((Nat.lt_succ_of_le (Nat.add_le_add_left hdiv _)).trans_le
            (h₁.trans (Nat.le_add_right _ _))).ne
        · exact ((Nat.add_lt_add_left hj _).trans_le (h₂.trans (Nat.le_add_right _ _))).ne'
      simp [Frame.digit,m',hne]
    have congrSlice (start len : ℕ) (hbound : start+len ≤ f.total) (mem : Memory w) :
        writeSlice f.dst (f.digit m') mem start len = writeSlice f.dst (f.digit m) mem start len := by
      induction len generalizing start mem with
      | zero => rfl
      | succ len ih' => rw [writeSlice,writeSlice,he start (by omega),ih' (start+1) (by omega)]
    rw [congrSlice (i+1) n (by omega) m'] at loop
    refine ⟨_,_, .whileStep hg step loop, ?_, hz, hzi⟩
    change 1 + traceCost (es++fs) ≤ _
    rw [show traceCost (es++fs) = traceCost es+traceCost fs from VPVNP.RAMBuckets.cost_append ..]
    omega

/-- The native output at each named coordinate and bit has the required Boolean value. -/
theorem writeSlice_at (dst : ℕ) (g : ℕ → Bool) (m : Memory w) (i n j : ℕ)
    (hi : i ≤ j) (hj : j < i+n) : writeSlice dst g m i n (dst+j) = word w (g j).toNat := by
  have outside (mem : Memory w) (a len b : ℕ) (hb : b < a ∨ a+len ≤ b) :
      writeSlice dst g mem a len (dst+b) = mem (dst+b) := by
    induction len generalizing a mem with
    | zero => rfl
    | succ len ih => rw [writeSlice,ih _ _ (by omega),Function.update_of_ne (by omega)]
  induction n generalizing m i with
  | zero => omega
  | succ n ih =>
    rw [writeSlice]
    rcases Nat.eq_or_lt_of_le hi with rfl | h
    · rw [outside _ _ _ _ (.inl (by omega)), Function.update_self]
    · exact ih _ _ (by omega) (by omega)

/-- Output offset `c*width+j` reads bit `j` of counter `c`, in the original memory. -/
theorem digit_at (f : Frame) (m : Memory w) {c j : ℕ} (hj : j < f.width) :
    f.digit m (c*f.width+j) = (m (f.src+c)).val.testBit j := by
  have hp : 0 < f.width := by omega
  rw [Frame.digit, Nat.mul_comm c f.width, Nat.mul_add_div hp, Nat.div_eq_of_lt hj, Nat.add_zero,
    Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hj]

end DiagonalTallyUnpack

end BorderVNP
end Computability
end OAI
