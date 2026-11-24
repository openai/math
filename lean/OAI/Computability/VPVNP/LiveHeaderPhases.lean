import OAI.Computability.VPVNP.LiveHeaderWidthCode
import OAI.Computability.VPVNP.LiveHeaderScan

/-!
# Live group flags computed from the scanned header

The live program tests whether it is at the first group, at the midpoint,
in the first half, or at the last group. Each test uses the scanned high
bit position and population count. The tests also apply when the first
group is the midpoint.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderWidths

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM

/-- The first-group, midpoint, first-half, and last-group predicates computed from the
one-based index. -/
inductive Flag where | first | middle | firstHalf | last

/-- Evaluate a phase flag against a one-based group index and the chain's height. -/
def Flag.holds (h i : ℕ) : Flag → Prop
  | .first => i = 1
  | .middle => i = 2^h
  | .firstHalf => i ≤ 2^h
  | .last => i = 2^(h+1)

instance (h i : ℕ) (f : Flag) : Decidable (f.holds h i) := by cases f <;> unfold Flag.holds <;> infer_instance


/-- The complete scanned prefix is the finite set of binary positions. -/
private theorem allOnes {i len : ℕ} (hlt : i < 2^len) :
    LiveHeader.prefixOnes i len = i.bitIndices.toFinset := by
  ext j
  simp only [LiveHeader.prefixOnes, Finset.mem_filter, Finset.mem_range, List.mem_toFinset,
    Nat.mem_bitIndices, and_iff_right_iff_imp]
  intro ht
  by_contra! hh
  have hz := Nat.testBit_lt_two_pow (hlt.trans_le (Nat.pow_le_pow_right (by decide) hh))
  simp_all

/-- In the nondegenerate case, the first tail index has precisely bits
zero and `h` set. The low bit distinguishes it from other tail indices
of population two. -/
theorem firstTail_iff {h i : ℕ} (hh : 0 < h) (hi : 0 < i) (hend : i ≤ 2^(h+1)) :
    Nat.log 2 i = h ∧ (LiveHeader.prefixOnes i (h+2)).card = 2 ∧ i.testBit 0 = true ↔ i = 2^h+1 := by
  have hfit : i < 2^(h+2) := by rw [show h+2=(h+1)+1 by omega, pow_succ]; omega
  have hs : ([0,h] : List ℕ).SortedLT := by simp [hh, List.sortedLT_nil]
  have hb := Nat.bitIndices_sum_map_two_pow hs
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, pow_zero,
    Nat.add_comm 1] at hb
  rw [allOnes hfit]
  constructor
  · rintro ⟨hk, hc, hl⟩
    have hlo : 0 ∈ i.bitIndices := Nat.mem_bitIndices.mpr hl
    have hhi : h ∈ i.bitIndices := by
      have ht := Nat.testBit_log2 hi.ne'
      rw [Nat.log2_eq_log_two, hk] at ht
      exact Nat.mem_bitIndices.mpr ht
    have hsub : ({0,h} : Finset ℕ) ⊆ i.bitIndices.toFinset := by
      simp [Finset.insert_subset_iff, hlo, hhi]
    have hcard : ({0,h} : Finset ℕ).card = 2 := by rw [Finset.card_insert_of_notMem (by simpa using hh.ne'.symm), Finset.card_singleton]
    have he := Finset.eq_of_subset_of_card_le hsub (hc.trans hcard.symm).le
    apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [← Nat.mem_bitIndices, ← Nat.mem_bitIndices, hb, ← List.mem_toFinset, ← he]
    simp
  · rintro rfl
    have hp := Nat.one_lt_two_pow hh.ne'
    have hk : Nat.log 2 (2^h+1) = h :=
      Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [pow_succ]; omega)
    rw [hk, hb, ← Nat.mem_bitIndices, hb]
    simp
    change ({0,h} : Finset ℕ).card = 2
    rw [Finset.card_insert_of_notMem (by simpa using hh.ne'.symm), Finset.card_singleton]


namespace PhaseCode

private abbrev Pub := Fin 16
private abbrev Reg := Fin 48
private abbrev Code := Flow 48 16

/-- The public parameters locate the two index-scan words and the destination. -/
def setup (p : Parameters) : Code :=
  straight (.constant 0 0) [.constant 1 1, .publicWord 2 p.height, .binary .sub 3 2 1,
    .publicWord 4 p.highestAddress, .publicWord 5 p.populationAddress, .publicWord 6 p.outputAddress,
    .read 7 4, .read 8 5]

private def store (b : Bool) : Code := .line (.write 6 (if b then 1 else 0))
private def single : Code := .ifEq 8 1 (store true) (store false)
private def middle : Code := .ifEq 7 3 single (store false)

/-- Select the native comparison and Boolean store that implement the requested phase flag. -/
def dispatch : Flag → Code
  | .first => .ifEq 7 0 (store true) (store false)
  | .middle => middle
  | .firstHalf => .ifLt 7 3 (store true) middle
  | .last => .ifEq 7 2 (store true) (store false)

/-- Load the scanned index summary and execute the test for the requested group flag. -/
def block (p : Parameters) (f : Flag) : Code := .seq (setup p) (dispatch f)

variable {w : ℕ}

private def loaded (pub : Pub → Word w) (p : Parameters) (m : Memory w) (rs : Regs w 48) : Regs w 48 :=
  let vs : List (Reg × Word w) :=
    [(0,0),(1,1),(2,pub p.height),(3,pub p.height-1),
      (4,pub p.highestAddress),(5,pub p.populationAddress),(6,pub p.outputAddress),
      (7,m (pub p.highestAddress).val),(8,m (pub p.populationAddress).val)]
  vs.foldl (fun a j => Function.update a j.1 j.2) rs

private def setupEvents (pub : Pub → Word w) (p : Parameters) (m : Memory w) : List (Event w) :=
  List.replicate 7 .tick ++ [.read (pub p.highestAddress) (m (pub p.highestAddress).val),
    .read (pub p.populationAddress) (m (pub p.populationAddress).val)]

private theorem setup_exec (pub : Pub → Word w) (p : Parameters) (state : Word w) (m : Memory w)
    (rs : Regs w 48) : Flow.Exec pub state (setup p) rs m (setupEvents pub p m) (loaded pub p m rs) m :=
  (Flow.once_sound pub state false (setup p) rs m rfl).1

private def Verdict (rs : Regs w 48) : Flag → Prop
  | .first => rs 7 = rs 0
  | .middle => rs 7 = rs 3 ∧ rs 8 = rs 1
  | .firstHalf => rs 7 < rs 3 ∨ rs 7 = rs 3 ∧ rs 8 = rs 1
  | .last => rs 7 = rs 2

private instance (rs : Regs w 48) (f : Flag) : Decidable (Verdict rs f) := by
  cases f <;> unfold Verdict <;> infer_instance

/-- A successful flag write after at most three conditional instructions. -/
private def Writes (pub : Pub → Word w) (state : Word w) (rs : Regs w 48) (m : Memory w)
    (a : Code) (v : Word w) (k : ℕ) : Prop :=
  ∃ n ≤ k, Flow.Exec pub state a rs m (List.replicate n .tick ++ [.write (rs 6) v]) rs (writeMemory m (rs 6) v)

private theorem Writes.store {pub : Pub → Word w} {state : Word w} {rs : Regs w 48} {m : Memory w}
    (b : Bool) : Writes pub state rs m (store b) (if b then rs 1 else rs 0) 0 := by
  cases b <;> exact ⟨0,by decide,.line rfl⟩

private theorem Writes.guard {pub : Pub → Word w} {state : Word w} {rs : Regs w 48} {m : Memory w}
    {a b : Code} {v : Word w} {k : ℕ} (hw : Writes pub state rs m a v k)
    (lift : ∀ es, Flow.Exec pub state a rs m es rs (writeMemory m (rs 6) v) →
      Flow.Exec pub state b rs m (.tick :: es) rs (writeMemory m (rs 6) v)) :
    Writes pub state rs m b v (k+1) := by
  obtain ⟨n,hn,hr⟩ := hw
  exact ⟨n+1,by omega,by simpa [List.replicate_succ] using lift _ hr⟩

private theorem Writes.weaken {pub : Pub → Word w} {state : Word w} {rs : Regs w 48} {m : Memory w}
    {a : Code} {v : Word w} {k k' : ℕ} (hw : Writes pub state rs m a v k) (h : k ≤ k') :
    Writes pub state rs m a v k' := by obtain ⟨n,hn,hr⟩ := hw; exact ⟨n,hn.trans h,hr⟩

private theorem eq_exec {pub : Pub → Word w} {state : Word w} {rs : Regs w 48} {m : Memory w}
    (x y : Reg) : Writes pub state rs m (.ifEq x y (store true) (store false))
      (if rs x = rs y then rs 1 else rs 0) 1 := by
  split_ifs with h
  · exact (Writes.store true).guard (fun _ e => .ifEqYes h e)
  · exact (Writes.store false).guard (fun _ e => .ifEqNo h e)

private theorem middle_exec {pub : Pub → Word w} {state : Word w} {rs : Regs w 48} {m : Memory w} :
    Writes pub state rs m middle (if rs 7 = rs 3 ∧ rs 8 = rs 1 then rs 1 else rs 0) 2 := by
  by_cases h : rs 7 = rs 3
  · simp only [h, true_and]
    exact (eq_exec 8 1).guard (fun _ e => .ifEqYes h e)
  · rw [ite_eq_right (fun he => h he.1)]
    exact ((Writes.store false).guard (fun _ e => .ifEqNo h e)).weaken (by decide)

private theorem dispatch_exec {pub : Pub → Word w} {state : Word w} {rs : Regs w 48} {m : Memory w}
    (f : Flag) : Writes pub state rs m (dispatch f) (if Verdict rs f then rs 1 else rs 0) 3 := by
  cases f with
  | first => exact (eq_exec 7 0).weaken (by decide)
  | last => exact (eq_exec 7 2).weaken (by decide)
  | middle => exact middle_exec.weaken (by decide)
  | firstHalf =>
    by_cases h : rs 7 < rs 3
    · have hv : Verdict rs .firstHalf := Or.inl h
      rw [ite_eq_left hv]
      exact ((Writes.store true).guard (fun _ e => .ifLtYes h e)).weaken (by decide)
    · have hv : Verdict rs .firstHalf ↔ rs 7 = rs 3 ∧ rs 8 = rs 1 := by simp [Verdict, h]
      rw [if_congr hv rfl rfl]
      exact middle_exec.guard (fun _ e => .ifLtNo h e)

/-- A deterministic native flag computation on the output of the index scan.
Its two reads and one write take at most thirteen instructions including tests. -/
theorem block_exec (pub : Pub → Word w) (p : Parameters) (state : Word w) (m : Memory w)
    (rs : Regs w 48) (h i c : ℕ) (f : Flag) (hi : 0 < i) (hend : i ≤ 2^(h+1))
    (hc : c = 1 ↔ i = 2 ^ Nat.log 2 i) (hh : (pub p.height).val = h+1)
    (hk' : (m (pub p.highestAddress).val).val = Nat.log 2 i)
    (hc' : (m (pub p.populationAddress).val).val = c) :
    let v := encodeBit w (decide (f.holds h i))
    ∃ es out, Flow.Exec pub state (block p f) rs m es out (writeMemory m (pub p.outputAddress) v) ∧
      countProbes es = 3 ∧ choiceBits es = [] ∧ es.length ≤ 13 := by
  let a := loaded pub p m rs
  obtain ⟨n,hn,hr⟩ := dispatch_exec (pub := pub) (state := state) (rs := a) (m := m) f
  have hgt := (pub p.height).isLt
  rw [hh] at hgt
  have h0 : (a 0).val = 0 := rfl
  have h1 : (a 1).val = 1 := by
    change (1 : Word w).val = 1
    exact Nat.mod_eq_of_lt (by omega : 1 < 2^w)
  have h2 : (a 2).val = h+1 := hh
  have h3 : (a 3).val = h := by
    change (a 2 - a 1).val = h
    rw [Fin.sub_val_of_le (by change (a 1).val ≤ _; omega),h2,h1]
    omega
  have h7 : (a 7).val = Nat.log 2 i := hk'
  have h8 : (a 8).val = c := hc'
  have hz := endpoints_iff (h+1) i hi hend
  have hv : Verdict a f ↔ f.holds h i := by
    cases f <;> simp only [Verdict, Flag.holds, Fin.ext_iff, Fin.lt_def, h0, h1, h2, h3, h7, h8]
    · exact hz.1
    · constructor
      · rintro ⟨he,hc'⟩
        simpa [he] using hc.mp hc'
      · rintro rfl
        simp [Nat.log_pow (by decide : 1 < 2), hc]
    · exact firstHalf_iff h i c hi hc
    · exact hz.2
  let v := encodeBit w (decide (f.holds h i))
  have hv' : (if Verdict a f then a 1 else a 0) = v := by
    by_cases he : f.holds h i
    · rw [ite_eq_left (hv.mpr he)]; simp [v, he, encodeBit]; rfl
    · rw [ite_eq_right (mt hv.mp he)]; simp [v, he, encodeBit]; rfl
  have hout : a 6 = pub p.outputAddress := rfl
  rw [hv', hout] at hr
  refine ⟨_,a,(setup_exec pub p state m rs).seq hr, ?_, ?_, ?_⟩
  · have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hn' with rfl | rfl | rfl | rfl <;> rfl
  · have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hn' with rfl | rfl | rfl | rfl <;> rfl
  · simp [setupEvents]; omega

/-- The first tail group needs the low bit as well as the high position and
population. Its low bit is at the base of the copied index array. -/
private def lowLoad (lowAddress : Pub) : Code :=
  straight (.constant 9 2) [.publicWord 10 lowAddress, .read 11 10]

private def twoLow : Code := .ifEq 8 9 (.ifEq 11 1 (store true) (store false)) (store false)
private def highTwoLow : Code := .ifEq 7 3 twoLow (store false)
private def tailDispatch : Code :=
  .ifEq 3 0 (dispatch .last) highTwoLow

/-- Load the index summary and low digit to test whether this is the first group after the
midpoint. -/
def firstTailBlock (p : Parameters) (lowAddress : Pub) : Code :=
  .seq (setup p) (.seq (lowLoad lowAddress) tailDispatch)

private def lowRegs (pub : Pub → Word w) (lowAddress : Pub) (m : Memory w) (rs : Regs w 48) :=
  Function.update (Function.update (Function.update rs (9 : Reg) 2) (10 : Reg) (pub lowAddress))
    (11 : Reg) (m (pub lowAddress).val)

private theorem lowLoad_exec (pub : Pub → Word w) (lowAddress : Pub) (state : Word w) (m : Memory w)
    (rs : Regs w 48) : Flow.Exec pub state (lowLoad lowAddress) rs m
    [.tick,.tick,.read (pub lowAddress) (m (pub lowAddress).val)] (lowRegs pub lowAddress m rs) m :=
  (Flow.once_sound pub state false _ rs m rfl).1

private theorem andEq {pub : Pub → Word w} {state : Word w} {rs : Regs w 48} {m : Memory w}
    {a : Code} {x y : Reg} {P : Prop} [Decidable P] {k : ℕ}
    (hw : Writes pub state rs m a (if P then rs 1 else rs 0) k) :
    Writes pub state rs m (.ifEq x y a (store false)) (if rs x = rs y ∧ P then rs 1 else rs 0) (k+1) := by
  by_cases he : rs x = rs y
  · simp only [he, true_and]
    exact hw.guard (fun _ e => .ifEqYes he e)
  · simp only [he, false_and, ↓reduceIte]
    exact ((Writes.store false).guard (fun _ e => .ifEqNo he e)).weaken (by omega)

private theorem tailDispatch_exec {pub : Pub → Word w} {state : Word w} {rs : Regs w 48} {m : Memory w} :
    let value := if rs 3 = rs 0 then (if rs 7 = rs 2 then rs 1 else rs 0)
      else if rs 7 = rs 3 ∧ rs 8 = rs 9 ∧ rs 11 = rs 1 then rs 1 else rs 0
    Writes pub state rs m tailDispatch value 4 := by
  dsimp only
  by_cases he : rs 3 = rs 0
  · rw [ite_eq_left he]
    exact ((eq_exec 7 2).guard (fun _ e => .ifEqYes he e)).weaken (by decide)
  · rw [ite_eq_right he]
    exact (andEq (andEq (eq_exec 11 1))).guard (fun _ e => .ifEqNo he e)

/-- The group after the midpoint alone is designated for initialization.
This test covers the two-group chain and reads a total of three scratch
words before writing its decision. -/
theorem firstTail_exec (hw : 2 ≤ w) (pub : Pub → Word w) (p : Parameters) (lowAddress : Pub)
    (state : Word w) (m : Memory w) (rs : Regs w 48) (h i : ℕ) (hi : 0 < i) (hend : i ≤ 2^(h+1))
    (hh : (pub p.height).val = h+1) (hk : (m (pub p.highestAddress).val).val = Nat.log 2 i)
    (hc : (m (pub p.populationAddress).val).val = (LiveHeader.prefixOnes i (h+2)).card)
    (hlo : m (pub lowAddress).val = encodeBit w (i.testBit 0)) :
    let v := encodeBit w (decide (i = 2^h+1))
    ∃ es out, Flow.Exec pub state (firstTailBlock p lowAddress) rs m es out (writeMemory m (pub p.outputAddress) v) ∧
      countProbes es = 4 ∧ choiceBits es = [] ∧ es.length ≤ 17 := by
  let a := loaded pub p m rs
  let b := lowRegs pub lowAddress m a
  obtain ⟨n,hn,hr⟩ := tailDispatch_exec (pub := pub) (state := state) (rs := b) (m := m)
  have ht : 2 < 2^w := calc
    2 < 2^2 := by decide
    _ ≤ 2^w := Nat.pow_le_pow_right (by decide) hw
  have h0 : (b 0).val = 0 := rfl
  have h1 : (b 1).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < 2^w)
  have h2 : (b 2).val = h+1 := hh
  have h3 : (b 3).val = h := by
    change (b 2 - b 1).val = h
    rw [Fin.sub_val_of_le (by change (b 1).val ≤ _; omega), h2, h1]
    omega
  have h7 : (b 7).val = Nat.log 2 i := hk
  have h8 : (b 8).val = (LiveHeader.prefixOnes i (h+2)).card := hc
  have h9 : (b 9).val = 2 := Nat.mod_eq_of_lt ht
  have h11 : b 11 = b 1 ↔ i.testBit 0 = true := by
    change m (pub lowAddress).val = (1 : Word w) ↔ _
    rw [hlo, encodeBit_eq_one (by omega)]
  let v := encodeBit w (decide (i = 2^h+1))
  have hv : (if b 3 = b 0 then (if b 7 = b 2 then b 1 else b 0)
      else if b 7 = b 3 ∧ b 8 = b 9 ∧ b 11 = b 1 then b 1 else b 0) = v := by
    have hz : b 3 = b 0 ↔ h = 0 := by simp only [Fin.ext_iff,h3,h0]
    by_cases he : h = 0
    · rw [ite_eq_left (hz.mpr he)]
      have hlast : b 7 = b 2 ↔ i = 2^h+1 := by
        rw [Fin.ext_iff, h7, h2, (endpoints_iff (h+1) i hi hend).2, he]
        rfl
      rw [if_congr hlast rfl rfl]
      by_cases ht : i = 2^h+1 <;> simp [v,ht,encodeBit] <;> rfl
    · rw [ite_eq_right (mt hz.mp he)]
      have hs : b 7 = b 3 ∧ b 8 = b 9 ∧ b 11 = b 1 ↔ i = 2^h+1 := by
        rw [h11]
        simpa only [Fin.ext_iff, h7,h3,h8,h9] using firstTail_iff (by omega : 0 < h) hi hend
      rw [if_congr hs rfl rfl]
      by_cases ht : i = 2^h+1 <;> simp [v,ht,encodeBit] <;> rfl
  have hout : b 6 = pub p.outputAddress := rfl
  rw [hv,hout] at hr
  refine ⟨_,b,(setup_exec pub p state m rs).seq ((lowLoad_exec pub lowAddress state m a).seq hr), ?_, ?_, ?_⟩
  · have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hn' with rfl | rfl | rfl | rfl | rfl <;> rfl
  · have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hn' with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp [setupEvents]; omega

end PhaseCode

/-- Direct composition with the two summary words of the header scan. -/
theorem scanned_width_exec {w : ℕ} (pub : Fin 16 → Word w) (p : Parameters) (state : Word w) (m : Memory w)
    (rs : Regs w 48) (s : Slot) (h Δ i : ℕ) (hi : 0 < i) (hend : i ≤ 2^(h+1)) (hneed : Needed h i s)
    (hh : (pub p.height).val = h+1) (hΔ : (pub p.delta).val = Δ)
    (hk : (m (pub p.highestAddress).val).val = LiveHeader.prefixHigh i (h+2))
    (hc : (m (pub p.populationAddress).val).val = (LiveHeader.prefixOnes i (h+2)).card)
    (hfit : (h+1)*Δ < 2^w) :
    let v : Word w := Fin.ofNat _ (CutSchedule.width (h+1) Δ (index i s))
    ∃ out, Flow.Exec pub state (WidthCode.block p s) rs m (WidthCode.events pub p m s v) out
      (writeMemory m (pub p.outputAddress) v) ∧ v.val = CutSchedule.width (h+1) Δ (index i s) := by
  have hb : i < 2^(h+2) := by rw [show h+2 = (h+1)+1 by omega, pow_succ]; omega
  obtain ⟨hk',hc'⟩ := LiveHeader.summary_correct hi.ne' hb
  exact WidthCode.needed_exec pub p state m rs s h Δ i _ hi hend hneed hc' hh hΔ (hk.trans hk') hc hfit

end LiveHeaderWidths

end VPVNP
end Computability
end OAI
