import OAI.Computability.BorderVNP.RoutingISAAddressFit
import OAI.Computability.BorderVNP.RoutingISAHeader

/-! # Native zero checks on the unused suffix of a physical block -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Inspect one physical word, reject a nonzero value, and advance the position. -/
def zeroScanBody : Code := .block [
  .copy 30 11, .copy 31 10, physicalAddress, .load 12 48, requireEq 12 0,
  .binary .add 10 10 1]

/-- Inspect the interval from register 10 up to the bound in register 7. -/
def zeroScan : Code := .whileLt 10 7 zeroScanBody

/-- Literal memory address of one physical position of the specified partner. -/
def zeroScanAddr (pub : Arg → ℕ) (mem : ℕ → ℕ) (partner pos : ℕ) : ℕ :=
  physicalBitAddress (frameField pub mem 0) (frameField pub mem 1)
    (frameField pub mem 3) (frameField pub mem 4) partner pos

/-- Bounds needed for unsigned address computation throughout the scanned interval. -/
structure ZeroScanRoom (w : ℕ) (pub : Arg → ℕ) (mem : ℕ → ℕ)
    (partner start limit : ℕ) : Prop where
  /-- Address of the last frame word used by physical addressing. -/
  frame : pub 0 + 4 < 2 ^ w
  /-- Positive number of teams. -/
  teamsPos : 0 < frameField pub mem 1
  /-- Positive width of the exterior field. -/
  linkPos : 0 < frameField pub mem 4
  /-- The scanned partner is distinct from the scanning team. -/
  distinct : partner ≠ frameField pub mem 0
  /-- The complete processor input stride fits. -/
  stride : 2 * frameField pub mem 3 + (frameField pub mem 1 - 1) * frameField pub mem 4 < 2 ^ w
  /-- Each addressed input word lies within the word address space. -/
  address (j : ℕ) : start ≤ j → j < limit → zeroScanAddr pub mem partner j < 2 ^ w

private def protectedRegs {w : ℕ} (s t : Bank w) : Prop :=
  ∀ i : Reg, i.val < 30 → i ≠ 10 → i ≠ 12 → t i = s i

/-- The scan returns at the limit and preserves every low register except the
cursor and the register receiving the loaded bit. -/
def ZeroScanResult {w : ℕ} (s t : Bank w) : Prop :=
  (t 10).val = (s 7).val ∧ ∀ i : Reg, i.val < 30 → i ≠ 10 → i ≠ 12 → t i = s i

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem afterFirst {a b : Code} {s m fs t mt} (first : Runs pub macros a s m fs t mt)
    (hd : a.deterministic = true) {es u mu} (all : Runs pub macros (.seq a b) s m es u mu) :
    ∃ gs, Runs pub macros b t mt gs u mu := by
  cases all with
  | atom h _ _ => cases h
  | seq left right =>
    obtain ⟨_,rfl,rfl⟩ := first.unique_of_deterministic hd left
    exact ⟨_,right⟩

private theorem requireEq_return {x y : Reg} {s m es t mt}
    (r : Runs pub macros (requireEq x y) s m es t mt) : s x = s y := by
  cases r with
  | atom h _ _ => cases h
  | ifEq h =>
    by_contra hn
    simp only [hn, ite_false] at h
    cases h with | atom h _ _ => cases h

private theorem zeroStep (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (m : Memory w)
    (s : Bank w) (start limit : ℕ) (h₀ : (s 0).val = 0) (h₁ : (s 1).val = 1)
    (lo : start ≤ (s 10).val) (hi : (s 10).val < limit) (fit : limit < 2 ^ w)
    (room : ZeroScanRoom w (readings pub) (readings m) (s 11).val start limit) :
    let addr := zeroScanAddr (readings pub) (readings m) (s 11).val (s 10).val
    ∃ t, (t 10).val = (s 10).val + 1 ∧ protectedRegs s t ∧
      ((m addr).val = 0 → ∃ es, Runs pub macros zeroScanBody s m es t m ∧
        traceCost es ≤ zeroScanBody.slots) ∧
      ∀ es u mu, Runs pub macros zeroScanBody s m es u mu →
        u = t ∧ mu = m ∧ (m addr).val = 0 := by
  dsimp only
  let a := Function.update s (30 : Reg) (s 11)
  let b := Function.update a (31 : Reg) (a 10)
  have ca : Runs pub macros (.copy 30 11) s m [tick w] a m := .localStep m rfl rfl
  have cb : Runs pub macros (.copy 31 10) a m [tick w] b m := .localStep m rfl rfl
  have left : (b 30).val = (s 11).val := by simp (config := { decide := true }) [a,b]
  have right : (b 31).val = (s 10).val := by simp (config := { decide := true }) [a,b]
  have safe : physicalAddress.safeReadOnly w (readings pub) (readings m) (readings b) := by
    refine physicalAddress_safe _ _ _ room.frame room.teamsPos room.linkPos ?_ room.stride ?_
    · simpa only [readings, left] using room.distinct
    · simpa only [readings, left, right, zeroScanAddr] using room.address _ lo hi
  obtain ⟨es,u,ru,cu,au,pu,_⟩ := physicalAddress_run pub macros m b safe
  rw [left,right] at au
  change (u 48).val = zeroScanAddr (readings pub) (readings m) (s 11).val (s 10).val at au
  have low (i : Reg) (h : i.val < 30) : u i = s i := by
    rw [pu _ h]
    have h₃₀ : i ≠ 30 := by rintro rfl; exact (by decide : ¬ (30 : Reg).val < 30) h
    have h₃₁ : i ≠ 31 := by rintro rfl; exact (by decide : ¬ (31 : Reg).val < 30) h
    simp [b,a,h₃₀,h₃₁]
  let l := Function.update u (12 : Reg) (m (u 48).val)
  have rl := Runs.load pub macros 12 48 u m
  have lowL (i : Reg) (h : i.val < 30) (h' : i ≠ 12) : l i = s i := by
    simpa only [l, Function.update_of_ne h'] using low i h
  have l₀ := lowL 0 (by decide) (by decide)
  have l₁ := lowL 1 (by decide) (by decide)
  have l₁₀ := lowL 10 (by decide) (by decide)
  let inc : Code := .binary .add 10 10 1
  have safeInc : inc.safeReadOnly w (readings pub) (readings m) (readings l) := by
    change (l 10).val + (l 1).val < 2 ^ w
    rw [l₁₀,l₁,h₁]
    omega
  obtain ⟨ts,t,rt,ct,ht⟩ := inc.runReadOnly pub macros m l safeInc
  have check : l 12 = l 0 ↔ (m (zeroScanAddr (readings pub) (readings m)
      (s 11).val (s 10).val)).val = 0 := by
    rw [l₀, ← Fin.val_inj, h₀, show l 12 = m (u 48).val by simp [l], au]
  have toc : (t 10).val = (s 10).val + 1 := by
    simpa [inc, Code.evalNat, readings, addressOp, l₁₀, l₁, h₁] using congrFun ht 10
  have kept : protectedRegs s t := by
    intro i hi h₁₀ h₁₂
    apply Fin.ext
    simpa only [inc, Code.evalNat, Function.update_of_ne h₁₀, readings, lowL i hi h₁₂]
      using congrFun ht i
  have execute (zero : (m (zeroScanAddr (readings pub) (readings m) (s 11).val (s 10).val)).val = 0) :
      ∃ gs, Runs pub macros zeroScanBody s m gs t m ∧ traceCost gs ≤ zeroScanBody.slots := by
    have nop : Runs pub macros .nop l m [tick w] l m := .localStep m rfl rfl
    have cmp : Runs pub macros (requireEq 12 0) l m [tick w,tick w] l m :=
      .ifEq (by simpa only [check.mpr zero, ite_true] using nop)
    refine ⟨_, ca.seq (cb.seq (ru.seq (rl.seq (cmp.seq rt)))), ?_⟩
    simp only [zeroScanBody, Code.block, Code.slots, requireEq] at *
    simp only [traceCost, VPVNP.RAMBuckets.cost_append, VPVNP.RAMBuckets.cost, tick,
      TeamTranscript.Action.extra] at *
    change traceCost es ≤ physicalAddress.slots at cu
    change traceCost ts ≤ 1 at ct
    change 1 + (1 + (traceCost es + (1 + (2 + traceCost ts)))) ≤ 1 + (1 + (physicalAddress.slots + (1 + ((1+1+1)+1))))
    omega
  refine ⟨t,toc,kept,execute,?_⟩
  intro fs z mz r
  obtain ⟨_,r₁⟩ := afterFirst ca rfl r
  obtain ⟨_,r₂⟩ := afterFirst cb rfl r₁
  obtain ⟨_,r₃⟩ := afterFirst ru (by decide) r₂
  obtain ⟨_,r₄⟩ := afterFirst rl rfl r₃
  have he : l 12 = l 0 := by
    cases r₄ with
    | atom ha _ _ => cases ha
    | seq first _ => exact requireEq_return first
  obtain ⟨gs,rg,_⟩ := execute (check.mp he)
  exact ⟨(r.unique_of_deterministic (by decide) rg).2.1,
    (r.unique_of_deterministic (by decide) rg).2.2, check.mp he⟩

private def zeroRange {w : ℕ} (pub : Arg → Word w) (m : Memory w) (s : Bank w) : Prop :=
  ∀ j, (s 10).val ≤ j → j < (s 7).val →
    (m (zeroScanAddr (readings pub) (readings m) (s 11).val j)).val = 0

private theorem scanPaths (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (h₀ : (s 0).val = 0) (h₁ : (s 1).val = 1)
    (bounds : (s 10).val ≤ (s 7).val)
    (room : ZeroScanRoom w (readings pub) (readings m) (s 11).val (s 10).val (s 7).val) :
    (zeroRange pub m s → ∃ es t, Runs pub macros zeroScan s m es t m ∧
      traceCost es ≤ ((s 7).val - (s 10).val) * (zeroScanBody.slots + 1) + 1 ∧ ZeroScanResult s t) ∧
    ∀ es t mt, Runs pub macros zeroScan s m es t mt →
      mt = m ∧ ZeroScanResult s t ∧ zeroRange pub m s := by
  by_cases guard : (s 10).val < (s 7).val
  · obtain ⟨u,cursor,keep,forward,backward⟩ :=
      zeroStep pub macros m s (s 10).val (s 7).val h₀ h₁ le_rfl guard (s 7).isLt room
    have boundReg := keep 7 (by decide) (by decide) (by decide)
    have partner := keep 11 (by decide) (by decide) (by decide)
    have nextBound : (u 10).val ≤ (u 7).val := by rw [cursor,boundReg]; exact guard
    have nextRoom : ZeroScanRoom w (readings pub) (readings m) (u 11).val (u 10).val (u 7).val := by
      rw [partner,boundReg]
      exact {room with address := fun j hj hk => room.address j (by omega) hk}
    have z := congrArg Fin.val (keep 0 (by decide) (by decide) (by decide))
    have o := congrArg Fin.val (keep 1 (by decide) (by decide) (by decide))
    obtain ⟨nextYes,nextSound⟩ := scanPaths pub macros m u (z.trans h₀) (o.trans h₁) nextBound nextRoom
    have post (t : Bank w) (res : ZeroScanResult u t) : ZeroScanResult s t :=
      ⟨res.1.trans (congrArg Fin.val boundReg),
        fun i hi h₁₀ h₁₂ => (res.2 i hi h₁₀ h₁₂).trans (keep i hi h₁₀ h₁₂)⟩
    constructor
    · intro allZero
      obtain ⟨es,re,ce⟩ := forward (allZero _ le_rfl guard)
      have tailZero : zeroRange pub m u := by
        intro j hj hk
        rw [partner]
        rw [boundReg] at hk
        exact allZero j (by omega) hk
      obtain ⟨fs,t,rf,cf,ht⟩ := nextYes tailZero
      refine ⟨_,t,Runs.whileStep guard re rf,?_,post t ht⟩
      change 1 + traceCost (es ++ fs) ≤ _
      rw [show traceCost (es ++ fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
      rw [boundReg,cursor] at cf
      have len : (s 7).val - (s 10).val = ((s 7).val - ((s 10).val + 1)) + 1 := by omega
      rw [len, Nat.add_mul, one_mul]
      omega
    · intro es t mt r
      cases r with
      | atom h _ _ => cases h
      | whileDone hg => exact (hg guard).elim
      | whileStep _ first tail =>
        obtain ⟨rfl,rfl,zero⟩ := backward _ _ _ first
        obtain ⟨mem,res,rem⟩ := nextSound _ _ _ tail
        refine ⟨mem,post _ res,?_⟩
        intro j hj hk
        rcases eq_or_lt_of_le hj with h | h
        · simpa only [← h] using zero
        · have hz := rem j (by omega) (boundReg.symm ▸ hk)
          simpa only [partner] using hz
  · have same : (s 10).val = (s 7).val := by omega
    have ret : Runs pub macros zeroScan s m [tick w] s m := Runs.whileDone guard
    have cost : traceCost [tick w] ≤ ((s 7).val - (s 10).val) * (zeroScanBody.slots + 1) + 1 := by
      rw [same,Nat.sub_self,zero_mul,zero_add]
      exact le_rfl
    have result : ZeroScanResult s s := ⟨same,fun _ _ _ _ => rfl⟩
    constructor
    · exact fun _ => ⟨_,s,ret,cost,result⟩
    · intro es t mt r
      obtain ⟨_,rfl,rfl⟩ := ret.unique_of_deterministic (by decide) r
      exact ⟨rfl,result,fun j hj hk => by omega⟩
termination_by (s 7).val - (s 10).val
decreasing_by rw [boundReg,cursor]; omega

/-- If every position in the unused interval is zero, the scan returns after
one guard tick and at most one body plus a guard tick per physical position. -/
theorem zeroScan_run (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (m : Memory w)
    (s : Bank w) (h₀ : (s 0).val = 0) (h₁ : (s 1).val = 1) (bounds : (s 10).val ≤ (s 7).val)
    (room : ZeroScanRoom w (readings pub) (readings m) (s 11).val (s 10).val (s 7).val)
    (zero : ∀ j, (s 10).val ≤ j → j < (s 7).val →
      (m (zeroScanAddr (readings pub) (readings m) (s 11).val j)).val = 0) :
    ∃ es t, Runs pub macros zeroScan s m es t m ∧
      traceCost es ≤ ((s 7).val - (s 10).val) * (zeroScanBody.slots + 1) + 1 ∧ ZeroScanResult s t :=
  (scanPaths pub macros m s h₀ h₁ bounds room).1 zero

/-- Every normal return of the actual signed assembly certifies zero at all
positions in the scanned interval and returns with the original memory. -/
theorem zeroScan_sound (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (m : Memory w)
    (s : Bank w) (h₀ : (s 0).val = 0) (h₁ : (s 1).val = 1) (bounds : (s 10).val ≤ (s 7).val)
    (room : ZeroScanRoom w (readings pub) (readings m) (s 11).val (s 10).val (s 7).val)
    {es t mt} (run : Runs pub macros zeroScan s m es t mt) :
    mt = m ∧ ZeroScanResult s t ∧ ∀ j, (s 10).val ≤ j → j < (s 7).val →
      (m (zeroScanAddr (readings pub) (readings m) (s 11).val j)).val = 0 :=
  (scanPaths pub macros m s h₀ h₁ bounds room).2 es t mt run

end RoutingISA

end BorderVNP
end Computability
end OAI
