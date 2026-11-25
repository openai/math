import OAI.Computability.BorderVNP.TransmissionBit

/-! # Actual public directory reads for the routed evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open DiagonalResidueRAM (effect effect_runs)

/-- An interval in the directory. The type tag distinguishes data delivery from a
wire shared by two substituted tables. -/
structure Range (w : ℕ) where
  /-- Zero for a shared wire, one for delivery. -/
  kind : Word w
  /-- Origin or first wire endpoint. -/
  teamA : Word w
  /-- Recipient or second endpoint. -/
  teamB : Word w
  /-- Number of bits in this interval. -/
  width : Word w
  /-- Absolute address of the first source bit. -/
  source : Word w
  /-- Absolute address of the first endpoint slot. -/
  dstA : Word w
  /-- Absolute address of the second endpoint slot. -/
  dstB : Word w
  /-- First ordinal within the physical team pair. -/
  ordinal : Word w

variable {w : ℕ}

/-- Interpret seven successive directory words and the single base-ordinal word. -/
def rangeAt (m : Memory w) (base ord : Word w) : Range w :=
  ⟨m base.val, m (base+1).val, m (base+2).val, m (base+3).val, m (base+4).val,
    m (base+5).val, m (base+6).val, m ord.val⟩

/-- The seven words and their ordinal in the working bank. -/
def rangeBank (s : Bank w) : Range w := ⟨s 8,s 9,s 10,s 11,s 12,s 13,s 14,s 15⟩

/-- Register effect of one actual directory pop. -/
private def afterPop (m : Memory w) (s : Bank w) (d c : Reg) : Bank w :=
  Function.update (Function.update s d (m (s c).val)) c (s c + s 1)

private theorem pop_runs (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (d c : Reg) (hcd : c ≠ d) (h1 : (1 : Reg) ≠ d) :
    ∃ es, Runs pub macros (popWord d c) s m es (afterPop m s d c) m ∧ traceCost es = 2 := by
  have hload := Runs.load pub macros d c s m
  refine ⟨_,.seq hload (Runs.localStep _ rfl ?_),rfl⟩
  simp [Code.atom, BinaryOp.eval, afterPop,hcd,h1]

private theorem afterPop_apply (m : Memory w) (s : Bank w) (d c i : Reg) :
    afterPop m s d c i = if i=c then s c+s 1 else if i=d then m (s c).val else s i := by
  simp [afterPop,Function.update_apply]

/-- Fetching a range performs precisely the prescribed eight reads, leaves memory
unchanged, advances both cursors, and clears the within-range offset. -/
theorem loadRange_runs (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (h₁ : s 1 = 1) (h₀ : s 2 = 0) :
    ∃ es t, Runs pub macros loadRange s m es t m ∧ traceCost es = 17 ∧
      rangeBank t = rangeAt m (s 3) (s 6) ∧ t 3 = s 3 + 7 ∧ t 6 = s 6 + 1 ∧ t 16 = 0 ∧
      (∀ i : Reg, i.val ≤ 5 → i ≠ 3 → t i = s i) := by
  let s1 := afterPop m s 8 3
  obtain ⟨e0,r0,h0c⟩ := pop_runs pub macros m s 8 3 (by decide) (by decide)
  let s2 := afterPop m s1 9 3
  obtain ⟨e1,r1,h1c⟩ := pop_runs pub macros m s1 9 3 (by decide) (by decide)
  let s3 := afterPop m s2 10 3
  obtain ⟨e2,r2,h2c⟩ := pop_runs pub macros m s2 10 3 (by decide) (by decide)
  let s4 := afterPop m s3 11 3
  obtain ⟨e3,r3,h3c⟩ := pop_runs pub macros m s3 11 3 (by decide) (by decide)
  let s5 := afterPop m s4 12 3
  obtain ⟨e4,r4,h4c⟩ := pop_runs pub macros m s4 12 3 (by decide) (by decide)
  let s6 := afterPop m s5 13 3
  obtain ⟨e5,r5,h5c⟩ := pop_runs pub macros m s5 13 3 (by decide) (by decide)
  let s7 := afterPop m s6 14 3
  obtain ⟨e6,r6,h6c⟩ := pop_runs pub macros m s6 14 3 (by decide) (by decide)
  let s8 := afterPop m s7 15 6
  obtain ⟨e7,r7,h7c⟩ := pop_runs pub macros m s7 15 6 (by decide) (by decide)
  let t := Function.update s8 16 (s8 2)
  have rc : Runs pub macros (.copy 16 2) s8 m [tick w] t m := Runs.localStep _ rfl rfl
  refine ⟨_,t,r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq rc))))))),?_,?_,?_,?_,?_,?_⟩
  · simp only [cost_append,h0c,h1c,h2c,h3c,h4c,h5c,h6c,h7c]; rfl
  all_goals try
    intro i hi h3
    have above (a : Reg) (h : 5 < a.val) : i ≠ a := by intro e; subst i; omega
    simp (config := { decide := true }) [t,s8,s7,s6,s5,s4,s3,s2,s1,afterPop_apply,above,h3]
  all_goals
    have addWord (i j : ℕ) : (Fin.ofNat _ i : Word w) + Fin.ofNat _ j = Fin.ofNat _ (i+j) :=
      Fin.ext (Nat.add_mod ..).symm
    have h2 : (1 : Word w) + 1 = 2 := addWord 1 1
    have h3 : (1 : Word w) + 2 = 3 := addWord 1 2
    have h4 : (1 : Word w) + 3 = 4 := addWord 1 3
    have h5 : (1 : Word w) + 4 = 5 := addWord 1 4
    have h6 : (1 : Word w) + 5 = 6 := addWord 1 5
    have h7 : (1 : Word w) + 6 = 7 := addWord 1 6
    simp (config := { decide := true }) [rangeBank,rangeAt,t,s8,s7,s6,s5,s4,s3,s2,s1,afterPop_apply,h₁,h₀,add_assoc]
    all_goals simp only [h2,h3,h4,h5,h6,h7] <;> trivial

/-- The start-of-directory frame in actual initialized shared memory. -/
def directoryFrame (pub : Arg → Word w) (m : Memory w) (i : Word w) := m (pub 0 + i).val

/-- The setup opcode table loads the relevant memory-frame words and sets both
loop constants independently of the incoming register bank. -/
theorem setup_runs (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) :
    ∃ es t, Runs pub macros setup s m es t m ∧ traceCost es ≤ setup.slots ∧
      t 0 = directoryFrame pub m 0 ∧ t 1 = 1 ∧ t 2 = 0 ∧ t 5 = 0 ∧
      t 3 = directoryFrame pub m 12 ∧ t 4 = directoryFrame pub m 13 ∧
      t 6 = directoryFrame pub m 20 := by
  let F (i : Word w) := m (pub 0 + i).val
  have read (d a scratch : Reg) (field : Word 8) (b : Bank w)
      (das : a ≠ scratch) :
      ∃ es u, Runs pub macros (readFrame d a scratch field) b m es u m ∧ traceCost es = 4 ∧
        u = Function.update (Function.update (Function.update b scratch (Fin.ofNat _ field.val))
          a (pub 0 + Fin.ofNat _ field.val)) d (F (Fin.ofNat _ field.val)) := by
    let s₁ := Function.update b a (pub 0)
    let s₂ := Function.update s₁ scratch (Fin.ofNat _ field.val)
    let s₃ := Function.update s₂ a (pub 0 + Fin.ofNat _ field.val)
    have eq : s₂ a = pub 0 := by simp [s₂,s₁,das]
    have eq₂ : s₂ scratch = Fin.ofNat _ field.val := Function.update_self ..
    have h3 : Runs pub macros (.binary .add a a scratch) s₂ m [tick w] s₃ m :=
      Runs.localStep _ rfl (by simp only [Code.atom, BinaryOp.eval, eq, eq₂]; rfl)
    have r₄ := Runs.load pub macros d a s₃ m
    refine ⟨_,_,Runs.seq (Runs.localStep _ rfl rfl) (.seq (Runs.localStep _ rfl rfl) (.seq h3 r₄)), rfl, ?_⟩
    simp [s₃,s₂,s₁,F,Function.update_comm das,Function.update_idem]
  obtain ⟨e0,s0,r0,h0,hs0⟩ := read 0 27 28 0 s (by decide)
  let s1 := Function.update s0 1 (1 : Word w)
  let s2 := Function.update s1 2 (0 : Word w)
  have r1 : Runs pub macros (.constant 1 1) s0 m [tick w] s1 m := Runs.localStep _ rfl rfl
  have r2 : Runs pub macros (.constant 2 0) s1 m [tick w] s2 m := Runs.localStep _ rfl rfl
  obtain ⟨e3,s3,r3,h3,hs3⟩ := read 3 27 28 12 s2 (by decide)
  obtain ⟨e4,s4,r4,h4,hs4⟩ := read 4 27 28 13 s3 (by decide)
  let s5 := Function.update s4 5 (s4 2)
  have r5 : Runs pub macros (.copy 5 2) s4 m [tick w] s5 m := Runs.localStep _ rfl rfl
  obtain ⟨e6,s6,r6,h6,hs6⟩ := read 6 27 28 20 s5 (by decide)
  refine ⟨_,s6,Runs.seq r0 (.seq r1 (.seq r2 (.seq r3 (.seq r4 (.seq r5 r6))))),?_,?_⟩
  · simp only [cost_append,h0,h3,h4,h6]; rfl
  · simp [hs6,s5,hs4,hs3,s2,s1,hs0,F,directoryFrame]

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
