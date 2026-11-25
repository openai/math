import OAI.Optimization.LinearProgramming.RAM.Loops
import Mathlib.Tactic

/-! The fixed prefix of a bordered determinant request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderPacketHeader

open RAM

/-- Emit the tag, row count, and the consecutive row indices without reading
any data cell of the matrix or of an existing packet. -/
def block : Block :=
  .seq (Block.straight [.addrCopy 80 144, .addrCopy 82 144, .addrCopy 96 144,
    .const 0 0, .const 1 1, .store 96 0, .incr 96 96, .addrCopy 98 96,
    .incr 96 96, .incr 99 128]) <|
  .seq (.forRange 97 99 (Block.straight [.store 96 0, .incr 96 96, .add 0 0 1]))
    (Block.straight [.store 98 0, .incr 81 99, .incr 81 81])

/-- The exact address-register footprint, including the two packet anchors. -/
def addressScratch (j : ℕ) : Prop := j=80 ∨ j=81 ∨ j=82 ∨ j=96 ∨ j=97 ∨ j=98 ∨ j=99

instance (j : ℕ) : Decidable (addressScratch j) := by unfold addressScratch; infer_instance

structure Frame {K : Type*} (entry s : Memory K) (k base : ℕ) : Prop where
  data : ∀ j, 2 ≤ j → (j < base ∨ base+k+3 ≤ j) → s.data j = entry.data j
  index : ∀ j, ¬addressScratch j → s.index j = entry.index j

structure Output {K : Type*} [NatCast K] [Zero K] (k base : ℕ) (s : Memory K) : Prop where
  tag : s.data base = 0
  count : s.data (base+1) = ((k+1 : ℕ) : K)
  row : ∀ j ≤ k, s.data (base+2+j) = (j : K)
  packet : s.index 80 = base
  length : s.index 81 = k+3
  start : s.index 82 = base
  cursor : s.index 96 = base+k+3

variable {K : Type*}

private def Safe (P : K → Prop) (entry : Memory K) (k base : ℕ) (s : Memory K) : Prop :=
  (∀ i, P (s.data i)) ∧ Frame entry s k base

private theorem index_safe {P : K → Prop} {entry s : Memory K} {k base r v : ℕ}
    (hs : Safe P entry k base s) (hr : addressScratch r) :
    Safe P entry k base (s.putIndex r v) := by
  refine ⟨hs.1,⟨hs.2.data,fun j hj => ?_⟩⟩
  have h : j ≠ r := by rintro rfl; exact hj hr
  simpa [h] using hs.2.index j hj

private theorem data_safe {P : K → Prop} {entry s : Memory K} {k base r : ℕ} {x : K}
    (hs : Safe P entry k base s) (hr : r<2 ∨ (base ≤ r ∧ r < base+k+3)) (hx : P x) :
    Safe P entry k base (s.putData r x) := by
  constructor
  · intro j
    by_cases h : j = r
    · simpa [h] using hx
    · simpa [h] using hs.1 j
  · refine ⟨fun j hj hout => ?_, hs.2.index⟩
    have h : j ≠ r := by omega
    simpa [h] using hs.2.data j hj hout

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem copyIndex {P : K → Prop} {entry s : Memory K} {k base : ℕ} (d a v : ℕ)
    (hs : Safe P entry k base s) (hd : addressScratch d) (h : s.index a = v) :
    Block.Eval (Safe P entry k base) (.op (.addrCopy d a)) s 1 (s.putIndex d v) := by
  subst v
  exact .op hs (index_safe hs hd) (fun _ => rfl)

private theorem incrIndex {P : K → Prop} {entry s : Memory K} {k base : ℕ} (d a v : ℕ)
    (hs : Safe P entry k base s) (hd : addressScratch d) (h : s.index a + 1 = v) :
    Block.Eval (Safe P entry k base) (.op (.incr d a)) s 1 (s.putIndex d v) := by
  subst v
  exact .op hs (index_safe hs hd) (fun _ => rfl)

private theorem store {P : K → Prop} {entry s : Memory K} {k base : ℕ} (a r dest : ℕ) (v : K)
    (hs : Safe P entry k base s) (hd : s.index a = dest) (hv : s.data r = v)
    (hslot : base ≤ dest ∧ dest < base+k+3) :
    Block.Eval (Safe P entry k base) (.op (.store a r)) s 1 (s.putData dest v) := by
  subst dest v
  exact .op hs (data_safe hs (Or.inr hslot) (hs.1 r)) (fun _ => rfl)

private structure Scan (P : K → Prop) (entry : Memory K) (k base j : ℕ) (s : Memory K) : Prop where
  safe : Safe P entry k base s
  counter : s.index 97 = j
  limit : s.index 99 = k+1
  slot : s.index 96 = base+2+j
  countSlot : s.index 98 = base+1
  value : s.data 0 = (j : K)
  one : s.data 1 = 1
  tag : s.data base = 0
  prev : ∀ i < j, s.data (base+2+i) = (i : K)
  anchor : s.index 80 = base
  start : s.index 82 = base

private theorem loop_body {P : K → Prop} {entry s : Memory K} {k base j : ℕ} (hbase : 256 ≤ base)
    (hj : j < k+1) (h : Scan P entry k base j s)
    (hp : ∀ i ≤ k+1, P (i : K)) :
    ∃ t, Block.Eval (Safe P entry k base)
      (Block.straight [.store 96 0,.incr 96 96,.add 0 0 1]) s 3 t ∧
      Scan P entry k base (j+1) (t.putIndex 97 (t.index 97+1)) := by
  let a := s.putData (base+2+j) (j : K)
  let b := a.putIndex 96 (base+2+(j+1))
  let c := b.putData 0 ((j+1 : ℕ) : K)
  have e₁ : Block.Eval (Safe P entry k base) (.op (.store 96 0)) s 1 a :=
    store _ _ _ _ h.safe h.slot h.value (by omega)
  have e₂ : Block.Eval (Safe P entry k base) (.op (.incr 96 96)) a 1 b :=
    incrIndex _ _ _ e₁.safe_end (by decide) (by simp [a,h.slot,Nat.add_assoc])
  have hval : b.data 0 + b.data 1 = ((j+1 : ℕ) : K) := by
    simp [b,a,show 0≠base+2+j by omega,show 1≠base+2+j by omega,h.value,h.one]
  have e₃ : Block.Eval (Safe P entry k base) (.op (.add 0 0 1)) b 1 c := by
    refine .op e₂.safe_end (data_safe e₂.safe_end (Or.inl (by decide : 0<2)) (hp _ hj)) (fun pc => ?_)
    change some ((b.atPC pc).putData 0 (b.data 0 + b.data 1)) = _
    rw [hval]; rfl
  refine ⟨c, .seq e₁ (.seq e₂ (.seq e₃ (.skip e₃.safe_end))), ?_⟩
  constructor
  · exact index_safe e₃.safe_end (by decide : addressScratch 97)
  · simp [c,b,a,h.counter]
  · simp [c,b,a,h.limit]
  · simp [c,b]
  · simp [c,b,a,h.countSlot]
  · simp [c]
  · simp [c,b,a,show 1≠base+2+j by omega,h.one]
  · simp [c,b,a,show base≠0 by omega,show base≠base+2+j by omega,h.tag]
  · intro i hi
    by_cases hij : i=j
    · subst i; simp [c,b,a]
    · simp only [Memory.putIndex_data, c, Memory.putData_ne _ (by omega : base+2+i≠0), b, a,
        Memory.putData_ne _ (by omega : base+2+i≠base+2+j), h.prev i (by omega)]
  · simp [c,b,a,h.anchor]
  · simp [c,b,a,h.start]

/-- On arbitrary ordered-field memory the emitted scalars are just the
successive small nonnegative integers. The published frame applies throughout. -/
theorem run_block (entry : Memory K) (k base : ℕ) (hk : entry.index 128=k)
    (hbase : entry.index 144=base) (hlo : 256 ≤ base) (P : K → Prop)
    (hm : ∀ j, P (entry.data j)) (hp : ∀ i ≤ k+1, P (i : K)) :
    ∃ n, Block.Eval (fun s => (∀ j, P (s.data j)) ∧ Frame entry s k base) block entry (6*k+21) n ∧
      Output k base n := by
  have hsafe : Safe P entry k base entry := ⟨hm, ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩⟩
  let s₁ := entry.putIndex 80 base
  let s₂ := s₁.putIndex 82 base
  let s₃ := s₂.putIndex 96 base
  let s₄ := s₃.putData 0 0
  let s₅ := s₄.putData 1 1
  let s₆ := s₅.putData base 0
  let s₇ := s₆.putIndex 96 (base+1)
  let s₈ := s₇.putIndex 98 (base+1)
  let s₉ := s₈.putIndex 96 (base+2)
  let s₁₀ := s₉.putIndex 99 (k+1)
  have e₁ : Block.Eval (Safe P entry k base) (.op (.addrCopy 80 144)) entry 1 s₁ :=
    copyIndex _ _ _ hsafe (by decide) hbase
  have e₂ : Block.Eval (Safe P entry k base) (.op (.addrCopy 82 144)) s₁ 1 s₂ :=
    copyIndex _ _ _ e₁.safe_end (by decide) (by simp [s₁,hbase])
  have e₃ : Block.Eval (Safe P entry k base) (.op (.addrCopy 96 144)) s₂ 1 s₃ :=
    copyIndex _ _ _ e₂.safe_end (by decide) (by simp [s₂,s₁,hbase])
  have e₄ : Block.Eval (Safe P entry k base) (.op (.const 0 0)) s₃ 1 s₄ :=
    .op e₃.safe_end (data_safe e₃.safe_end (Or.inl (by decide : 0<2))
      (by simpa using hp 0 (Nat.zero_le _))) (fun pc => by
        change some ((s₃.atPC pc).putData 0 ((0 : ℚ) : K)) = _
        rw [Rat.cast_zero]; rfl)
  have e₅ : Block.Eval (Safe P entry k base) (.op (.const 1 1)) s₄ 1 s₅ :=
    .op e₄.safe_end (data_safe e₄.safe_end (Or.inl (by decide : 1<2))
      (by simpa using hp 1 (by omega))) (fun pc => by
        change some ((s₄.atPC pc).putData 1 ((1 : ℚ) : K)) = _
        rw [Rat.cast_one]; rfl)
  have e₆ : Block.Eval (Safe P entry k base) (.op (.store 96 0)) s₅ 1 s₆ :=
    store _ _ _ _ e₅.safe_end (by simp [s₅,s₄,s₃]) (by simp [s₅,s₄]) (by omega)
  have e₇ : Block.Eval (Safe P entry k base) (.op (.incr 96 96)) s₆ 1 s₇ :=
    incrIndex _ _ _ e₆.safe_end (by decide) (by simp [s₆,s₅,s₄,s₃])
  have e₈ : Block.Eval (Safe P entry k base) (.op (.addrCopy 98 96)) s₇ 1 s₈ :=
    copyIndex _ _ _ e₇.safe_end (by decide) (by simp [s₇])
  have e₉ : Block.Eval (Safe P entry k base) (.op (.incr 96 96)) s₈ 1 s₉ :=
    incrIndex _ _ _ e₈.safe_end (by decide) (by simp [s₈,s₇])
  have e₁₀ : Block.Eval (Safe P entry k base) (.op (.incr 99 128)) s₉ 1 s₁₀ :=
    incrIndex _ _ _ e₉.safe_end (by decide) (by simp [s₉,s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁,hk])
  have init : Block.Eval (Safe P entry k base)
      (Block.straight [.addrCopy 80 144,.addrCopy 82 144,.addrCopy 96 144,
        .const 0 0,.const 1 1,.store 96 0,.incr 96 96,.addrCopy 98 96,.incr 96 96,.incr 99 128])
      entry 10 s₁₀ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇
        (.seq e₈ (.seq e₉ (.seq e₁₀ (.skip e₁₀.safe_end))))))))))
  have hinit : Scan P entry k base 0 (s₁₀.putIndex 97 0) := by
    constructor
    · exact index_safe e₁₀.safe_end (by decide : addressScratch 97)
    · simp
    · simp [s₁₀]
    · simp [s₁₀,s₉]
    · simp [s₁₀,s₉,s₈]
    · simp [s₁₀,s₉,s₈,s₇,s₆,s₅,s₄,show 0≠base by omega]
    · simp [s₁₀,s₉,s₈,s₇,s₆,s₅,show 1≠base by omega]
    · simp [s₁₀,s₉,s₈,s₇,s₆]
    · simp
    · simp [s₁₀,s₉,s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁]
    · simp [s₁₀,s₉,s₈,s₇,s₆,s₅,s₄,s₃,s₂]
  obtain ⟨z,loop,ho⟩ := Block.Eval.forRange_invariant_exact 97 99 (k+1) 3
    (Scan P entry k base) s₁₀ init.safe_end hinit
    (fun _ _ h => ⟨h.safe,h.counter,h.limit⟩)
    (fun _ hj _ h => loop_body hlo hj h hp)
  let z₁ := z.putData (base+1) ((k+1 : ℕ) : K)
  let z₂ := z₁.putIndex 81 (k+2)
  let z₃ := z₂.putIndex 81 (k+3)
  have ex₁ : Block.Eval (Safe P entry k base) (.op (.store 98 0)) z 1 z₁ :=
    store _ _ _ _ ho.safe ho.countSlot ho.value (by omega)
  have ex₂ : Block.Eval (Safe P entry k base) (.op (.incr 81 99)) z₁ 1 z₂ :=
    incrIndex _ _ _ ex₁.safe_end (by decide) (by simp [z₁,ho.limit])
  have ex₃ : Block.Eval (Safe P entry k base) (.op (.incr 81 81)) z₂ 1 z₃ :=
    incrIndex _ _ _ ex₂.safe_end (by decide) (by simp [z₂])
  refine ⟨z₃,?_,?_⟩
  · have tail : Block.Eval (Safe P entry k base) (Block.straight
        [.store 98 0,.incr 81 99,.incr 81 81]) z 3 z₃ :=
      .seq ex₁ (.seq ex₂ (.seq ex₃ (.skip ex₃.safe_end)))
    exact (show 10+((k+1)*(3+3)+2+3) = 6*k+21 by omega) ▸ Block.Eval.seq init (.seq loop tail)
  · constructor
    · simp [z₃,z₂,z₁,ho.tag]
    · simp [z₃,z₂,z₁]
    · intro j hj
      simp [z₃,z₂,z₁,show base+2+j≠base+1 by omega,ho.prev j (by omega)]
    · simp [z₃,z₂,z₁,ho.anchor]
    · simp [z₃]
    · simp [z₃,z₂,z₁,ho.start]
    · simp [z₃,z₂,z₁,ho.slot]
      omega


omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A coordinate form of the wire layout for clients appending the column
list. Includes the empty column list case, whose header still has three words. -/
theorem Output.word {s : Memory K} {k base : ℕ} (h : Output k base s) (j : ℕ) (hj : j < k+3) :
    s.data (base+j) =
      if j=0 then 0 else if j=1 then ((k+1 : ℕ) : K) else ((j-2 : ℕ) : K) := by
  rcases j with _ | j
  · simpa using h.tag
  rcases j with _ | j
  · simpa using h.count
  · have hidx : base+(j+1+1) = base+2+j := by omega
    simpa [hidx] using h.row j (by omega)

private theorem log_mono {i j : ℕ} (h : i ≤ j) : i.log2 ≤ j.log2 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · exact Nat.le_of_lt_succ ((Nat.log2_lt hi.ne').2 (h.trans_lt Nat.lt_log2_self))

def width (H k : ℕ) : ℕ := H + 3 + (k+1).log2

theorem run_bits (entry : Memory ℚ) (k base H : ℕ) (hk : entry.index 128=k)
    (hbase : entry.index 144=base) (hlo : 256 ≤ base)
    (hm : ∀ j, ratBits (entry.data j) ≤ H) :
    ∃ n, Block.Eval (fun s => (∀ j, ratBits (s.data j) ≤ width H k) ∧ Frame entry s k base)
      block entry (6*k+21) n ∧ Output k base n := by
  apply run_block entry k base hk hbase hlo (fun x => ratBits x ≤ width H k)
  · intro j; exact (hm j).trans (by unfold width; omega)
  · intro i hi
    have h := log_mono hi
    simp [ratBits,width,show Nat.log2 1=0 by rfl]
    omega

end BorderPacketHeader
end Geometry
end LinearProgramming
end Optimization
end OAI
