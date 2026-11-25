import OAI.Computability.NearSquareRoot.CRTControlledBenesSplit
import OAI.Computability.IntegerMultiplication.Param.Base

/-! # Encoded sizes for the local routing-table compiler

A complete table on a `d`-bit block contains at most `2^d` rows, each with two `d`-bit
words. This charges the unary width argument and both words of every row in the P192
encoding. A polynomial-time compiler on those encodings has polynomial time in the global
address width whenever the block occupies logarithmically many positions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes
open IntegerMultiplication IntegerMultiplication.Code

theorem rawTable_size_bound (d : ℕ) (t : RawTable)
    (hr : ∀ row ∈ t, row.1.length ≤ d ∧ row.2.length ≤ d) :
    size t ≤ t.length * (4*d+4) + 1 := by
  induction t with
  | nil => simp
  | cons row t ih =>
    have h := hr row (by simp)
    have ht := ih fun q hq => hr q (List.mem_cons_of_mem _ hq)
    simp only [size_cons, size_prod, Bits.size_word, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem rawInput_size_bound (d : ℕ) (t : RawTable) (ht : t.length ≤ 2^d)
    (hr : ∀ row ∈ t, row.1.length ≤ d ∧ row.2.length ≤ d) :
    size (tally d,t) ≤ 6*(2^d+1)^2 := by
  have hb := rawTable_size_bound d t hr
  have hd : d ≤ 2^d := d.lt_two_pow_self.le
  have hm := Nat.mul_le_mul ht (show 4*d+4 ≤ 4*2^d+4 by omega)
  simp only [size_prod,size_tally,tally_length]
  nlinarith

/-- Charge a uniform compiler on the represented width and the full input table. -/
theorem rawCompiler_ports {I Y : Type*} [Codec Y] (d : I → ℕ) (t : I → RawTable)
    (ht : ∀ i, (t i).length ≤ 2^(d i))
    (hr : ∀ i, ∀ row ∈ t i, row.1.length ≤ d i ∧ row.2.length ≤ d i)
    {F : Tally × RawTable → Y} (hF : Poly F) :
    Task.BT (fun i => 2^(d i)) (fun i => send (tally (d i),t i))
      (fun i => send (F (tally (d i),t i))) :=
  hF.on ⟨2,6,fun i => rawInput_size_bound _ _ (ht i) (hr i)⟩

theorem blockPorts_poly {I : Type*} (d k : I → ℕ) (C : ℕ)
    (hd : ∀ i, d i ≤ C * Nat.clog 2 (2*k i)) : Dom k (fun i => 2^(d i)) := by
  refine ⟨C, 4^C, fun i => ?_⟩
  calc
    2^(d i) ≤ 2^(C * Nat.clog 2 (2*k i)) := Nat.pow_le_pow_right (by decide) (hd i)
    _ = (2^Nat.clog 2 (2*k i))^C := by rw [Nat.mul_comm C, pow_mul]
    _ ≤ (4*(k i+1))^C :=
      Nat.pow_le_pow_left (by have := Param.logBound (2*k i); omega) _
    _ = _ := Nat.mul_pow ..

/-- Compile every local table with one physical program when the block widths and the
external control settings vary. The exponent of the polynomial may depend on `C`. -/
theorem rawCompiler_param {I Y : Type*} [Codec Y] (d k : I → ℕ) (t : I → RawTable) (C : ℕ)
    (hd : ∀ i, d i ≤ C * Nat.clog 2 (2*k i)) (ht : ∀ i, (t i).length ≤ 2^(d i))
    (hr : ∀ i, ∀ row ∈ t i, row.1.length ≤ d i ∧ row.2.length ≤ d i)
    {F : Tally × RawTable → Y} (hF : Poly F) :
    Task.BT k (fun i => send (tally (d i),t i)) (fun i => send (F (tally (d i),t i))) :=
  (rawCompiler_ports d t ht hr hF).mono (blockPorts_poly d k C hd)

/-- The routing invariant supplies both input-size hypotheses, in every enumeration order. -/
theorem represented_bounds {d : ℕ} {p : Equiv.Perm (Word d)} {t : RawTable}
    (h : RawRepresents p t) : t.length = 2^d ∧
      ∀ row ∈ t, row.1.length = d ∧ row.2.length = d := by
  classical
  obtain ⟨ks,hn,ha,rfl⟩ := h
  have hall : ks.toFinset = Finset.univ := by ext x; simp [ha]
  constructor
  · rw [List.length_map, ← List.toFinset_card_of_nodup hn, hall]
    simp [Word]
  · intro row hrow
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hrow
    simp

/-- Apply the polynomial-time compiler directly on any correct local permutation table. -/
theorem representedCompiler_param {I Y : Type*} [Codec Y] (d k : I → ℕ) (t : I → RawTable)
    (p : (i : I) → Equiv.Perm (Word (d i))) (C : ℕ)
    (hd : ∀ i, d i ≤ C * Nat.clog 2 (2*k i)) (ht : ∀ i, RawRepresents (p i) (t i))
    {F : Tally × RawTable → Y} (hF : Poly F) :
    Task.BT k (fun i => send (tally (d i),t i)) (fun i => send (F (tally (d i),t i))) := by
  refine rawCompiler_param d k t C hd (fun i => (represented_bounds (ht i)).1.le) ?_ hF
  intro i row hrow
  obtain ⟨hi,ho⟩ := (represented_bounds (ht i)).2 row hrow
  exact ⟨hi.le,ho.le⟩

end Benes

end NearSquareRoot
end Computability
end OAI
