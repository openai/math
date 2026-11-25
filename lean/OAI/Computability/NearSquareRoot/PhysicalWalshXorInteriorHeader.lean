import OAI.Computability.NearSquareRoot.PhysicalWalshSwapPrefix

/-! # The physical rulers of the interior Walsh XOR

A three-slot XOR keeps one leading slot inside the packed prefix and carries
all the slots after the moving window inside its payload. Its two packing
rulers are built from the original compact Walsh descriptor.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.Interior

open IntegerMultiplication Code Strip Carry Staff PhysicalWalsh Space

def L (A : ℕ) (s : Shape) := grow A (s.level-1)
def P (A W : ℕ) (s : Shape) := Nat.clog 2 (groups W s) + L A s
def B (a : ℕ) (s : Shape) := (a-3)*L (a+1) s
def S (a : ℕ) (s : Shape) := s.suff*2^(B a s)
def rows (a W : ℕ) (s : Shape) := 2^(P (a+1) W s + 3*L (a+1) s)

theorem realizes_L (A : ℕ) (hA : 1 ≤ A) : Realizes (Header.regime A) (L A) := Header.childBits A hA

theorem realizes_P (A W : ℕ) (hA : 1 ≤ A) : Realizes (Header.regime A) (P A W) :=
  (Header.groupCount A W).short_log.plus (realizes_L A hA)

/-- The three moving chunks, the fixed leading chunk, and the suffix of
remaining chunks occupy the entire positive-level Walsh grid. -/
theorem rows_mul_S {a W : ℕ} {s : Shape} (ha : 4 ≤ a) (hlevel : 0 < s.level) :
    rows a W s * S a s = SwapPrefix.paddedSize (a+1) W s := by
  have split : L (a+1) s + 3*L (a+1) s + B a s = grow (a+1) s.level := by
    have eq : a+1 = (a-3)+4 := by omega
    calc
      _ = (a+1)*L (a+1) s := by
        unfold B
        rw [show (a+1)*L (a+1) s = ((a-3)+4)*L (a+1) s from congrArg (·*L (a+1) s) eq]
        ring
      _ = grow (a+1) s.level := by
        unfold L grow
        rw [show s.level = s.level-1+1 by omega] at ⊢
        simp only [Nat.add_sub_cancel,pow_succ]; ring
  unfold rows S P SwapPrefix.paddedSize inner
  rw [← split]
  simp only [pow_add]
  ring

def header (a W : ℕ) (s : Shape) :=
  ((tally (rows a W s), tally (S a s * (2*(s.w+1)))),
    Header.wire (a+1) s, tally (rows a W s * S a s), tally (2*(s.w+1)))

/-- Manufacture the possibly large unary fields at their own length, with
all other setup polynomial in the compact node descriptor. -/
theorem mint (a W : ℕ) : Mint (Header.regime (a+1)) (header a W) := by
  have desc : (Header.regime (a+1)).Has (Header.wire (a+1)) := (Header.regime (a+1)).self
  have width : Realizes (Header.regime (a+1)) (fun s => s.w+1) := desc.ez (Easy.fst.compose (Easy.snd.compose Easy.snd))
  have hL := realizes_L (a+1) (by omega)
  have hR := (Figure.natural 2).repeated ((realizes_P (a+1) W (by omega)).plus ((Realizes.fix 3).times hL))
  have hS := (Header.suff (a+1)).multiplied ((Figure.natural 2).repeated ((Realizes.fix (a-3)).times hL))
  have bits := (Realizes.fix 2).times width
  exact ((Mint.tally hR).pair (Mint.tally (hS.multiplied (Figure.of_spoken bits)))).pair
    ((Mint.of_has desc).pair ((Mint.tally (hR.multiplied hS)).pair (Mint.of_has bits)))

private theorem hdr_bound {a W d : ℕ} {s : Shape} (ha : 4 ≤ a) (hl : 0 < s.level) :
    size (header a W s) ≤ 25*(allowance (a+1) (d+1) s+1) := by
  let q := allowance (a+1) (d+1) s
  let n := rows a W s * S a s
  have hc : n ≤ 2*count (a+1) s := (rows_mul_S ha hl).le.trans
    ((SwapPrefix.paddedSize_le (a+1) W s).trans (Nat.mul_le_mul_left _ (SwapPrefix.length_le_count ..)))
  have cap : (count (a+1) s+1)*(s.w+1) ≤ q :=
    (Nat.mul_le_mul_left _ (show s.w+1 ≤ grow (a+1) s.level+s.w+1 by omega)).trans (Nat.le_add_right ..)
  have nv : n*(s.w+1) ≤ 2*q := calc
    _ ≤ (2*count (a+1) s)*(s.w+1) := Nat.mul_le_mul_right _ hc
    _ ≤ 2*((count (a+1) s+1)*(s.w+1)) := by rw [Nat.mul_assoc]; gcongr; omega
    _ ≤ _ := Nat.mul_le_mul_left _ cap
  have rowpos : 0 < rows a W s := Nat.two_pow_pos _
  have spos : 0 < S a s := Nat.mul_pos s.suff_pos (Nat.two_pow_pos _)
  have rsmall : rows a W s ≤ n := Nat.le_mul_of_pos_right _ spos
  have ssmall : S a s ≤ n := Nat.le_mul_of_pos_left _ rowpos
  have sm := Nat.mul_le_mul_right (s.w+1) ssmall
  have nsmall : n ≤ n*(s.w+1) := Nat.le_mul_of_pos_right _ (by omega)
  have sw : s.w+1 ≤ n*(s.w+1) := Nat.le_mul_of_pos_left _ (Nat.mul_pos rowpos spos)
  have compact : size (Header.wire (a+1) s) ≤ q := by
    have hp := Nat.pow_le_pow_right (n:=Header.scale (a+1) s+1) (by omega) (show 1 ≤ d+1 by omega)
    rw [pow_one] at hp
    exact (Nat.le_add_right _ 1).trans (hp.trans (Nat.le_add_left ..))
  change size (header a W s) ≤ 25*(q+1)
  simp only [header,size_prod,size_tally,tally_length]
  simp only [size_prod,size_tally] at compact
  rw [show rows a W s * S a s = n from rfl]
  rw [Nat.mul_left_comm (S a s) 2]; omega

/-- Replace the compact header on the padded array by the packing rulers and
the interior XOR header, keeping the complete record stream intact. -/
theorem headBounded {I : Type} (a W : ℕ) (ha : 4 ≤ a) (s : I → Shape)
    (hlevel : ∀ i, 0 < (s i).level) (x : (i : I) → Data (s i)) : ∃ d,
    let b i := allowance (a+1) d (s i)
    let z i := SwapPrefix.stream (SwapPrefix.paddedSize (a+1) W (s i)) (x i)
    BoundedTask b b (fun i => send (Header.wire (a+1) (s i),z i)) (fun i => send (header a W (s i),z i)) := by
  obtain ⟨d,C,cmd⟩ := (mint a W).bounded
  refine ⟨d+1,?_⟩
  intro b z
  have hp (i : I) : C*(Header.scale (a+1) (s i)+1)^d ≤ C*b i := by
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_right (by omega) (Nat.le_succ d)).trans (Nat.le_add_left ..)
  apply ((cmd.on s).left (fun i => send (z i))).bound (C+30) (C+50)
  · intro i
    have he := hp i
    have hs := hdr_bound (d:=d) (W:=W) ha (hlevel i)
    change size (header a W (s i)) ≤ 25*(b i+1) at hs
    change C*(Header.scale (a+1) (s i)+1)^d + size (header a W (s i))+1 ≤ (C+30)*(b i+1)
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]; omega
  · intro i
    have he := hp i
    have hs := hdr_bound (d:=d) (W:=W) ha (hlevel i)
    have hz := SwapPrefix.stream_cost (a+1) W (d+1) (s i) _ (x i) le_rfl
    change size (z i) ≤ 16*b i+1 at hz
    change size (header a W (s i)) ≤ 25*(b i+1) at hs
    change C*(Header.scale (a+1) (s i)+1)^d + size (header a W (s i))+size (z i)+1 ≤ (C+50)*(b i+1)
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]; omega

end PhysicalWalshNode.Interior

end NearSquareRoot
end Computability
end OAI
