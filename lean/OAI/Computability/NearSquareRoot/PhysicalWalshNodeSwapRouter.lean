import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSwapBits
import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryPrefix

/-! # Assembling physical interchanges of whole Walsh slots -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.Route
open IntegerMultiplication Code Space PhysicalWalsh KernelScaleLayout XorBits SwapWord Staff

/-- Replacing a row operation by an everywhere equal function preserves its
single physical command and both resource bounds. -/
theorem FlatRun.congr {W a : ℕ} {T S : Shape → ℕ} {F G : (s : Shape) → Data s → Data s}
    (p : FlatRun (W:=W) a T S F) (eq : ∀ s x,F s x = G s x) : FlatRun (W:=W) a T S G := by
  simpa only [show F=G from funext fun s => funext (eq s)] using p

/-- The trailing `cut` bits stay outside the rectangular swap and can be
moved by a logarithmic number of two-bit scans. -/
def lowerSwap {a : ℕ} (cut : Shape → ℕ) (i j : Fin (a+1)) (s : Shape) (x : Data s) : Data s :=
  let L := grow (a+1) (s.level-1)
  x ∘ stride s (SwapWord.run (offset L i) (offset L j) (cut s))

def upperSwap {a : ℕ} (cut : Shape → ℕ) (i j : Fin (a+1)) (s : Shape) (x : Data s) : Data s :=
  let L := grow (a+1) (s.level-1)
  x ∘ stride s (SwapWord.run (offset L i+cut s) (offset L j+cut s) (L-cut s))

/-- Axis ordering does not depend on the recursive width of a slot. -/
theorem apart_of_gt {a : ℕ} {i j : Fin (a+1)} (h : j < i) (L : ℕ) : offset L i + L ≤ offset L j := by
  unfold offset
  rw [← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ (by change j.val < i.val at h; omega)

theorem lowerRun (a W : ℕ) (cut : Shape → ℕ) (known : Realizes (Header.regime (a+1)) cut)
    (cap : ∀ s, cut s ≤ grow (a+1) (s.level-1)) : ∃ D : ℕ, ∀ d, D ≤ d → ∀ i j : Fin (a+1), j < i →
    FlatRun (W:=W) a (nodeScan a W d (ElementarySweep.prefixExtra (a+1) cut)) (nodeArena a W d) (lowerSwap cut i j) := by
  obtain ⟨D,p⟩ := ElementarySweep.prefixRun a W cut known cap
  refine ⟨D,fun d hd i j ji => ?_⟩
  have h₁ := p d hd i j (ne_of_gt ji)
  have h₂ := p d hd j i (ne_of_lt ji)
  let T := nodeScan a W d (ElementarySweep.prefixExtra (a+1) cut)
  have cost (s : Shape) : nodeArena a W d s ≤ T s := Nat.le_add_right ..
  have fit (s : Shape) : PhysicalWalshContext.routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ nodeArena a W d s := le_max_right ..
  apply ((h₁.chain cost fit h₂).chain cost fit h₁).congr
  intro s x
  funext n
  let L := grow (a+1) (s.level-1)
  let lo := offset L i
  let hi := offset L j
  change x (stride s (window lo hi (cut s)) (stride s (window hi lo (cut s)) (stride s (window lo hi (cut s)) n))) = _
  rw [stride_comp,stride_comp]
  apply congrArg x
  exact congrArg (fun f => stride s f n) (funext fun q => three_xor lo hi _ q ((Nat.add_le_add_left (cap s) lo).trans (apart_of_gt ji L)))

/-- Combining the short lower swap and one packed upper swap exchanges the
complete slots at every physical ordinal. -/
theorem lower_upper {a : ℕ} (cut : Shape → ℕ) (cap : ∀ s,cut s ≤ grow (a+1) (s.level-1))
    (i j : Fin (a+1)) (ji : j < i) (s : Shape) (x : Data s) :
    upperSwap cut i j s (lowerSwap cut i j s x) = axisSwap i j s x := by
  funext n
  let L := grow (a+1) (s.level-1)
  let lo := offset L i
  let hi := offset L j
  change x (stride s (SwapWord.run lo hi (cut s)) (stride s (SwapWord.run (lo+cut s) (hi+cut s) (L-cut s)) n)) = x (key s (axes _) n)
  rw [stride_comp,key_swap i j (ne_of_gt ji) s n (apart_of_gt ji L)]
  apply congrArg x
  exact congrArg (fun f => stride s f n) (funext fun q => SwapWord.split lo hi L (cut s) q (apart_of_gt ji L) (cap s))

theorem axisSwap_self {a : ℕ} (i : Fin (a+1)) (s : Shape) (x : Data s) : axisSwap i i s x = x := by
  funext n
  rw [axisSwap,Equiv.swap_self]
  let h := (a+1)^(s.level-1)
  let M := 2^((a+1)*(2*h))
  let r : Fin M := ⟨n/s.suff%M,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  change x ((n/s.suff/M*M+(rank (address a h r)).val)*s.suff+n%s.suff) = x n
  rw [rank_address]
  change x ((n/s.suff/M*M+n/s.suff%M)*s.suff+n%s.suff) = x n
  rw [Nat.div_add_mod',Nat.div_add_mod']

/-- A coincident-axis swap only drops the descriptor. -/
theorem identityRun (a W d : ℕ) (extra : Shape → ℕ) (i : Fin (a+1)) :
    FlatRun (W:=W) a (nodeScan a W d extra) (nodeArena a W d) (axisSwap i i) := by
  let S := nodeArena a W d
  let m : Meter Shape := ⟨S,S,fun _ => le_rfl,fun _ _ _ _ => True⟩
  have size := PhysicalWalshContext.fitsLayout (m:=m) (coords a W) Shape.w (Header.wire (a+1)) (fun s => le_max_right ..)
  let input := fun t : XorInput W => (Header.wire (a+1) t.shape,laneFlat (a+1) W t.shape t.row)
  have op := PhysicalWalshGrid.easyWithin (fun t : XorInput W => S t.shape) Easy.snd input 3 (fun t => by
    have hH := size.header t.shape
    change Code.size (PhysicalWalshGrid.header (coords a W) Shape.w t.shape)+Code.size (Header.wire (a+1) t.shape)+1 ≤ S t.shape at hH
    have hR := size.row t.shape t.row
    change Code.size (((coords a W).rows t.shape).map (Dusk.mark ∘ t.row)) ≤ S t.shape at hR
    rw [coords_range _ _ _ t.positive] at hR
    change Code.size (Header.wire (a+1) t.shape)+Code.size ((List.range _).map (Dusk.mark ∘ t.row))+1 ≤ 3*(S t.shape+1)
    omega)
  unfold FlatRun
  simp only [axisSwap_self]
  exact op.mono (fun _ => Nat.le_add_right ..) (fun _ => le_rfl)

/-- Supply physical upper-field rectangle passes only for strictly ordered
slots. The lower bits, reverse ordering and coincident slots use fixed scans. -/
theorem wholeSwaps (a W : ℕ) (cut extra : Shape → ℕ) (known : Realizes (Header.regime (a+1)) cut)
    (cap : ∀ s, cut s ≤ grow (a+1) (s.level-1)) (clock : ∀ s, ElementarySweep.prefixExtra (a+1) cut s ≤ extra s)
    (upper : ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ i j : Fin (a+1), j < i →
      FlatRun (W:=W) a (nodeScan a W d extra) (nodeArena a W d) (upperSwap cut i j)) :
    ∃ D : ℕ, ∀ d, D ≤ d → ∀ i j : Fin (a+1),
      FlatRun (W:=W) a (nodeScan a W d extra) (nodeArena a W d) (axisSwap i j) := by
  obtain ⟨e,hr⟩ := lowerRun a W cut known cap
  obtain ⟨f,hr'⟩ := upper
  refine ⟨max e f,fun d hd i j => ?_⟩
  have ordered (i j : Fin (a+1)) (ji : j < i) : FlatRun (W:=W) a (nodeScan a W d extra) (nodeArena a W d) (axisSwap i j) := by
    have lower := hr d ((le_max_left ..).trans hd) i j ji
    have widen : FlatRun (W:=W) a (nodeScan a W d extra) (nodeArena a W d) (lowerSwap cut i j) := lower.mono
      (fun t => Nat.add_le_add_left (clock t.shape) _) (fun _ => le_rfl)
    exact (widen.chain (fun _ => Nat.le_add_right ..) (fun _ => le_max_right ..)
      (hr' d ((le_max_right ..).trans hd) i j ji)).congr (lower_upper cut cap i j ji)
  rcases lt_trichotomy j i with lt|eq|gt
  · exact ordered i j lt
  · subst j; exact identityRun a W d extra i
  · apply (ordered j i gt).congr
    intro s x;unfold axisSwap;rw [Equiv.swap_comm j i]

end PhysicalWalshNode.Route

end NearSquareRoot
end Computability
end OAI
