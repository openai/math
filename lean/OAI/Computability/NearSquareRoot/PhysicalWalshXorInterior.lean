import OAI.Computability.NearSquareRoot.PhysicalWalshXorInteriorHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshXorInteriorBuffer
import OAI.Computability.NearSquareRoot.PhysicalWalshXorDusk
import OAI.Computability.NearSquareRoot.PhysicalWalshXorThreshold

/-! # The canonical interior Walsh XOR on one physical lane

The outer prefix is extended to a dyadic interval and the trailing fields
are packed with the full nonbinary suffix. The resulting three-slot XOR
is run on the complete bit tapes before the padded groups are cropped.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.Interior

open IntegerMultiplication Code Space PhysicalWalsh SwapPrefix XorThreshold

def volume (a W : ℕ) (s : Shape) := paddedSize (a+1) W s * (2*(s.w+1))

noncomputable def extra (a W : ℕ) (ρ : ℝ) (s : Shape) := gateClock ρ (L (a+1) s) (volume a W s)

theorem volume_bound (a W d : ℕ) (s : Shape) : volume a W s ≤ 4*allowance (a+1) d s := by
  have h := (paddedSize_le (a+1) W s).trans (Nat.mul_le_mul_left _ (length_le_count ..))
  have hm := Nat.mul_le_mul_right (2*(s.w+1)) h
  have hc : (count (a+1) s+1)*(s.w+1) ≤ allowance (a+1) d s :=
    (Nat.mul_le_mul_left _ (show s.w+1 ≤ grow (a+1) s.level+s.w+1 by omega)).trans (Nat.le_add_right ..)
  unfold volume; ring_nf at hc hm ⊢; omega

theorem volume_eq (a W : ℕ) (ha : 4 ≤ a) (s : Shape) (hl : 0 < s.level) :
    XorReserve.volume (P (a+1) W s) (3*L (a+1) s) (B a s) (s.suff*(2*(s.w+1))) = volume a W s := by
  rw [volume, ← rows_mul_S (W:=W) ha hl]
  unfold XorReserve.volume rows S
  rw [pow_add]; ring

/-- An XOR only changes its active address. In particular the source row of
any real prefix group belongs to the original, unpadded stream. -/
theorem xorIndex_bound {a W : ℕ} (s : Shape) (positive : 0<s.level)
    (g : Fin (a+1) × Fin (a+1)) (n : ℕ) :
    xorIndex a g s n < length (a+1) W s ↔ n < length (a+1) W s := by
  let h := (a+1)^(s.level-1)
  let M := 2^((a+1)*(2*h))
  have dim := Header.grid_width W a s positive
  change (a+1)*(2*h)=grow (a+1) s.level at dim
  have span : length (a+1) W s = groups W s*M*s.suff := by
    unfold length inner M; rw [dim,Nat.mul_assoc]
  let y := KernelScaleLayout.rank (KernelPass.xorColumn g ∘ KernelScaleLayout.coord a h s.suff n)
  have small : y.val < M := y.isLt
  have mp : 0<M := Nat.two_pow_pos _
  have div_digit {d x j : ℕ} (hj : j<d) : (x*d+j)/d = x := by
    rw [Nat.mul_comm x d,Nat.mul_add_div (Nat.zero_lt_of_lt hj),Nat.div_eq_of_lt hj,Nat.add_zero]
  have keep : xorIndex a g s n / s.suff / M = n/s.suff/M := by
    change ((n/s.suff/M*M+y.val)*s.suff+n%s.suff)/s.suff/M = _
    rw [div_digit (Nat.mod_lt _ s.suff_pos),div_digit small]
  rw [span,← Nat.div_lt_iff_lt_mul s.suff_pos,← Nat.div_lt_iff_lt_mul mp,keep,
    Nat.div_lt_iff_lt_mul mp,Nat.div_lt_iff_lt_mul s.suff_pos]

def axes (a : ℕ) (ha : 4 ≤ a) : Fin (a+1) × Fin (a+1) := (⟨2,by omega⟩,⟨1,by omega⟩)

theorem actual_output (a W : ℕ) (ha : 4 ≤ a) (s : Shape) (hl : 0<s.level) (x : Data s) :
    laneFlat (a+1) W s (extend (a+1) W s x ∘ XorSweep.directedRead (L (a+1) s) (S a s)) =
      laneFlat (a+1) W s (xor a (axes a ha) s x) := by
  apply List.map_congr_left
  intro n hn
  have small : n < length (a+1) W s := List.mem_range.mp hn
  have e : xorIndex a (axes a ha) s n = XorSweep.directedRead (L (a+1) s) (S a s) n :=
    XorSweep.xorIndex_interior (by omega) s n
  simp only [Function.comp_apply,← e,xor,extend,ite_eq_left ((xorIndex_bound s hl (axes a ha) n).mpr small)]

/-- Calls whose available low bits cover the compiled table degree. -/
abbrev Large (a W D : ℕ) := {u : XorInput W // cutoff D (Header.scale (a+1) u.shape) ≤ L (a+1) u.shape}

/-- A fixed program for every large interior call. Its input is the real
Walsh descriptor and one flat lane, and its output uses the node's exact
slot-index permutation. -/
theorem large {ρ : ℝ} (lower : 1/2 < ρ) (upper : ρ ≤ 1) (a W : ℕ) (arity : 4 ≤ a) :
    ∃ D d : ℕ,
      let s (u : Large a W D) := u.val.shape
      BoundedTask (fun u => allowance (a+1) d (s u)+extra a W ρ (s u))
        (allowance (a+1) d ∘ s)
        (fun u => send (Header.wire (a+1) (s u),laneFlat (a+1) W (s u) u.val.row))
        (fun u => send (laneFlat (a+1) W (s u) (xor a (axes a arity) (s u) u.val.row))) := by
  let A := a+1
  obtain ⟨D,template⟩ := XorWindow.boundedDuskOn lower (P A W) (L A) (S a) Shape.w
    (realizes_P A W (by dsimp [A];omega)) (realizes_L A (by dsimp [A];omega))
  let s (u : Large a W D) := u.val.shape
  let x (u : Large a W D) := u.val.row
  let b (u : Large a W D) := B a (s u)
  let m (u : Large a W D) := (s u).suff*(2*((s u).w+1))
  let q (u : Large a W D) := Header.scale A (s u)
  let price (u : Large a W D) := factor ρ (L A (s u))
  let z (u : Large a W D) := extend A W (s u) (x u)
  let y (u : Large a W D) := z u ∘ XorSweep.directedRead (L A (s u)) (S a (s u))
  have low (u : Large a W D) : Controlled.payloadBits D (q u) ≤ b u := by
    simpa only [b,B,show a+1-4=a-3 by omega] using
      (payload_le_suffix (A:=a+1) (by omega) u.property)
  have native := template s b m q price
    (fun u => by change ((s u).suff*2^(b u)) * (2*((s u).w+1)) = 2^(b u)*m u; dsimp only [m]; ring)
    (fun _ => le_rfl) (fun u => Nat.mul_pos (s u).suff_pos (by omega))
    low (fun u => factor_pays ρ (L A) (s u))
    (fun u => factor_le_prefix upper u.property (Nat.le_add_left ..)) z
  have physical : BoundedTask (fun u => extra a W ρ (s u)) (fun u => volume a W (s u))
      (fun u => send (header a W (s u),stream (paddedSize A W (s u)) (z u)))
      (fun u => send (stream (paddedSize A W (s u)) (y u))) := by
    have dim (u : Large a W D) := rows_mul_S (W:=W) arity u.val.positive
    have vol (u : Large a W D) := volume_eq a W arity (s u) u.val.positive
    apply native.conform
    · intro u
      change (4+3*Controlled.guardWidth (3*L A (s u)))*
        (XorReserve.volume (P A W (s u)) (3*L A (s u)) (B a (s u)) (m u)*(price u+1))+1=_
      rw [show XorReserve.volume (P A W (s u)) (3*L A (s u)) (B a (s u)) (m u)=volume a W (s u) from vol u]
      rfl
    · exact vol
    · intro u
      change Tree.fork (send (header a W (s u))) (send (stream (rows a W (s u)*S a (s u)) (z u))) = _
      rw [show rows a W (s u)*S a (s u)=paddedSize A W (s u) from dim u]; rfl
    · intro u
      change send (stream (rows a W (s u)*S a (s u)) (y u)) = _
      rw [show rows a W (s u)*S a (s u)=paddedSize A W (s u) from dim u]
  obtain ⟨d,head⟩ := headBounded a W arity s (fun u => u.val.positive) z
  have middle := physical.bound (time':=fun u => extra a W ρ (s u)) (space':=allowance A d ∘ s) 1 4
    (fun _ => by simp) (fun u => by
      have h := volume_bound a W d (s u)
      change volume a W (s u)+1 ≤ 4*(allowance (a+1) d (s u)+1)
      omega)
  have both := head.compose middle
  obtain ⟨e,assembled⟩ := realLane A W s x y (fun u => extra a W ρ (s u)) (d:=d)
    (both.mono (fun _ => le_rfl) (fun _ => max_le le_rfl le_rfl))
  refine ⟨D,e,assembled.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_⟩
  intro u; exact congrArg send (actual_output a W arity (s u) u.val.positive (x u))

end PhysicalWalshNode.Interior

end NearSquareRoot
end Computability
end OAI
