import OAI.Hierarchy.GridPinPublisherLayout
import OAI.Hierarchy.GridReceiverHeader
import OAI.Hierarchy.GridTraceCap
import OAI.Hierarchy.GridApproximationAdvice
import OAI.ThreeFlat.RAM.GuessLoop

namespace OAI
/-! # Initial external bits, self-description, compact network and parameter words -/

noncomputable section
namespace Hierarchy.GridSelfHeader
open ThreeFlat
open Diagonal RAM Computability.VPVNP Computability.VPVNP.BurstRAM PrivateRAM RAMMemory
open scoped Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {k p raw w n e B tp tr tk ep er ek ell : ℕ}
variable (X : Catalyst.Approximation F k p) (enc : FieldCode F (64*w))
variable (params : Fin n → Word (64*w))

def words (i : Fin (n+GridReceiverHeader.count w)) : Word (64*w) :=
  Fin.addCases params (GridReceiverHeader.thresholdWords w) i

def suffix (i : ℕ) : Bool :=
  if h : i<B*w^2 then GridApproximationAdvice.paddedTape X w B enc ⟨i,h⟩
  else if h : i-B*w^2<(n+GridReceiverHeader.count w)*(64*w) then
    GridReceiverHeader.wordBits (64*w) (words params) ⟨i-B*w^2,h⟩ else false

open Filter GridScale

/-- The fixed input fields and the whole original tensor port array fit
below the first workspace sector and inside the clock of the actual trace. -/
theorem raw_room_of_poly {Q : ℕ→ℕ} {D : ℕ→ℝ} (env : Envelopes Q D) (k A c coeff degree : ℕ) (hk : 0<k) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let a := overhead Q D w
      let B := pairs A w q
      ∀ n≤coeff*(w+1)^degree, let S := rawSize w (external k a B) B n
      S ≤ 2^evalDepth w k A c a q ∧ S ≤ 2^(4*w) ∧ S≤12*GridDescription.sector w ∧
        12*GridDescription.sector w+selector k w a < 2^(64*w) := by
  let C := 1500+64*coeff
  filter_upwards [controller_room env k A C (degree+2) hk,depth_range env k A c,
    budgets env k A 1 0,sublinear env (10*k+3),eventually_ge_atTop 2] with w volume depth data sub hw
  intro q pos top a B n num S
  have ctl := (volume q pos top).1
  have bpos : 1 ≤ B := Nat.le_trans (Nat.two_pow_pos _) (data q pos top).bankLo
  have gpos : 0<side a := Nat.two_pow_pos _
  have geom := Nat.le_mul_of_pos_right ((side a)^k*B) (Nat.pow_pos (Nat.succ_pos w) (n:=c))
  let fixed := (64*w)*(n+GridReceiverHeader.count w)+w^2
  have pk : fixed+w^2+2 ≤ C*(w+1)^(degree+2) := by
    have overhead := GridReceiverHeader.structural_words w coeff degree n num
    dsimp only [C,fixed]
    nlinarith only [overhead,Nat.zero_le w]
  have charge : S ≤ C*(w+1)^(degree+2)*(ticks k a q*pins w a+external k a B+B) := by
    let E := external k a B
    have pp := Nat.mul_le_mul_right B pk
    have fe := Nat.le_mul_of_pos_right fixed bpos
    have coef : 2≤C*(w+1)^(degree+2) := by omega
    have ext := Nat.mul_le_mul_right E coef
    have add := Nat.zero_le ((ticks k a q*pins w a)*(C*(w+1)^(degree+2)))
    change E*2+w^2+B*w^2+(n+GridReceiverHeader.count w)*(64*w) ≤
      C*(w+1)^(degree+2)*(ticks k a q*pins w a+E+B)
    change (64*w)*(n+GridReceiverHeader.count w)+w^2 ≤ fixed*B at fe
    nlinarith only [pp,fe,ext,add,Nat.zero_le B]
  have attained : S ≤ (side a)^k*B := charge.trans ctl
  have cutoff : S ≤ 2^evalDepth w k A c a q :=
    (attained.trans geom).trans Nat.lt_log2_self.le
  have upper : evalDepth w k A c a q ≤ w+(10*k+3)*a := (depth q pos top).2
  change (10*k+3)*a≤w at sub
  have ww : evalDepth w k A c a q ≤ 4*w := upper.trans ((Nat.add_le_add_left sub w).trans (by omega))
  have small := cutoff.trans (Nat.pow_le_pow_right (by decide : 0<2) ww)
  have lo := GridDescription.small_before_sector (by omega : 0<w)
  have big := GridDescription.sectors_fit (by omega : 1≤w)
  have selectorBound : selector k w a ≤ 2^(4*w) :=
    Nat.pow_le_pow_right (by decide) (show w-(10*k+24)*a≤4*w by omega)
  exact ⟨cutoff,small,by omega,by omega⟩

theorem raw_room_of_linear {Q : ℕ→ℕ} {D : ℕ→ℝ} (env : Envelopes Q D) (k A c coeff : ℕ) (hk : 0<k) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let a := overhead Q D w
      let B := pairs A w q
      ∀ n≤coeff*(w+1), let S := rawSize w (external k a B) B n
      S ≤ 2^evalDepth w k A c a q ∧ S ≤ 2^(4*w) ∧ S≤12*GridDescription.sector w ∧
        12*GridDescription.sector w+selector k w a < 2^(64*w) := by
  simpa only [pow_one] using raw_room_of_poly env k A c coeff 1 hk

theorem raw_room {Q : ℕ→ℕ} {D : ℕ→ℝ} (env : Envelopes Q D) (k A c n : ℕ) (hk : 0<k) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let a := overhead Q D w
      let B := pairs A w q
      let S := rawSize w (external k a B) B n
      S ≤ 2^evalDepth w k A c a q ∧ S ≤ 2^(4*w) ∧ S≤12*GridDescription.sector w ∧
        12*GridDescription.sector w+selector k w a < 2^(64*w) := by
  filter_upwards [raw_room_of_linear env k A c n hk] with w room
  intro q qp qt
  exact room q qp qt n (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

variable (recv : Machine (64*w) tp tr tk) (eval : Machine (64*w) ep er ek)
variable (x : Fin (e*2) → Bool)

def rawTape : ℕ→Bool :=
  GridDescription.input x (GridDescription.code (q:=w^2) recv eval) (suffix (B:=B) X enc params)

def captured (start : ℕ) (s : Fin ell → Bool) : Memory (64*w) :=
  GuessLoop.install start s (initialMemory (rawSize w e B n)
    (fun j => TraceBitHeader.binaryWord (64*w) (rawTape (B:=B) X enc params recv eval x j)))

theorem input_at {start : ℕ} (sep : rawSize w e B n ≤ start) (s : Fin ell → Bool)
    (i : Fin (rawSize w e B n)) :
    captured (B:=B) X enc params recv eval x start s i.val =
      ((rawTape (B:=B) X enc params recv eval x i.val).toNat : Word (64*w)) := by
  have low : ¬ (start ≤ i.val ∧ i.val < start + ell) := fun h => (Nat.not_le_of_lt (i.isLt.trans_le sep)) h.1
  simp only [captured,GuessLoop.install,dite_eq_right low,initialMemory,ite_eq_left i.isLt]
  cases rawTape (B:=B) X enc params recv eval x i.val <;> rfl

theorem external_at {start : ℕ} (sep : rawSize w e B n ≤ start)
    (s : Fin ell → Bool) (i : Fin (e*2)) :
    captured (B:=B) X enc params recv eval x start s i.val = ((x i).toNat : Word (64*w)) := by
  have atAddr := input_at X enc params recv eval x sep s
    ⟨i.val,by have := i.isLt; unfold rawSize; omega⟩
  simpa only [rawTape,GridDescription.pair_at] using atAddr

theorem compact_at {start : ℕ} (sep : rawSize w e B n ≤ start)
    (s : Fin ell → Bool) (i : Fin (B*w^2)) :
    captured (B:=B) X enc params recv eval x start s (e*2+w^2+i.val) =
      ((GridApproximationAdvice.paddedTape X w B enc i).toNat : Word (64*w)) := by
  have atAddr := input_at X enc params recv eval x sep s
    ⟨e*2+w^2+i.val,by have := i.isLt; unfold rawSize; omega⟩
  simpa [rawTape,GridDescription.fixed_at,suffix,i.isLt] using atAddr

theorem operand_at {start : ℕ} (sep : rawSize w e B n ≤ start) (s : Fin ell → Bool)
    (i : Fin ((n+GridReceiverHeader.count w)*(64*w))) :
    captured (B:=B) X enc params recv eval x start s (e*2+w^2+(B*w^2+i.val)) =
      ((GridReceiverHeader.wordBits (64*w) (words params) i).toNat : Word (64*w)) := by
  have atAddr := input_at X enc params recv eval x sep s
    ⟨e*2+w^2+(B*w^2+i.val),by have := i.isLt; unfold rawSize; omega⟩
  simpa [rawTape,GridDescription.fixed_at,suffix,i.isLt] using atAddr

/-- The very first deterministic phase of the native evaluator consumes the
advice beginning at the true source address on the captured self-description tape. -/
theorem loader {start : ℕ} (large : 768≤w) (positive : 0<B) (size : rawSize w e B n≤2^(4*w))
    (sep : rawSize w e B n ≤ start) (s : Fin ell → Bool) :
    let dst := 2*GridDescription.sector w
    let m := captured (B:=B) X enc params recv eval x start s
    (GridApproximationAdvice.loader w B (e*2+w^2) dst).Spec
      (·=m) (fun _ out => out=GridApproximationAdvice.paddedMemory X enc B dst m) (4000*(w*B)) := by
  intro dst m
  have low := GridDescription.small_before_sector (by omega : 0<w)
  have top := GridDescription.sectors_fit (by omega : 1≤w)
  have len := (GridApproximationAdvice.padded_clock w B large positive).1
  have word : 12*B≤(64*w)*(12*B) := Nat.le_mul_of_pos_left _ (by omega)
  have cap : e*2+w^2+B*w^2≤2^(4*w) := (Nat.le_add_right _ _).trans size
  intro p r K M pc reg pub exit install pubAt c mem enter equal
  subst mem
  exact GridApproximationAdvice.loader_spec X enc large positive (dst:=dst) (src:=e*2+w^2)
    (.inr (by dsimp [dst];omega)) (by dsimp [dst];omega) (by omega)
    M pc reg pub exit install pubAt c m enter (compact_at X enc params recv eval x sep s)

end Hierarchy.GridSelfHeader
end

end OAI
