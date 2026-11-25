import OAI.ThreeFlat.Diagonal.TraceAddressRecord
import OAI.ThreeFlat.RAM.TraceWordBound
import Mathlib.Data.Nat.Choose.Bounds

namespace OAI
/-! # Word capacity of the physical-port address records

The base and interval endpoints can scale with the row count. Each stride is
bounded by a polynomial in the public row description. The XOR displacement
only changes bits in the row index.
-/

namespace ThreeFlat.Diagonal.TraceAddressRecord

open Computability.VPVNP RAM.BitLayout TracePhysical TraceUniformRow

/-- Public space per row for all alternatives of the local address record. -/
def portRowWords (w p r k d : ℕ) : ℕ :=
  2 + w + (5+r)*(w+1) + 7*(w+1) + RAMLayout.layerCount d * (7*(w+1)) + (1+6*p+k)*w

/-- A single polynomial bounds the displayed row expression, uniformly for
all local register, instruction and constant counts below the same envelope. -/
theorem portRowWords_polynomial {w p r k d c e : ℕ} (hd : d ≤ w)
    (hp : p ≤ c*(w+1)^e) (hr : r ≤ c*(w+1)^e) (hk : k ≤ c*(w+1)^e) :
    portRowWords w p r k d ≤ 64*(c+1)*(w+1)^(e+3) := by
  let X := w+1
  let T := X^(e+3)
  have x_pos : 0 < X := Nat.succ_pos _
  have ht : 0 < T := Nat.pow_pos x_pos
  have mono (i : ℕ) (hi : i ≤ e+3) : X^i ≤ T := Nat.pow_le_pow_right x_pos hi
  have hx : X ≤ T := by simpa using mono 1 (by omega)
  have hw : w ≤ T := (Nat.le_succ _).trans hx
  have grow {n : ℕ} (hn : n ≤ c*X^e) : n*X ≤ c*T := calc
    _ ≤ (c*X^e)*X := Nat.mul_le_mul_right _ hn
    _ = c*X^(e+1) := by rw [pow_succ, mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (mono _ (by omega))
  have rc := grow hr
  have rp := grow hp
  have rk := grow hk
  have cpu : (5+r)*X ≤ 5*T+c*T := by rw [Nat.add_mul]; omega
  have textWidth : (1+6*p+k)*w ≤ T+7*(c*T) := by
    apply le_trans (Nat.mul_le_mul_left _ (Nat.le_succ w))
    change (1+6*p+k)*X ≤ _
    rw [show (1+6*p+k)*X = X+6*(p*X)+k*X by ring]
    omega
  have lc : RAMLayout.layerCount d ≤ X^2 := (Nat.choose_le_pow (d+1) 2).trans
    (Nat.pow_le_pow_left (Nat.succ_le_succ hd) 2)
  have wire : RAMLayout.layerCount d * (7*X) ≤ 7*T := calc
    _ ≤ X^2*(7*X) := Nat.mul_le_mul_right _ lc
    _ = 7*X^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (mono _ (by omega))
  change 2+w+(5+r)*X+7*X+RAMLayout.layerCount d*(7*X)+(1+6*p+k)*w ≤ 64*(c+1)*T
  rw [show 64*(c+1)*T = 64*(c*T)+64*T by ring]
  omega

private def fixedTerms (R : Record) : ℕ := R.testBias+R.lo+R.hi+R.base+R.sub+R.bit.getD 0

private def slopeTerms (R : Record) : ℕ := R.testStride+R.stride

private structure HeaderBound (R : Record) (D B : ℕ) : Prop where
  mask : R.mask < D
  fixed : fixedTerms R ≤ 20*(D*B)
  slope : slopeTerms R ≤ 20*B

private theorem ordinary_bound {w p r k d S f : ℕ} (hw : 2 ≤ w+1)
    (time : S+f ≤ 2^(1+d)) (z : TracePhysical.Port w r d) :
    HeaderBound (ordinary hw S f z) (2^d) (portRowWords w p r k d) := by
  let D := 2^d
  let C := (5+r)*(w+1)
  let J := 7*(w+1)
  let L := RAMLayout.layerCount d
  let B := portRowWords w p r k d
  have dp : 0 < D := Nat.two_pow_pos d
  have b2 : 2 ≤ B := by dsimp [B, portRowWords]; omega
  have bw : w ≤ B := by dsimp [B, portRowWords]; omega
  have bc : C ≤ B := by dsimp [B, C, portRowWords]; omega
  have bj : J ≤ B := by dsimp [B,J,portRowWords]; omega
  have bl : L*J ≤ B := by dsimp [B,L,J,portRowWords]; omega
  have bd : B ≤ D*B := Nat.le_mul_of_pos_left _ dp
  have dd : D ≤ D*B := Nat.le_mul_of_pos_right _ (by omega)
  have ts : S+f ≤ 2*D := by simpa [D,pow_add] using time
  have hmul (x y : ℕ) (hx : x ≤ 2*D) (hy : y ≤ B) :
      x*y ≤ 2*(D*B) := by simpa only [mul_assoc] using Nat.mul_le_mul hx hy
  have sw := hmul S w (by omega) bw
  have fc := hmul f C (by omega) bc
  have cs : C*S ≤ 2*(D*B) := by simpa [mul_comm] using hmul S C (by omega) bc
  have layers : L*(D*(2*J)) ≤ 2*(D*B) := by
    calc
      L*(D*(2*J)) = 2*(D*(L*J)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ bl)
  rcases z with ⟨c,j⟩ | ⟨s,j⟩ | ⟨l,own,s,j⟩ | ⟨out,j⟩
  · have hj : j.val ≤ C := j.isLt.le
    have hcc : C*c.val ≤ 2*B := by
      rw [mul_comm 2 B]
      exact Nat.mul_le_mul bc (by have := c.isLt; omega)
    constructor
    · exact dp
    · change c.val+S+(S+f)+(2+S*w+j.val+C*c.val)+C*S+0 ≤ 20*(D*B)
      have := c.isLt
      omega
    · change 2+2*C ≤ 20*B
      omega
  · have hj := j.isLt
    have hs := s.isLt
    have hws : w*s.val ≤ B := by
      calc
        w*s.val ≤ w*1 := Nat.mul_le_mul_left _ (by omega)
        _ ≤ _ := by simpa using bw
    constructor
    · exact dp
    · change s.val+0+S+(2+j.val+w*s.val)+0+0 ≤ 20*(D*B)
      omega
    · change 2+2*w ≤ 20*B
      omega
  · have hj : j.val ≤ J := j.isLt.le
    have hsj : J*s.val ≤ B := by
      calc
        J*s.val ≤ J*1 := Nat.mul_le_mul_left _ (by have := s.isLt; omega)
        _ ≤ _ := by simpa using bj
    have hl : D*(2*J)*l.val ≤ 2*(D*B) := by
      apply le_trans _ layers
      rw [mul_comm _ l.val]
      exact Nat.mul_le_mul_right _ l.isLt.le
    constructor
    · change (if own then 0 else 2^((RAMLayout.layerEquiv d).symm l).siteBit) < 2^d
      split
      · exact dp
      · exact Nat.pow_lt_pow_right (by decide) ((RAMLayout.layerEquiv d).symm l).siteBit_lt
    · change 0+0+1+(2+S*w+f*C+j.val+J*s.val+D*(2*J)*l.val)+0+0 ≤ 20*(D*B)
      omega
    · change 0+2*J ≤ 20*B
      omega
  · have hj : j.val ≤ J := j.isLt.le
    cases out <;> constructor
    · exact dp
    · change 0+1+D+(2+S*w+f*C+L*(D*(2*J))+j.val)+J+0 ≤ 20*(D*B)
      omega
    · change 1+J ≤ 20*B
      omega
    · exact dp
    · change 0+0+(D-1)+(2+S*w+f*C+L*(D*(2*J))+j.val)+0+0 ≤ 20*(D*B)
      omega
    · change 1+J ≤ 20*B
      omega

private theorem port_bound {w p r k d S f : ℕ} (hw : 2 ≤ w+1) (time : S+f ≤ 2^(1+d))
    (z : TraceUniformRow.Port w p r k d) :
    HeaderBound (portRecord hw S f z) (2^d) (portRowWords w p r k d) := by
  rcases z with z | ⟨future,j⟩
  · exact ordinary_bound hw time z
  let D := 2^d
  let C := (5+r)*(w+1)
  let J := 7*(w+1)
  let L := RAMLayout.layerCount d
  let T := (1+6*p+k)*w
  let B := portRowWords w p r k d
  have dp : 0 < D := Nat.two_pow_pos _
  have b2 : 2 ≤ B := by dsimp [B,portRowWords]; omega
  have bw : w ≤ B := by dsimp [B,portRowWords]; omega
  have bc : C ≤ B := by dsimp [B,C,portRowWords]; omega
  have bj : J ≤ B := by dsimp [B,J,portRowWords]; omega
  have bl : L*J ≤ B := by dsimp [B,L,J,portRowWords]; omega
  have bt : T ≤ B := by dsimp [B,T,portRowWords]; omega
  have bd : B ≤ D*B := Nat.le_mul_of_pos_left _ dp
  have dd : D ≤ D*B := Nat.le_mul_of_pos_right _ (by omega)
  have ts : S+f ≤ 2*D := by simpa [D,pow_add] using time
  have sw : S*w ≤ 2*(D*B) := by simpa [mul_assoc] using Nat.mul_le_mul (by omega : S ≤ 2*D) bw
  have fc : f*C ≤ 2*(D*B) := by simpa [mul_assoc] using Nat.mul_le_mul (by omega : f ≤ 2*D) bc
  have layers : L*(D*(2*J)) ≤ 2*(D*B) := by
    calc
      L*(D*(2*J)) = 2*(D*(L*J)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ bl)
  have last : (D-1)*J ≤ D*B := Nat.mul_le_mul (Nat.sub_le _ _) bj
  have space : Fintype.card (Shared w r f d) ≤ 5*(D*B) := by
    rw [← sharedCount_card]
    change f*C+(L*(D*(2*J))+(D-1)*J) ≤ 5*(D*B)
    omega
  have hj : (finProdFinEquiv j).val ≤ T := (finProdFinEquiv j).isLt.le
  cases future <;> constructor
  · exact dp
  · change 0+0+1+(2+S*w+Fintype.card (Shared w r f d)+(finProdFinEquiv j).val)+0+0 ≤ 20*(D*B)
    omega
  · change 0+T ≤ 20*B
    omega
  · exact dp
  · change 0+0+(D-1)+(2+S*w+Fintype.card (Shared w r f d)+(finProdFinEquiv j).val+T)+0+0 ≤ 20*(D*B)
    omega
  · change 1+T ≤ 20*B
    omega

/-- Numerical word capacity suffices for every physical port at any word width. -/
theorem portRecord_fits_of_capacity {W d p r k S f : ℕ} (hw : 2 ≤ W+1)
    (time : S+f ≤ 2^(1+d)) (cap : 40*(2^d * portRowWords W p r k d) < 2^W)
    (v : Fin (2^d)) (z : TraceUniformRow.Port W p r k d) :
    (portRecord hw S f z).Fits W v.val := by
  let R := portRecord hw S f z
  let D := 2^d
  let B := portRowWords W p r k d
  have hb : HeaderBound R D B := port_bound hw time z
  have bpos : 0 < B := by dsimp [B,portRowWords]; omega
  have Dpos : 0 < D := Nat.two_pow_pos _
  change 40*(D*B) < 2^W at cap
  have field := hb.fixed
  have stride := hb.slope
  unfold fixedTerms at field
  unfold slopeTerms at stride
  have small : D ≤ D*B := Nat.le_mul_of_pos_right _ bpos
  have vm : v.val < D := v.isLt
  have mask := hb.mask
  have first : R.testStride*v.val ≤ 20*(D*B) := by
    have h := Nat.mul_le_mul (show R.testStride ≤ 20*B by omega) vm.le
    calc
      _ ≤ (20*B)*D := h
      _ = _ := by ring
  have second : R.stride*(v.val ^^^ R.mask) ≤ 20*(D*B) := by
    have h := Nat.mul_le_mul (show R.stride ≤ 20*B by omega) (Nat.xor_lt_two_pow vm mask).le
    calc
      _ ≤ (20*B)*D := h
      _ = _ := by ring
  change R.Fits W v.val
  constructor <;> first | (unfold Record.test; omega) | (unfold Record.numerator; omega) | omega

/-- The eight preconditions used by native instruction selection hold for
every row and every concrete port, including both branches of each guard. -/
theorem portRecord_fits_word {u d p r k S f c e : ℕ} (hw : 2 ≤ 16*u^10+1)
    (time : S+f ≤ 2^(1+d)) (hu : RAM.traceWordThreshold (40*c) e ≤ u) (hd : d ≤ 15*u^10)
    (hrow : portRowWords (16*u^10) p r k d ≤ c*(16*u^10+1)^e)
    (v : Fin (2^d)) (z : TraceUniformRow.Port (16*u^10) p r k d) :
    (portRecord hw S f z).Fits (16*u^10) v.val := by
  apply portRecord_fits_of_capacity hw time _ v z
  exact RAM.trace_word_address_lt (control := 0) hu hd hrow (Nat.zero_le _) (by simp)

/-- The relocation subtraction also fits whenever the physical row budget fits. -/
theorem portRecord_add_sub_lt_of_capacity {W d p r k S f : ℕ} (hw : 2 ≤ W+1)
    (time : S+f ≤ 2^(1+d)) (cap : 40*(2^d * portRowWords W p r k d) < 2^W)
    (z : TraceUniformRow.Port W p r k d) :
    (portRecord hw S f z).sub + (S*W-S) < 2^W := by
  let D := 2^d
  let B := portRowWords W p r k d
  have hb : W ≤ B := by dsimp [B,portRowWords]; omega
  have ts : S+f ≤ 2*D := by simpa [D,pow_add] using time
  have sw : S*W ≤ 2*(D*B) := by simpa [mul_assoc] using Nat.mul_le_mul (by omega : S ≤ 2*D) hb
  have fixed := (port_bound hw time z).fixed
  change fixedTerms (portRecord hw S f z) ≤ 20*(D*B) at fixed
  unfold fixedTerms at fixed
  change 40*(D*B) < 2^W at cap
  change (portRecord hw S f z).sub + (S*W-S) < 2^W
  omega

/-- Relocating shared cells after removal of the unused header bits adds
`S*W-S` to the preexisting saturating subtraction. This larger word also fits. -/
theorem portRecord_add_sub_lt {u d p r k S f c e : ℕ} (hw : 2 ≤ 16*u^10+1)
    (time : S+f ≤ 2^(1+d)) (hu : RAM.traceWordThreshold (40*c) e ≤ u) (hd : d ≤ 15*u^10)
    (hrow : portRowWords (16*u^10) p r k d ≤ c*(16*u^10+1)^e)
    (z : TraceUniformRow.Port (16*u^10) p r k d) :
    (portRecord hw S f z).sub + (S*(16*u^10)-S) < 2^(16*u^10) := by
  apply portRecord_add_sub_lt_of_capacity hw time _ z
  exact RAM.trace_word_address_lt (control := 0) hu hd hrow (Nat.zero_le _) (by simp)

/-- A fixed bound on the public program parameters suffices uniformly for
all ports and rows at every sufficiently large native word size. -/
theorem portRecord_fits_of_public_bounds {u d p r k S f c e : ℕ} (hw : 2 ≤ 16*u^10+1)
    (time : S+f ≤ 2^(1+d)) (hu : RAM.traceWordThreshold (40*(64*(c+1))) (e+3) ≤ u)
    (hd : d ≤ 15*u^10) (hp : p ≤ c*(16*u^10+1)^e)
    (hr : r ≤ c*(16*u^10+1)^e) (hk : k ≤ c*(16*u^10+1)^e)
    (v : Fin (2^d)) (z : TraceUniformRow.Port (16*u^10) p r k d) :
    (portRecord hw S f z).Fits (16*u^10) v.val :=
  portRecord_fits_word hw time hu hd (portRowWords_polynomial (by omega) hp hr hk) v z

end ThreeFlat.Diagonal.TraceAddressRecord

end OAI
