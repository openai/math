import OAI.Hierarchy.TaggedRadixFormats

namespace OAI
/-! # Volume bounds for the physical radix-pass ledger -/

noncomputable section
namespace Hierarchy.Tagged.Radix

/-- Width cost per row of the comparison and port checks in a stable sort. -/
theorem sort_shell_width_cost (u a d w : ℕ) :
    u*((a+a+w)+(a+d+1)+(a+d+2)*176+28*w) + 28*(u*(a+w)+(u*a+u*(a+w))) ≤
      1024*u*(a+d+w+1) := by
  ring_nf
  omega

/-- Width cost per row of the alignment checks and their oracle ports. -/
theorem align_shell_width_cost (u j t d w : ℕ) :
    14000000000*u*(d+j+t+3)+u*(j+t)+28*(u*w+(u*(j+t)+u*w)) ≤
      15000000000*u*(d+(j+t)+w+3) := by
  ring_nf
  omega

/-- The resource ledger of the three kernels and the three rectangular adapters.
`ell` is the common height of both local banks. -/
theorem PassShape.ledger_cost (s : PassShape) {ell h c w sort align wide : ℕ}
    (pos : 1 ≤ w)
    (localVolume : s.blocks*2^ell ≤ 8*2^h)
    (wideVolume : 2^s.globalHeight*s.pack ≤ 8*2^h) (lastVolume : s.nextRows ≤ 4*2^h)
    (hd : s.digitBits ≤ c*h) (hl : ell ≤ c*h) (hg : s.globalHeight ≤ c*h) (hw : w ≤ c*h)
    (ls : sort ≤ 1024*2^ell*(ell+(s.digitBits+1)+w+1))
    (la : align ≤ 15000000000*2^ell*(s.digitBits+ell+w+3))
    (ws : wide ≤ 1024*2^s.globalHeight*(s.globalHeight+(s.digitBits+1)+s.pack*w+1)) :
    s.blocks*sort + s.blocks*align + wide + 4*(s.blocks*2^ell*w) +
      3*(2^s.globalHeight*s.pack*w) + 2*(s.nextRows*w) ≤ (1000000000000*c)*2^h*h := by
  let P := c*h
  let L := s.blocks*2^ell
  let W := 2^s.globalHeight*s.pack
  have one : 1 ≤ P := pos.trans hw
  change ell ≤ P at hl
  change s.digitBits ≤ P at hd
  change s.globalHeight ≤ P at hg
  change w ≤ P at hw
  have localWord : ell + (s.digitBits+1) + w + 1 ≤ 5*P := by omega
  have alignWord : s.digitBits + ell + w + 3 ≤ 6*P := by omega
  have packPos : 0 < s.pack := Nat.two_pow_pos _
  have small : P ≤ s.pack*P := Nat.le_mul_of_pos_left _ packPos
  have packed : s.pack*w ≤ s.pack*P := Nat.mul_le_mul_left _ hw
  have wideWord : s.globalHeight + (s.digitBits+1) + s.pack*w + 1 ≤ 5*(s.pack*P) := by omega
  have localSort : s.blocks*sort ≤ 40960*2^h*P := calc
    _ ≤ s.blocks*(1024*2^ell*(ell+(s.digitBits+1)+w+1)) :=
      Nat.mul_le_mul_left _ ls
    _ = (1024*L)*(ell+(s.digitBits+1)+w+1) := by dsimp [L]; ring
    _ ≤ (1024*(8*2^h))*(5*P) := Nat.mul_le_mul (Nat.mul_le_mul_left _ localVolume) localWord
    _ = _ := by ring
  have localAlign : s.blocks*align ≤ 720000000000*2^h*P := calc
    _ ≤ s.blocks*(15000000000*2^ell*(s.digitBits+ell+w+3)) :=
      Nat.mul_le_mul_left _ la
    _ = (15000000000*L)*(s.digitBits+ell+w+3) := by dsimp [L]; ring
    _ ≤ (15000000000*(8*2^h))*(6*P) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ localVolume) alignWord
    _ = _ := by ring
  have globalSort : wide ≤ 40960*2^h*P := calc
    _ ≤ 1024*2^s.globalHeight*(s.globalHeight+(s.digitBits+1)+s.pack*w+1) :=
      ws
    _ ≤ 1024*2^s.globalHeight*(5*(s.pack*P)) := Nat.mul_le_mul_left _ wideWord
    _ = (5120*W)*P := by dsimp [W]; ring
    _ ≤ (5120*(8*2^h))*P := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ wideVolume)
    _ = _ := by ring
  have lbits : L*w ≤ (8*2^h)*P := Nat.mul_le_mul localVolume hw
  have wbits : W*w ≤ (8*2^h)*P := Nat.mul_le_mul wideVolume hw
  have obits : s.nextRows*w ≤ (4*2^h)*P := Nat.mul_le_mul lastVolume hw
  change s.blocks*sort + s.blocks*align + wide + 4*(L*w) + 3*(W*w) + 2*(s.nextRows*w) ≤ _
  calc
    _ ≤ 40960*2^h*P + 720000000000*2^h*P + 40960*2^h*P +
        4*((8*2^h)*P) + 3*((8*2^h)*P) + 2*((4*2^h)*P) := by omega
    _ = 720000081984 * 2^h * P := by ring
    _ ≤ 1000000000000 * 2^h * P :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
    _ = _ := by dsimp [P]; ring


/-- The rounding and padding of each scheduled pass fit the three physical
volume caps and the common linear height cap. -/
theorem GridScales.pass_network_resources {a B : ℝ} {h n c ell : ℕ} (g : GridScales a B h)
    (two : 2 ≤ h) (count : n+1 ≤ 2^(passBits h)) (i : ℕ)
    (height : ell = packBits B h + (2*digitBits a h+1-packBits B h)) :
    let s := passShapeAt a B h n i
    s.blocks*2^ell ≤ 8*2^h ∧ 2^s.globalHeight*s.pack ≤ 8*2^h ∧ s.nextRows ≤ 4*2^h ∧
    s.digitBits ≤ (c+2)*h ∧ ell ≤ (c+2)*h ∧ s.globalHeight ≤ (c+2)*h := by
  let s := passShapeAt a B h n i
  change s.blocks*2^ell ≤ 8*2^h ∧ 2^s.globalHeight*s.pack ≤ 8*2^h ∧ s.nextRows ≤ 4*2^h ∧
    s.digitBits ≤ (c+2)*h ∧ ell ≤ (c+2)*h ∧ s.globalHeight ≤ (c+2)*h
  have digits := g.digit_room
  have last := g.last_room
  have endRoom : passBits h+2*digitBits a h+2 ≤ h+1 := by omega
  have before := slotSequence_bounds count digits endRoom (min i n) (by omega)
  have after := slotSequence_bounds count digits endRoom (min i n+1) (by omega)
  change 2^(h+1) ≤ s.rows ∧ s.rows ≤ 2*2^(h+1) at before
  change 2^(h+1) ≤ s.nextRows ∧ s.nextRows ≤ 2*2^(h+1) at after
  rw [pow_succ] at before after
  have room : s.packBits ≤ 2*s.digitBits := by change packBits B h ≤ 2*digitBits a h; omega
  have hp : 0 < s.rows := by have := Nat.two_pow_pos h; omega
  have within : s.packBits ≤ h := by change packBits B h ≤ h; omega
  have bounds := s.global_height room within (h:=h) (by omega) (by omega)
  have tagSize : ell = 2*s.digitBits+1 := by
    change ell = 2*digitBits a h+1
    omega
  have kl : 2*s.digitBits+1 ≤ h := by change 2*digitBits a h+1 ≤ h; omega
  have lv := s.local_volume
  rw [←tagSize] at lv
  have wv := (s.global_volume room hp).2
  have factor : 2*h ≤ (c+2)*h := by rw [Nat.add_mul]; omega
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

end Hierarchy.Tagged.Radix

end
end OAI
