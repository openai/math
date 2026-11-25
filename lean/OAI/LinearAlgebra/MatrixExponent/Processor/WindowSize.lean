import OAI.LinearAlgebra.MatrixExponent.Processor.Handle
import OAI.LinearAlgebra.MatrixExponent.Processor.DispatchSize
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Broadcast

section
/-! # Finite size estimates before the working width is chosen -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Diagonal Controller
variable {F : Type} [Field F] [Fintype F] {N l d B n r h C : ℕ}

theorem Bank.data_le_budget (M : Bank (Fin n)) (F : Type) [Field F] [Fintype F] :
    Fintype.card M.Data ≤ M.budget F := by
  simp only [Bank.Data, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, Bank.budget]
  apply Finset.sum_le_sum
  intro i _
  have : 0 < templateCost F := by unfold templateCost; positivity
  exact (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ this)).trans
    (Nat.le_mul_of_pos_right _ (by positivity))

namespace Window

theorem position_card (n r a h : ℕ) :
    Fintype.card (Position n r a h) = (r ^ n) ^ 2 * 2 ^ n * h * a := by
  simp [Position, Packet, Template, Label, Spectral.Cube]
  ring

theorem position_bound (hp : (r ^ n) ^ 2 * 2 ^ n * h ≤ C * N * d) :
    Fintype.card (Position n r (rounds n r h (12 * (C * N * d))) h) ≤ 13 * C * N * d := by
  let M := (r ^ n) ^ 2 * 2 ^ n * h
  rw [position_card]
  have he : rounds n r h (12 * (C * N * d)) = 12 * (C * N * d) / M + 1 := by
    simp [rounds, Label, Spectral.Cube, M]
  rw [he]
  change M * (12 * (C * N * d) / M + 1) ≤ _
  rw [mul_add, mul_one]
  exact (Nat.add_le_add (Nat.mul_div_le _ _) hp).trans_eq (by ring)

variable (P : Format N l d n r h)

theorem total_positions (hpos : Fintype.card (Position n r P.count h) ≤ 13 * C * N * d)
    (hB : B * d ≤ 4 * r) : Fintype.card (Position n r (B * P.count) h) ≤ 52 * C * N * r := by
  calc
    _ = B * Fintype.card (Position n r P.count h) := by rw [position_card, position_card]; ring
    _ ≤ B * (13 * C * N * d) := Nat.mul_le_mul_left _ hpos
    _ = 13 * C * N * (B * d) := by ring
    _ ≤ 13 * C * N * (4 * r) := Nat.mul_le_mul_left _ hB
    _ = _ := by ring

variable (hp : Fintype.card (Position n r (B * P.count) h) ≤ 52 * C * N * r)

include hp in
theorem packet_bound (hh : 0 < h) : Fintype.card (Packet n r (B * P.count)) ≤ 52 * C * N * r := by
  refine le_trans ?_ hp
  rw [Fintype.card_prod (Packet n r (B * P.count))]
  have : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  exact Nat.le_mul_of_pos_right _ Fintype.card_pos

include hp in
theorem rows_bound (hh : 0 < h) (hr : 0 < r) : r ^ 2 * packetRows P B ≤ 52 * C * N := by
  apply Nat.le_of_mul_le_mul_right _ hr
  calc
    _ = (PacketKernel.templates n r * r ^ 3) * (B * P.count) := by unfold packetRows; ring
    _ ≤ (r ^ n) ^ 2 * (B * P.count) := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    _ = Fintype.card (Packet n r (B * P.count)) := by simp [Packet, Template, Label, pow_two]
    _ ≤ _ := packet_bound P hp hh

include hp in
theorem guess_bound (hl : l ≤ N) (hr : 0 < r) :
    Fintype.card (XIn P B) ≤ (16 + 104 * C) * N := by
  have hs : Fintype.card (SlotKey.Domain n r (B * P.count) h) ≤ 104 * C * N := by
    apply Nat.le_of_mul_le_mul_right _ hr
    calc
      _ = (Fintype.card (SlotKey n r) / r * r) * (B * P.count * h) := by
        simp only [SlotKey.Domain, Fintype.card_prod, Fintype.card_fin, SlotKey.count]
        ring
      _ ≤ Fintype.card (SlotKey n r) * (B * P.count * h) := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
      _ = 2 * Fintype.card (Position n r (B * P.count) h) := by
        simp only [SlotKey, Position, Packet, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        ring
      _ ≤ 2 * (52 * C * N * r) := Nat.mul_le_mul_left _ hp
      _ = _ := by ring
  have hi : Fintype.card (PinIndex.Domain N l r) ≤ l + 12 * N := by
    simp only [PinIndex.Domain, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [show 4 * N / r * (3 * r) = 3 * (4 * N / r * r) by ring]
    have := Nat.div_mul_le_self (4 * N) r
    omega
  rw [Fintype.card_sum, Fintype.card_sum (α := PinIndex.Domain N l r), add_mul]
  have ht : Fintype.card (Machine.Ports N l l) ≤ 3 * N := by simp [Machine.Ports]; omega
  omega

end Window
end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-!
# A single working width at each sufficiently large scale

The number of lanes exceeds the length of the processor by a
polylogarithmic factor. Packet slots and private bits are counted
per worker, before any diagram is chosen.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Diagonal Controller Filter
variable {F : Type} [Field F] [Fintype F] {N l d B n r h C Q w W : ℕ}

private theorem rough_keys (hn : 2 ≤ n) (hr : 1 ≤ r) (hp : r ^ (16 * n) ≤ N) :
    3 * r * Fintype.card (Name n r) ≤ 9 * (6 + 2 * 2 ^ n) * N ∧
    Fintype.card (Query n r) ≤ 9 * (6 + 2 * 2 ^ n) * N := by
  let T := (r ^ n) ^ 2
  have ht (j : ℕ) (hj : j ≤ n * 2) : r ^ j ≤ T := by
    unfold T; rw [← pow_mul]
    exact Nat.pow_le_pow_right hr hj
  have h₁ : r * r ^ n ≤ T := by rw [← pow_succ']; exact ht _ (by omega)
  have h₂ : r ^ n ≤ T := ht _ (by omega)
  have h₃ : r ^ 3 ≤ T := ht _ (by omega)
  have h₄ : 1 ≤ T := ht 0 (by omega)
  have h₅ : r ^ 2 * T ≤ N := by
    unfold T
    rw [← pow_mul, ← pow_add]
    exact (Nat.pow_le_pow_right hr (by omega)).trans hp
  have ha : Fintype.card (Name n r) + 1 ≤ (6 + 2 * 2 ^ n) * T := by
    rw [name_card]
    change 3 * r * r ^ n + r ^ n + T * 2 ^ n * 2 + r ^ 3 + 1 ≤ _
    nlinarith only [h₁, h₂, h₃, h₄]
  have hb : (3 * r) * (3 * r) * (Fintype.card (Name n r) + 1) ≤ 9 * (6 + 2 * 2 ^ n) * N := by
    calc
      _ ≤ (3 * r) * (3 * r) * ((6 + 2 * 2 ^ n) * T) := Nat.mul_le_mul_left _ ha
      _ = 9 * (6 + 2 * 2 ^ n) * (r ^ 2 * T) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h₅
  constructor
  · exact (Nat.mul_le_mul (Nat.le_mul_of_pos_right _ (by omega)) (Nat.le_succ _)).trans hb
  · rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_option, Fintype.card_fin, ← mul_assoc]
    exact hb

private def threshold (A : Expansion F n h) (C : ℕ) :=
  100000000 + 3 * n + 9 * (6 + 2 * 2 ^ n) + (16 + 104 * C) +
  PacketKernel.rate A + PacketKernel.batchRate A + 512 * PacketKernel.rowSize A +
  36 * Fintype.card A.I + 15 * PacketKernel.frameRate A * (52 * C + 1) +
  2 * PacketKernel.rowSize A * (52 * C + 1)

private theorem finite_window (P : Format N l d n r h) (A : Expansion F n h) (hn : 2 ≤ n)
    (M : Bank (Fin n)) (S : Controller P A hn M B) (hh : 0 < h)
    (hN : N = 2 ^ w) (hr : 3 ≤ r) (hp : r ^ (16 * n) ≤ N) (hl : l ≤ N)
    (hpos : Fintype.card (Position n r P.count h) ≤ 13 * C * N * d) (hB : B * d ≤ 4 * r)
    (hM : M.budget F ≤ N * w ^ Q) (hT : threshold A C ≤ w)
    (hW : w ≤ W) (hs : W ≤ 2 * w) (hu : 2 ^ W ≤ N * w ^ (Q + 10)) (hd : N * w ^ (Q + 4) ≤ 2 ^ W) :
    Window P A M B C Q w W := by
  unfold threshold at hT
  have hw : 100000000 ≤ w := by omega
  have hNr : 0 < N := by rw [hN]; positivity
  have hNw : w < N := by rw [hN]; exact Nat.lt_two_pow_self
  have hr' : 0 < r := by omega
  have hpow (j : ℕ) (hj : j ≤ 16 * n) : r ^ j ≤ N := (Nat.pow_le_pow_right hr' hj).trans hp
  have hrN : r ≤ N := by simpa using hpow 1 (by omega)
  have hr₂ := hpow 2 (by omega)
  have hr₃ := hpow 3 (by omega)
  have spaces (k : ℕ) (hk : k < Q + 4) : N * w ^ k < 2 ^ W :=
    (Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by omega) hk) hNr).trans_le hd
  have hcap : N * w < 2 ^ W := by simpa using spaces 1 (by omega)
  have constant (k : ℕ) (hk : k ≤ w) : k * N ≤ 2 ^ W :=
    (Nat.mul_le_mul_right N hk).trans (by rw [mul_comm]; exact hcap.le)
  have hNV : N ≤ 2 ^ W := by simpa using constant 1 (by omega)
  have htot := Window.total_positions P hpos hB
  have hpack := Window.packet_bound P htot hh
  have hrow := Window.rows_bound P htot hh hr'
  have hrow' : r ^ 2 * (1 + packetRows P B) ≤ (52 * C + 1) * N := by rw [mul_add, add_mul]; omega
  have hpack' : Fintype.card (Packet n r (B * P.count)) < N ^ 3 := by
    apply hpack.trans_lt
    calc
      _ ≤ 52 * C * N * N := Nat.mul_le_mul_left _ hrN
      _ < N * N * N := by gcongr; omega
      _ = _ := by ring
  have hcnt : countWidth P B ≤ 3 * w := by
    apply Nat.clog_le_of_le_pow
    rw [mul_comm 3, pow_mul, ← hN]
    exact hpack'
  have hc : 9 * Fintype.card (A.CountBit r (B * P.count)) ≤ 2 ^ W := by
    rw [Fintype.card_prod, Fintype.card_prod (Class r) A.I, Fintype.card_fin,
      show Fintype.card (Class r) = r ^ 3 by simp [Class]; ring]
    calc
      _ ≤ 9 * (N * Fintype.card A.I * (3 * w)) := by gcongr
      _ = (27 * Fintype.card A.I) * N * w := by ring
      _ ≤ w * N * w := by gcongr; omega
      _ ≤ _ := by rw [show w * N * w = N * w ^ 2 by ring]; exact (spaces 2 (by omega)).le
  have hkeys := rough_keys hn (by omega) hp
  have hkey := constant (9 * (6 + 2 * 2 ^ n)) (by omega)
  refine ⟨hs, hu, ?_, hr, constant _ (by omega), hkeys.1.trans hkey, hc, ?_, ?_, ?_, ?_, ?_, ?_,
    by omega, hpos⟩
  · refine ⟨by omega, by omega, hNV, hr', hp.trans hNV, ?_, by omega, ?_, ?_, hkeys.2.trans hkey,
      by omega⟩
    · rw [mul_pow]
      exact (Nat.mul_le_mul_left _ (hpow 5 (by omega))).trans (constant _ (by omega))
    · intro i z
      have hz : A.cross z i ≤ PacketKernel.reserve A := PacketKernel.width_le A z i true
      unfold Expansion.chargeBits PacketKernel.rowSize PacketKernel.prefixSize at *
      omega
    · exact hpack'.trans_le ((Nat.pow_le_pow_left hNV 3).trans
        (Nat.pow_le_pow_right (by positivity) (by decide)))
  · have hsl : 1 + packetRows P B ≤ (52 * C + 1) * N :=
      (Nat.le_mul_of_pos_left _ (by positivity)).trans hrow'
    calc
      _ ≤ 2 * ((packetRows P B + 1) * PacketKernel.rowSize A) := (PacketKernel.height_bounds A _).2
      _ ≤ 2 * (((52 * C + 1) * N) * PacketKernel.rowSize A) := by gcongr; omega
      _ = N * (2 * PacketKernel.rowSize A * (52 * C + 1)) := by ring
      _ ≤ N * w := by gcongr; omega
      _ < _ := hcap
  · rw [Fintype.card_prod, PacketKernel.card_spot]
    calc
      _ ≤ 3 * r ^ 2 * (PacketKernel.frameRate A * (1 + packetRows P B) * (1 + countWidth P B)) :=
        Nat.mul_le_mul_left _ (PacketKernel.frame_width A)
      _ = 3 * PacketKernel.frameRate A * (r ^ 2 * (1 + packetRows P B)) * (1 + countWidth P B) := by ring
      _ ≤ 3 * PacketKernel.frameRate A * ((52 * C + 1) * N) * (5 * w) := by gcongr; omega
      _ = (15 * PacketKernel.frameRate A * (52 * C + 1)) * N * w := by ring
      _ ≤ w * N * w := by gcongr; omega
      _ ≤ _ := by rw [show w * N * w = N * w ^ 2 by ring]; exact (spaces 2 (by omega)).le
  · exact (Window.guess_bound P htot hl hr').trans (constant _ (by omega))
  · exact (M.data_le_budget F).trans (hM.trans (spaces Q (by omega)).le)
  · have := S.literal
    omega
  · rw [mul_right_comm]
    exact (Nat.mul_le_mul_left _ hrN).trans (constant _ (by omega))

theorem window (n h C Q : ℕ) (hn : 2 ≤ n) (hh : 0 < h) (hC : 4 ≤ C)
    (A : Expansion F n h) :
    ∀ᶠ w : ℕ in atTop,
      let N := 2 ^ w
      let r := 2 ^ (w / (16 * n))
      let d := 2 ^ (w / (32 * n))
      let l := N / 2048
      let B := (3 * r + d - 1) / d
      ∀ fa : Machine.Ports N l l → Label n r,
        let P := Format.prescribed d h (rounds n r h (12 * (C * N * d))) fa
        ∀ M : Bank (Fin n), M.budget F ≤ N * w ^ Q → Nonempty (Controller P A hn M B) →
          ∃ W, Window P A M B C Q w W := by
  obtain ⟨δ, _, hs⟩ := Diagonal.scales C n h (Fintype.card A.I) hC hn
  filter_upwards [hs, eventually_ge_atTop (threshold A C), eventually_ge_atTop (32 * n),
    poly_bound (Q + 4) 1 (by decide)] with w hs hT hw he
  intro N r d l B fa P M hM hS
  obtain ⟨hd, hd', _⟩ := batch_floor w n
  have sc : Scales C n h (Fintype.card A.I) N r l l d 0 B :=
    hs.2 d 0 hd hd' (by simp)
  have hr : 3 ≤ r := by
    have h₁ : 2 ≤ w / (16 * n) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    exact (show 3 ≤ 2 ^ 2 by decide).trans (Nat.pow_le_pow_right (by decide) h₁)
  have hp : r ^ (16 * n) ≤ N := by
    unfold r N
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self w (16 * n))
  have hw' : 2 ≤ w := by omega
  let j := Nat.clog 2 (w ^ (Q + 4))
  have hj : j ≤ w := Nat.clog_le_of_le_pow (by simpa only [Nat.div_one] using he)
  have hlog := Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (w ^ (Q + 4))).le
  have hhigh : 2 ^ j ≤ w ^ (Q + 10) := calc
    _ ≤ 2 ^ (Nat.log 2 (w ^ (Q + 4)) + 1) := Nat.pow_le_pow_right (by decide) hlog
    _ ≤ w ^ (Q + 4) * w := by rw [pow_succ]; exact Nat.mul_le_mul (Nat.pow_log_le_self _ (by positivity)) hw'
    _ ≤ _ := by rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨w + j, finite_window P A hn M hS.some hh rfl hr hp (Nat.div_le_self _ _)
    (Window.position_bound sc.padding) sc.copies hM hT (by omega) (by omega) ?_ ?_⟩
  · rw [pow_add]; exact Nat.mul_le_mul_left N hhigh
  · rw [pow_add (2 : ℕ)]; exact Nat.mul_le_mul_left N (Nat.le_pow_clog (by decide) _)

end OAI.LinearAlgebra.MatrixExponent.Processor
end
