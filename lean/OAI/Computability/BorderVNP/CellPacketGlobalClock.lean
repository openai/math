import OAI.Computability.BorderVNP.CellPacketPhysical
import OAI.Computability.BorderVNP.CellPacketBitWidth

/-! # Transporting global binary identifiers in the physical private-cell call

A global row identifier or pointer may have magnitude polynomial in the batch size.
Only its binary width enters this estimate. Locally expanded wire addresses and repetition
counts retain the separate per-cell numeric bounds used by the validator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet

/-- A scalar transported in a machine word has at most the word's width in digits.
The fixed packet tags require two digits even at a smaller machine width. -/
theorem words_width (D : Directory) (p w : ℕ) (h : RawFields D p (2^w-1)) :
    ∀ v ∈ words D p, v.size ≤ max w 2 := by
  intro v hv
  rw [Nat.size_le]
  apply (words_bounded D p h _ hv).trans_lt
  apply max_lt_iff.mpr
  have hw := Nat.pow_le_pow_right (show 0 < 2 by decide) (le_max_left w 2)
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by decide) (le_max_right w 2)
  have hp := pow_pos (show 0 < (2:ℕ) by decide) w
  norm_num at h2
  omega

end CellSparse.Packet

namespace RoutingISA.CompactPacket

open Filter TeamScales CellSparse CellMacro CellMacro.Generator RationalHitting.StackLanguage

private theorem regroup (a x l : ℕ) : a*(3*x*l) = 3*a*(x*l) := by ring

/-- The word and step allowances with arbitrary global scalars in the packed input.
Their binary widths, and the measured original-packet translation time, may grow with
the batch word width. -/
theorem eventually_global_clock (A B j : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r M E w p t : ℕ, 1 ≤ r →
      (r:ℝ) ≤ 2^((n:ℝ)^ω) → M ≤ width n (1/5) → E ≤ width n (1/4) → 0 < w → w ≤ n →
      ∀ (D : Directory) (ext : List Bool), ext.length ≤ E →
      D.StaticBounds A M → D.CompactFields p (4*(M+E+1)^3) →
      D.records.length ≤ 4*(M+E+1)^3 → D.reportedCounts.length ≤ 4*(M+E+1)^3 →
      Packet.storedMass D ≤ A*(M+1)^2 → (∀ v ∈ Packet.words D p, v.size ≤ B*(logWidth r n+1)^j) →
      t ≤ B*(M+E+1)^96*(logWidth r n+1)^j →
      (CompactFrame.pack w (Packet.input D p ext)).length ≤ width n (1/2) ∧
      let s := D.program p
      let ops := (CompactMachine.withExternal ext s).expand []
      2*(3*((CompactFrame.pack w (Packet.input D p ext)).length*w)+
        generationCost 8 (Packet.bits D p) ext s t + (2*(stream ops).length+1) + budget ops) ≤ n^25 := by
  let P := (8*A+4)*(4*B+4)+1
  let C := B+42*P+34
  obtain ⟨ω,hω,room⟩ := eventually_compiled_load_log A C j
  refine ⟨ω,hω,?_⟩
  filter_upwards [room] with n hn
  intro r M E w p t hr hrω hM hE hw hwn D ext he st hf hc hg hstore hwidth ht
  let X := M+E+1
  let Y := (M+1)^2+E+1
  let L := (logWidth r n+1)^j
  have hL : 1 ≤ L := Nat.one_le_pow _ _ (by omega)
  have hY : (M+1)^2 ≤ Y := by dsimp [Y]; omega
  have hExt : 1+ext.length ≤ Y*L := (show 1+ext.length ≤ Y by dsimp [Y]; omega).trans
    (Nat.le_mul_of_pos_right _ hL)
  have hbits := Packet.input_length_from_static D p ext st hstore hwidth
  have hwide : 4*(B*L)+4 ≤ (4*B+4)*L := by rw [Nat.add_mul,Nat.mul_assoc]; omega
  have hproduct : (8*A+4)*(M+1)^2*(4*(B*L)+4) ≤ ((8*A+4)*(4*B+4))*(Y*L) := by
    calc _ ≤ (8*A+4)*Y*((4*B+4)*L) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hY) hwide
         _ = _ := by rw [Nat.mul_mul_mul_comm]
  have hpay : (Packet.input D p ext).length ≤ P*(Y*L) := by
    rw [show P*(Y*L) = ((8*A+4)*(4*B+4))*(Y*L)+Y*L from Nat.succ_mul ..]
    change _ ≤ (8*A+4)*(M+1)^2*(4*(B*L)+4)+1+ext.length at hbits
    omega
  have metaLen : (Packet.bits D p).length ≤ (Packet.input D p ext).length := by
    simp [Packet.input,codeWord_length]; omega
  let T := X^96*L
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hx96 : X ≤ X^96 := by simpa only [pow_one] using Nat.pow_le_pow_right hx (show 1 ≤ 96 by decide)
  have hs96 := (Nat.pow_le_pow_left (show M+1 ≤ X by dsimp [X]; omega) 2).trans
    (Nat.pow_le_pow_right hx (show 2 ≤ 96 by decide))
  have hY96 : Y ≤ 3*X^96 := by
    dsimp only [Y]
    have : E ≤ X := by dsimp [X]; omega
    omega
  have hmeta : (Packet.bits D p).length ≤ 3*P*T :=
    (metaLen.trans hpay).trans ((Nat.mul_le_mul_left P (Nat.mul_le_mul_right L hY96)).trans_eq (regroup P (X^96) L))
  have hxT := hx96.trans (Nat.le_mul_of_pos_right _ hL)
  have heT : ext.length ≤ T := he.trans ((show E ≤ X by dsimp [X]; omega).trans hxT)
  have hT : 1 ≤ T := hx.trans hxT
  have htime : t ≤ B*T := by simpa only [T,Nat.mul_assoc] using ht
  have extra : t+14*(Packet.bits D p).length+12*ext.length+22 ≤ C*X^96*L := by
    rw [show C*X^96*L = C*T from Nat.mul_assoc ..]
    dsimp only [C]; simp only [Nat.add_mul,Nat.mul_assoc] at hmeta ⊢; omega
  have hlen := hpay.trans (Nat.mul_le_mul_right (Y*L) (show P ≤ C by dsimp [C]; omega))
  rw [← Nat.mul_assoc] at hlen
  obtain ⟨hq,hclock⟩ := hn r M E w p hr hrω hM hE hw hwn D st hf hc hg _ _ hlen extra
  refine ⟨hq,?_⟩
  have h := packet_work D p t ext
  dsimp only at h ⊢
  omega

end RoutingISA.CompactPacket

end BorderVNP
end Computability
end OAI
