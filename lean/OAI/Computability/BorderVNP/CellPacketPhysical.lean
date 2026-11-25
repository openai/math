import OAI.Computability.BorderVNP.CellDirectoryPhysical
import OAI.Computability.BorderVNP.CellPacketInputSize

/-! # The private tape clock with the original cell packet and boundary bits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactPacket

open Filter TeamScales CellSparse CellMacro CellMacro.Generator RationalHitting.StackLanguage

/-- Translation and boundary injection add an exact term to the private validation work. -/
theorem packet_work (d : Directory) (p t : ℕ) (ext : List Bool) :
    let s := d.program p
    let metadata := Packet.bits d p
    let ops := (CompactMachine.withExternal ext s).expand []
    generationCost 8 metadata ext s t + (2*(stream ops).length+1) + budget ops =
      generatedWork s + (t+14*metadata.length+12*ext.length+22) := by
  dsimp only
  obtain ⟨hs,hb⟩ := CompactMachine.byteCosts_withExternal ext (d.program p) []
  rw [hs,hb]
  unfold generationCost generatedWork work
  omega

private theorem packet_envelope {X L M E m : ℕ} (hX : X = M+E+1) (hL : 1 ≤ L)
    (hm : m ≤ E) : m ≤ X^96*L ∧ (M+1)^2+E+1 ≤ 3*X^96 := by
  have hx : 1 ≤ X := by omega
  have hx1 : X ≤ X^96 := by simpa only [pow_one] using Nat.pow_le_pow_right hx (show 1 ≤ 96 by decide)
  have hx2 := Nat.pow_le_pow_right hx (show 2 ≤ 96 by decide)
  have hm2 := (Nat.pow_le_pow_left (show M+1 ≤ X by omega) 2).trans hx2
  have hmul := Nat.le_mul_of_pos_right (X^96) hL
  omega

private theorem packet_reorder (a b c : ℕ) : a*(3*b*c) = 3*a*(b*c) := by ring

/-- Both private-machine resource limits for an original sparse packet. The count and
width assumptions describe its transported data, and the translation parameter is the
actual time of the typed packet reader. -/
theorem eventually_typed_clock (A B j : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r M E w p t : ℕ, 1 ≤ r →
      (r:ℝ) ≤ 2^((n:ℝ)^ω) → M ≤ width n (1/5) → E ≤ width n (1/4) → 0 < w → w ≤ n →
      ∀ (D : Directory) (ext : List Bool), ext.length ≤ E →
      D.StaticBounds A M → D.CompactFields p (4*(M+E+1)^3) →
      D.records.length ≤ 4*(M+E+1)^3 → D.reportedCounts.length ≤ 4*(M+E+1)^3 →
      Packet.storedMass D ≤ A*(M+1)^2 → Packet.RawFields D p (B*(n+2)^j) →
      t ≤ B*(M+E+1)^96*(n.size+1)^j →
      (CompactFrame.pack w (Packet.input D p ext)).length ≤ width n (1/2) ∧
      let s := D.program p
      let ops := (CompactMachine.withExternal ext s).expand []
      2*(3*((CompactFrame.pack w (Packet.input D p ext)).length*w)+
        generationCost 8 (Packet.bits D p) ext s t + (2*(stream ops).length+1) + budget ops) ≤ n^25 := by
  let P := 4*(8*A+4)*((B+3).size+j+1)
  let C := B+42*(P+2)+34
  obtain ⟨ω,hω,room⟩ := eventually_compiled_load A C (max j 1)
  refine ⟨ω,hω,?_⟩
  filter_upwards [room] with n hn
  intro r M E w p t hr hrω hM hE hw hwn D ext hExt st hf hc hg hstore hraw ht
  let X := M+E+1
  let Y := (M+1)^2+E+1
  let L := (n.size+1)^(max j 1)
  have hL : 1 ≤ L := Nat.one_le_pow _ _ (by omega)
  have hL₁ : n.size+1 ≤ L := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (show 1 ≤ n.size+1 by omega) (le_max_right j 1)
  have hLj : (n.size+1)^j ≤ L := Nat.pow_le_pow_right (by omega) (le_max_left ..)
  have hlen := Packet.input_length_le D p ext st hstore hraw le_rfl
  change (Packet.input D p ext).length ≤ P*(M+1)^2*(n.size+1)+1+ext.length at hlen
  have hY : (M+1)^2 ≤ Y := by dsimp [Y]; omega
  have hYext : 1+ext.length ≤ Y := by dsimp [Y]; omega
  have hYL := Nat.le_mul_of_pos_right Y hL
  have hp1 : P*(M+1)^2*(n.size+1) ≤ P*(Y*L) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hY) hL₁
  have hbytes : (Packet.input D p ext).length ≤ (P+2)*(Y*L) := by rw [Nat.add_mul]; omega
  have hmeta : (Packet.bits D p).length ≤ (Packet.input D p ext).length := by
    simp [Packet.input,codeWord_length]; omega
  obtain ⟨hext,hY96⟩ := packet_envelope (X := X) rfl hL hExt
  let T := X^96*L
  have hdata : (Packet.bits D p).length ≤ 3*(P+2)*T := by
    apply hmeta.trans (hbytes.trans ?_)
    calc (P+2)*(Y*L) ≤ (P+2)*((3*X^96)*L) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right L hY96)
         _ = _ := packet_reorder (P+2) (X^96) L
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le (Nat.one_le_pow _ X (by dsimp [X]; omega)) hL
  have htime : t ≤ B*T := by rw [show B*T = B*X^96*L from (Nat.mul_assoc ..).symm]; exact ht.trans (Nat.mul_le_mul_left _ hLj)
  have hextra : t+14*(Packet.bits D p).length+12*ext.length+22 ≤ C*X^96*L := by
    rw [show C*X^96*L = C*T from Nat.mul_assoc ..]
    dsimp only [C]; simp only [Nat.add_mul,Nat.mul_assoc] at hdata ⊢
    change ext.length ≤ T at hext
    omega
  have hpre := hbytes.trans (Nat.mul_le_mul_right (Y*L) (show P+2 ≤ C by dsimp [C]; omega))
  rw [← Nat.mul_assoc] at hpre
  obtain ⟨hq,hclock⟩ := hn r M E w p hr hrω hM hE hw hwn D st hf hc hg _ _ hpre hextra
  refine ⟨hq,?_⟩
  dsimp only
  have h := packet_work D p t ext
  dsimp only at h
  omega

end RoutingISA.CompactPacket

end BorderVNP
end Computability
end OAI
