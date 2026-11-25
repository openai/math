import OAI.Computability.NearSquareRoot.InterchangeROMStageVolume
import OAI.Computability.NearSquareRoot.InterchangeROMStageVolumeCoefficient

/-! # Effective local time and space allowances for the entire grouped stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageVolume
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROM InterchangeROMStage InterchangeROMStageTable

/-- The coefficient bounding any intermediate packet, header included. -/
def packetFactor (c : Parameters) := slotMax c*(2*c.2.1+2)+4

/-- This one coefficient bounds the local steps, resident data and return depth
of any instruction, before charging its child movements. -/
def localFactor (c : Parameters) :=
  ((slotMax c+2)*160+172)*packetFactor c + gateMax c + 95

/-- Eleven instructions, eleven program joins and one final pass. -/
def stageFactor (c : Parameters) := 11*localFactor c + 23

theorem primrec_packetFactor : Primrec packetFactor := by
  have p : Primrec (fun c : Parameters => c.2.1) := Primrec.fst.comp Primrec.snd
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp primrec_slotMax
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) p) (Primrec.const 2))) (Primrec.const 4)

theorem primrec_localFactor : Primrec localFactor := by
  have route := Primrec.nat_mul.comp (Primrec.nat_add.comp primrec_slotMax (Primrec.const 2)) (Primrec.const 160)
  exact Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp
    (Primrec.nat_add.comp route (Primrec.const 172)) primrec_packetFactor) primrec_gateMax) (Primrec.const 95)

theorem primrec_stageFactor : Primrec stageFactor :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 11) primrec_localFactor) (Primrec.const 23)

theorem computable_stageFactor : Computable stageFactor := primrec_stageFactor.to_comp

theorem uniform_render {A : Type} {Y : A → Type} (c : Parameters) [NeZero c.2.1] (n : ℕ)
    (addr : Series A) (pay : (a : A) → Series (Y a)) (width : ℕ) (hw : ∀ a, (pay a).count ≤ width)
    (x : Ground → (a : A) → Y a → ZMod c.2.1) (header : Tree) :
    (packet header (render c n addr pay x)).count+1 ≤ packetFactor c*mass header addr.count width := by
  apply (render_size c n addr pay width hw x header).trans
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ (slots_le_any c n)) _)

theorem uniform_typed {A : Type} {Y : A → Type} (c : Parameters) [NeZero c.2.1]
    (r : Frame.Realization c.1) (n : ℕ) (addr : Series A) (pay : (a : A) → Series (Y a))
    (width : ℕ) (hw : ∀ a, (pay a).count ≤ width)
    (x : (a : A) → Y a → r.Boundary n → Fin c.2.2.1 → ZMod c.2.1) (header : Tree) :
    (Tree.fork header (r.Tape n c.2.2.1 (fun z j => stripe addr fun a => stripe (pay a)
      fun k => InterchangeROMTable.numeral (x a k z j).val))).count+1 ≤
        packetFactor c*mass header addr.count width := by
  apply (typed_size r n _ addr pay width hw x header).trans
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ (slots_le_any c n)) _)

private theorem factor_bounds (c : Parameters) :
    ((slotMax c+2)*160)*packetFactor c ≤ localFactor c ∧
    171*packetFactor c ≤ localFactor c ∧
    packetFactor c + (gateMax c + 95) ≤ localFactor c := by
  unfold localFactor
  rw [Nat.add_mul ((slotMax c+2)*160) 172 (packetFactor c)]
  omega

theorem route_local (c : Parameters) (n V W m : ℕ)
    (hi : V+1 ≤ packetFactor c*m) (ho : W ≤ packetFactor c*m) :
    (slots c (n+1)+2)*(160*(V+1)) ≤ localFactor c*m ∧
      170*(V+1)+W ≤ localFactor c*m := by
  obtain ⟨rt,rs,_⟩ := factor_bounds c
  constructor
  · calc
      _ ≤ (slotMax c+2)*(160*(packetFactor c*m)) :=
        Nat.mul_le_mul (Nat.add_le_add_right (slots_le_any c _) _) (Nat.mul_le_mul_left _ hi)
      _ = (((slotMax c+2)*160)*packetFactor c)*m := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ rt
  · calc
      _ ≤ 170*(packetFactor c*m)+packetFactor c*m := Nat.add_le_add (Nat.mul_le_mul_left _ hi) ho
      _ = (171*packetFactor c)*m := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ rs

theorem gate_local (c : Parameters) (tag : Fin 5) (header : Tree) (records w V : ℕ)
    (hi : V ≤ packetFactor c * mass header records w) :
    let m := mass header records w
    let t := 84*header.count + charge c (c.1.gate tag (inputBoundary tag)) records w + 11
    t ≤ localFactor c*m ∧ V+t ≤ localFactor c*m := by
  let m := mass header records w
  have q : records*(w+1)+1 ≤ m := by dsimp [m,mass]; omega
  have h : header.count ≤ m := by dsimp [m,mass]; omega
  have hm : 1 ≤ m := by dsimp [m,mass]; omega
  have clk := (charge_le_factor c tag records w).trans (Nat.mul_le_mul_left _ q)
  have total : V+(84*header.count+charge c (c.1.gate tag (inputBoundary tag)) records w+11) ≤ localFactor c*m := calc
    _ ≤ packetFactor c*m+(84*m+gateMax c*m+11*m) := by dsimp only [m] at *; omega
    _ = (packetFactor c+(gateMax c+95))*m := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (factor_bounds c).2.2
  exact ⟨by change _ ≤ localFactor c*m; omega,total⟩

/-- The exact eleven-instruction clock from the physical composition includes
one copy of the six movement ledgers. -/
theorem clock (c : Parameters) (m : ℕ) (hm : 1 ≤ m) (rr ledger : Fin 6 → ℕ) (tt : Fin 5 → ℕ)
    (route : ∀ k, rr k ≤ localFactor c*m + ledger k)
    (gate : ∀ k, tt k ≤ localFactor c*m) :
    23 + (∑ k, rr k) + ∑ k, tt k ≤ stageFactor c*m + ∑ k, ledger k := by
  have h₁ := Finset.sum_le_sum (s:=Finset.univ) (fun k _ => route k)
  have h₂ := Finset.sum_le_sum (s:=Finset.univ) (fun k _ => gate k)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h₁ h₂
  unfold stageFactor
  rw [Nat.add_mul,Nat.mul_assoc]
  omega

end InterchangeROMStageVolume

end NearSquareRoot
end Computability
end OAI
