import OAI.Computability.BorderVNP.PackedFrozenLayerCost
import OAI.Computability.BorderVNP.PackedFrozenPrepBatch

/-! # Gate count for freshly frozen subdivision records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.PrepBatch

open Crossing Shortening Shortening.PublicCapacity Shortening.PublicEndpoints PackedHistoryCircuit WorkWords
open CellAddressCircuit Subdivision VPVNP.VerifierNetwork ParseBatchSort
open private view_cubic prefix_size from OAI.Computability.BorderVNP.PackedFrozenLayerCost

variable {k w np extra : ℕ} {s : Shape} (T : Format)
    {Old A B : Type} [Fintype Old] [Fintype B]
    (prior : Inputs A s.sites s.edges w w → Old) (ports : WorkWords.Ports np)
    (fit : (s.subdivide extra).sites ≤ 2^w)

private theorem dimensions (s m np extra : ℕ) :
    let R := 8*(extra+1)*(s+m+np+1)
    1+CellAddressCircuit.count s m np s ≤ R ∧
      1+CellAddressCircuit.count (s+extra*m) ((extra+1)*m) np (s+extra*m) ≤ R ∧
      s+(m+m+np)+1 ≤ R ∧ Fintype.card (Gates.Row m np extra) ≤ R := by
  simp only [Gates.Row,Gates.Old,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,CellAddressCircuit.count]
  constructor
  · nlinarith only [Nat.zero_le (extra*s),Nat.zero_le (extra*m),Nat.zero_le (extra*np),Nat.zero_le extra]
  constructor
  · nlinarith only [Nat.zero_le (extra*s),Nat.zero_le (extra*m),Nat.zero_le (extra*np),Nat.zero_le extra]
  constructor <;> nlinarith only [Nat.zero_le (extra*s),Nat.zero_le (extra*m),Nat.zero_le (extra*np),Nat.zero_le extra]

set_option maxHeartbeats 1500000 in
/-- The two site-address scans, both prefix lookups and every newly frozen
record cost a cubic word factor per allocated site, cable or port. The old
owner-key queries retain their separate charge. -/
theorem leafCharge_cubic (i : Fin k) (W : ℕ) (hw : w ≤ W)
    (hlog : Nat.clog 2 (8*(extra+1)*(s.sites+s.edges+np+1)) ≤ W) :
    leafCharge (B := B) T prior ports fit i ≤
      lookupCost s.sites (Fintype.card T.Rows) w w + 15000*(8*(extra+1)*(s.sites+s.edges+np+1))*(W+1)^3 := by
  let R := 8*(extra+1)*(s.sites+s.edges+np+1)
  let unit := R*(W+1)^3
  let old := oldFields (B := B) T prior ports fit i
  let new := newFields (B := B) (Old := Old) T ports fit i
  let col := siteWord (s := s) (w := w) (B := B) (Old := Old) (extra := extra) T i
  let present := hopPresent (B := B) (Old := Old) (s := s) (extra := extra) (w := w) T i
  obtain ⟨rows₀,rows₁,prefixRows,rows⟩ := dimensions s.sites s.edges np extra
  have oldSize : (Views.frame old).size ≤ 3200*unit := (view_cubic old rows₀ ⟨hw,hw,hlog⟩).trans_eq (by ring)
  have newSize : (Views.frame new).size ≤ 3200*unit := (view_cubic new rows₁ ⟨hw,hw,hlog⟩).trans_eq (by ring)
  have prefixes (b : Bool) : (Layer.prefixFrame old (col b)).size ≤ 1000*unit := by
    have log := (Nat.clog_mono_right 2 ((Nat.le_succ _).trans prefixRows)).trans hlog
    exact (prefix_size old (col b)).trans ((lookupCost_cubic s.sites (s.edges+s.edges+np) w w W log hw hw).trans
      ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1000 prefixRows)).trans_eq (by ring)))
  let Q := Fintype.card (Gates.Row s.edges np extra)
  have command : Q*(1+w+6*w)*(30*(w+w)+18) ≤ 500*unit := by
    rw [Nat.mul_assoc]
    have factor : (1+w+6*w)*(30*(w+w)+18) ≤ 500*(W+1)^3 := by
      calc _ ≤ (1+W+6*W)*(30*(W+W)+18) := by gcongr
           _ ≤ _ := by nlinarith only [Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
    exact (Nat.mul_le_mul rows factor).trans_eq (by ring)
  have emission : Q*(4500*(w+1)^2) ≤ 4500*unit := by
    have factor : (w+1)^2 ≤ (W+1)^3 :=
      (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by positivity) (by decide : 2 ≤ 3))
    exact (Nat.mul_le_mul rows (Nat.mul_le_mul_left 4500 factor)).trans_eq (by ring)
  have scan := Gates.inputs_size old new (col false) (col true) present
  change (Gates.inputs old new (col false) (col true) present).size ≤
    (Views.frame old).size + ((Views.frame new).size +
      ((Layer.prefixFrame old (col false)).size + (Layer.prefixFrame old (col true)).size)) +
    Q*(1+w+6*w)*(30*(w+w)+18) at scan
  have p₀ := prefixes false
  have p₁ := prefixes true
  have pos : 0 < unit := by dsimp [unit,R]; positivity
  unfold leafCharge
  apply Nat.add_le_add_left
  change (Gates.inputs old new (col false) (col true) present).size + 1 + Q*(4500*(w+1)^2) ≤ 15000*R*(W+1)^3
  rw [Nat.mul_assoc 15000 R]
  change _ ≤ 15000*unit
  have sum := Nat.add_le_add (Nat.add_le_add oldSize (Nat.add_le_add newSize (Nat.add_le_add p₀ p₁))) command
  refine (Nat.add_le_add (Nat.add_le_add_right (scan.trans sum) 1) emission).trans ?_
  omega

/-- Closed near-linear bound at the true subdivision widths. Its sorting
depth depends logarithmically on the incoming rectangle and the hop count. -/
theorem leafCharge_polynomial (i : Fin k) :
    leafCharge (B := B) T prior ports fit i ≤
      lookupCost s.sites (Fintype.card T.Rows) w w + 15000*(8*(extra+1)*(s.sites+s.edges+np+1))*
        (w + Nat.clog 2 (s.sites+2*s.edges+np+2) + Nat.clog 2 (8*(extra+1)) + 1)^3 := by
  apply leafCharge_cubic T prior ports fit i _ (by omega)
  have base : s.sites+s.edges+np+1 ≤ s.sites+2*s.edges+np+2 := by omega
  apply Nat.clog_le_of_le_pow
  rw [pow_add,pow_add]
  have a := Nat.le_pow_clog (by decide : 1<2) (8*(extra+1))
  have b := base.trans (Nat.le_pow_clog (by decide : 1<2) (s.sites+2*s.edges+np+2))
  exact (Nat.mul_le_mul a b).trans (by
    rw [Nat.mul_comm (2^Nat.clog 2 (8*(extra+1))) _]
    gcongr
    exact Nat.le_mul_of_pos_left _ (pow_pos (by decide) w))

end Packing.Inherited.FrozenTape.PrepBatch

end BorderVNP
end Computability
end OAI
