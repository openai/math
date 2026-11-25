import OAI.Hierarchy.DescentMatcherRateNumbers
import OAI.Hierarchy.DescentPackedPhaseResident
import OAI.Hierarchy.DescentPackedPayloadBudget

namespace OAI
/-! # Literal header, scratch and final matching aperture at unequal word widths -/

namespace Hierarchy.DescentPackedColony.Phase.Arena
open DescentColonies DescentSIMDLookup _root_.OAI.Hierarchy.DescentPackedColony.Frame
open scoped Classical
variable {k Δ G H b w h : ℕ}

def pageCharge (H G h a : ℕ) := 2^(h/2)*h+2*(2*H*h+4*H*G*a+h)

private theorem page_bits_of_payload (A : Chart) (k b H G h : ℕ)
    (fixed : A.bits=Frame.pageBits H G k b (lanes h (unit k b))) (wide : 2*unit k b≤h) :
    A.page*h≤pageCharge H G h (unit k b) := by
  let a:=unit k b
  let M:=lanes h a
  let n:=H*chunks G M
  let t:=max H n
  have hp : 0<a := by dsimp [a,unit];omega
  have rows : n*h≤H*h+4*H*G*a := volume H G h a hp wide
  have u : DescentPackedColony.unit k b≤a := by
    unfold DescentPackedColony.unit
    apply max_le <;> dsimp [DescentPackedColony.width,a,unit] <;> omega
  have bits : DescentPackedColony.unit k b*M≤h/2 := (Nat.mul_le_mul_right _ u).trans (by simpa [Nat.mul_comm] using lanes_fit h a)
  have tpos : 2^(t.log2+1)≤2*(t+1) := by
    rw [Nat.pow_succ]
    by_cases z:t=0
    · simp [z]
    · have:=Nat.log2_self_le z;omega
  have area : t≤H+n := max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
  rw [Frame.Chart.page,fixed]
  change 2^(max (t.log2+1) (DescentPackedColony.unit k b*M))*h≤_
  rcases le_total (t.log2+1) (DescentPackedColony.unit k b*M) with limit|limit
  · rw [max_eq_right limit]
    exact (Nat.mul_le_mul_right h (Nat.pow_le_pow_right (by decide) bits)).trans (Nat.le_add_right ..)
  · rw [max_eq_left limit]
    have old:=(Nat.mul_le_mul_right h tpos).trans (Nat.mul_le_mul_right h (Nat.mul_le_mul_left 2 (Nat.add_le_add_right area 1)))
    apply old.trans
    have result:=Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.add_le_add_left rows (H*h)) h)
    unfold pageCharge
    nlinarith only [result,Nat.zero_le (2^(h/2)*h)]

theorem header_words (A : Chart) (_H _G k b Δ h : ℕ) :
    first A Δ k b h-A.origin≤
       (2^k-1)*(Δ+3+4*k)*A.page+(Menu.pages k+2^k*((2^k-1)*2^(k+1)))*2^(h/2) := by
  have panel:=(Menu.bit_bound k b h (.inl ()))
  change (1+k*2^k)*lanes h (unit k b)≤h/2 at panel
  let sheets := (2^k-1)*(Δ+3+4*k)*A.page
  let winners := 2^k*((2^k-1)*2^(k+1))
  let lookup := 2^((1+k*2^k)*lanes h (unit k b))
  have bounded : winners*lookup≤winners*2^(h/2) :=
    Nat.mul_le_mul_left winners (Nat.pow_le_pow_right (by decide : 0<2) panel)
  have address : first A Δ k b h=A.origin+(sheets+Menu.pages k*2^(h/2)+winners*lookup) := by
    unfold first Arena.names menu Frame.Chart.sheetEnd Frame.Chart.sheetSpan PackedWinnerRAM.tableWords
    dsimp only [sheets,winners,lookup]
    ring
  rw [address,Nat.add_sub_cancel_left]
  calc
    _ ≤ sheets+Menu.pages k*2^(h/2)+winners*2^(h/2) := Nat.add_le_add_left bounded _
    _ = _ := by dsimp only [sheets,winners]; ring

theorem header_bits (A : Chart) (Δ H G k b h w K : ℕ)
    (page : A.bits=Frame.pageBits H G k b (lanes h (unit k b))) (wide : 2*unit k b≤h) (hardware : w≤K*h) :
    (first A Δ k b h-A.origin)*w ≤ K*(sharedTables k Δ * (2^(h/2)*h) +
      ((2^k-1)*(Δ+3+4*k))*(2*(2*H*h+4*H*G*unit k b+h))) := by
  apply DescentPackedPayloadBudget.clock hardware
  let sheets := (2^k-1)*(Δ+3+4*k)
  let tables := Menu.pages k+2^k*((2^k-1)*2^(k+1))
  have charged := Nat.mul_le_mul_left sheets (page_bits_of_payload A k b H G h page wide)
  calc
    _ ≤ (sheets*A.page+tables*2^(h/2))*h := Nat.mul_le_mul_right h (header_words A H G k b Δ h)
    _ = sheets*(A.page*h)+tables*(2^(h/2)*h) := by ring
    _ ≤ sheets*(pageCharge H G h (unit k b))+tables*(2^(h/2)*h) := Nat.add_le_add_right charged _
    _ = _ := by dsimp only [sheets,tables,pageCharge,sharedTables]; ring

theorem total_words (A : Chart) (Δ k b h H G : ℕ) :
    endAt A Δ k b h+2^k*(H*chunks G (lanes h (unit k b)))-A.origin =
      (first A Δ k b h-A.origin) + ((2^k-1)*(k+1)+7)*A.page +
        ((2^k-1)+1+(2^(k+1)+1))+2^k*(H*chunks G (lanes h (unit k b))) := by
  have low : A.origin≤first A Δ k b h := (show A.origin≤ menu A Δ k from Nat.le_add_right ..).trans
    ((show menu A Δ k≤names A Δ k h from Nat.le_add_right ..).trans (Nat.le_add_right ..))
  let payload := ((2^k-1)*(k+1)+7)*A.page +
    ((2^k-1)+1+(2^(k+1)+1)) + 2^k*(H*chunks G (lanes h (unit k b)))
  have layout : endAt A Δ k b h+2^k*(H*chunks G (lanes h (unit k b))) =
      payload + first A Δ k b h := by
    dsimp only [endAt, colorWork, selected, seedWork, payload]
    ring
  rw [layout, Nat.add_sub_assoc low]
  dsimp only [payload]
  ac_rfl

end Hierarchy.DescentPackedColony.Phase.Arena

end OAI
