import OAI.Hierarchy.DescentSeedNativeWideNode
import OAI.Hierarchy.DescentDatedSeedExtent
import OAI.Hierarchy.DescentSeedBitRectangle

namespace OAI
/-! # Charging the program that reads the original bits and enters the first native date -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSeedRoot DescentPackedSeed DescentCompiler DescentColonies DescentSIMDLookup DescentDyadicSpan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} {k cp p H : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k) (publicWide : Fintype.card (Vertex X)≤H)
    (l : Layout) (header payload w : ℕ)
local notation "g₀" => S.groupCount 0
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "finish" => (chart).seedEnd top
local notation "stock" => Fintype.card (Vertex X)
local notation "runCost" => wideTicks (S:=S) (k:=k) (H:=H) X l payload+
  7*DescentStaticWordColumn.names (wideNode X digits publicWide l header payload w)

theorem selector_fill (factor word : ℕ) (enough : 2*digitsNeeded l.seedWidth≤payload)
    (cpu : word≤factor*payload) :
    word≤ DescentPackedSeed.multiplicity payload l.seedWidth*(4*factor*digitsNeeded l.seedWidth) :=by
  have bits : 0<digitsNeeded l.seedWidth := Nat.zero_lt_succ _
  unfold DescentPackedSeed.multiplicity
  split
  · rename_i grouped
    have cover:=pitch_fill payload (8*digitsNeeded l.seedWidth) word factor (by omega) (by omega) cpu
    calc
      word≤_:=cover
      _=_:=by ring
  · exact pitch_fill payload _ word factor bits enough cpu

private theorem allocation_price {ticks entries core metadataWords total : ℕ}
    (fee : ticks ≤ 1300+66*entries+1600*core+115*metadataWords)
    (within : core ≤ total) (metadata : metadataWords ≤ total) (active : 0 < total) :
    ticks ≤ 3500*total+66*entries := by omega

theorem wide_rectangle (positive : 0<H)
    (sRows : 0<chunks g₀ l.packedLanes) (oRows : 0<chunks g₀ l.operandLanes)
    (s₁ s₂ s₃ : ℕ) (sm : g₀≤l.packedLanes ∨ w+1≤l.packedLanes*s₁) (om : w+1≤l.operandLanes*s₂)
    (cm : w+1≤ DescentPackedSeed.multiplicity payload l.seedWidth*s₃) :
    (runCost)*(w+1)≤H*(w+1)*(14000066+224000*(l.groupsPerNode+1)*2^k)+
      H*(g₀*2^k)*(14000000*s₁+224000*(l.groupsPerNode+1)*s₂+528*s₃) :=by
  have fee:=wide_price X digits publicWide l header payload w oRows
  have floors:=fences X l H g₀ k
  have pre : l.base≤top := floors.1.trans (floors.2.1.trans floors.2.2)
  have dt : top+(chart).names*(chart).rows≤finish := Nat.le_add_right ..
  have pp : top-l.base+1≤finish-l.base+1 :=by omega
  have metadataSize : (chart).names*(chart).rows≤finish-l.base+1 :=by omega
  have receipt : (runCost) ≤ 3500*(finish-l.base+1)+66*(DescentPackedSeed.rows X S.copies l.seedWidth payload) :=
    allocation_price fee pp metadataSize (Nat.succ_pos _)
  have old : Fintype.card (Old X)≤ stock :=
    Fintype.card_le_of_embedding ⟨Sum.inl,Sum.inl_injective⟩
  have copies:=Fintype.card_congr digits
  simp only [Fintype.card_fin,Fintype.card_prod] at copies
  have same : S.copies=g₀*2^k :=by simpa [Block] using copies
  have cap : finish=seededFloor l.base stock H g₀ l.packedLanes l.operandLanes k l.groupsPerNode :=rfl
  rw [cap] at receipt
  have rowCount : DescentPackedSeed.rows X S.copies l.seedWidth payload=
      Fintype.card (Old X)*chunks ((g₀*2^k)*8) (DescentPackedSeed.multiplicity payload l.seedWidth) :=by
    simp only [DescentPackedSeed.rows,same]
  rw [rowCount] at receipt
  exact seed_bit_rectangle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (old.trans publicWide) publicWide positive
    sRows oRows sm om cm receipt

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
