import OAI.Hierarchy.DescentArgumentPageWordTariff
import OAI.Hierarchy.DescentOrdinaryPaletteBirthBook

namespace OAI
/-! # Word cost of printing the original six-party coefficient dictionary -/
namespace Hierarchy.DescentOrdinaryPaletteBirth
open DescentSixParty DescentOrdinaryBorn DescentStaticWordColumn ProtocolRAM

/-- The final partial group page costs one executed word per old host. The static
dictionary is charged once over all hosts and groups. -/
theorem scaled {F : Type} [Field F] (G : PoweredGadget F) (seed Z : ℕ) (op : RotorSpec)
    (B : Chart) (base w h ratio unit : ℕ) (src : Bank)
    (table : 2*B.chipBits*B.lanes≤h/2) (fill : h≤B.lanes*unit) (bus : w≤ratio*h) :
    ((phase G seed Z op B src base w).ticks+7*names (phase G seed Z op B src base w).program)*w≤
      2048*ratio*(fields B+1)*(h+B.hosts*h+B.hosts*B.groups*unit)+
        2048*ratio*(fields B+1)*2^(h/2)*h :=by
  apply DescentDatedSeedStartup.page_scan_words B.hosts B.groups B.lanes unit h w ratio (fields B) 2048 _ fill bus
  obtain ⟨time,text⟩:=price G seed Z op B src base w
  have static : 2^((2*B.chipBits)*B.lanes) ≤ 2^(h/2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) table
  have bound : bookWords B≤(fields B+1)*(2*2^(h/2)) :=by
    calc
      bookWords B=(1+fields B)*(2*2^((2*B.chipBits)*B.lanes)) := by
        simp only [bookWords,DescentOperandFamilyBook.words,DescentOperandFamilyBook.unit,Nat.mul_one,two_mul]
      _≤(fields B+1)*(2*2^(h/2)) :=by
        rw [Nat.add_comm 1 (fields B)]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ static)
  change _≤2048*((fields B+1)*(1+B.rows)+(fields B+1)*2^(h/2))
  change _≤4+10*bookWords B+(4+fields B*(4+B.rows*(2*32+4))) at time
  change _≤15*(bookWords B+1)+(15+fields B*(11+4*32)) at text
  nlinarith only [time,text,bound,Nat.zero_le (fields B),Nat.zero_le B.rows,
    Nat.zero_le (fields B*B.rows),Nat.zero_le (2^(h/2)),Nat.zero_le (fields B*2^(h/2))]

end Hierarchy.DescentOrdinaryPaletteBirth

end OAI
