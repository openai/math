import OAI.Hierarchy.TaggedShorterClockCost
import OAI.Hierarchy.TaggedShorterHistoryOrder

namespace OAI
/-! # The bit cost of the fixed 72-label terminal CPU and its sorted record history -/

namespace Hierarchy.DescentCompiler
open TaggedShorterClock TaggedShorterHistoryOrder

/-- A constant common to all programs, packet widths, addresses and run times. -/
def fixedISAPrice : ℕ := 4*unitPrice 1 72 13+250000

/-- The literal tariff of the weighted terminal host after installing the fixed
CPU. The seven fields of every record and all layers of the seven-level sort
are paid, as are the exterior pins and the local sorting calls. -/
theorem fixed_isa_tariff (w m fuel steps seed rows word bins W choices obs exterior sort : ℕ)
    (depth : steps≤4^7) :
    4*(seed+(fuel+1)*unitPrice w 72 13+
      2^m*(20000*(w+1))+(4*(2^m*(50*(w+1)+11)+2*2^m+1)+1))+1+
      9*(rows*word)+bins*W+
      (choices+fuel*((5+13)*(w+1))+obs*(w+1)+(steps+1)*(2^m*RecordWidth (w+1)))+
      exterior+sort ≤
    4*seed+9*(rows*word)+bins*W+choices+exterior+sort+
      fixedISAPrice*(fuel+1+2^m+obs)*(w+1) := by
  rw [recordWidth_eq]
  let bill (cpu height : ℕ) :=
    4*(seed+(fuel+1)*cpu+2^m*(20000*(w+1))+(4*(2^m*(50*(w+1)+11)+2*2^m+1)+1))+1+
      9*(rows*word)+bins*W+
      (choices+fuel*((5+13)*(w+1))+obs*(w+1)+(height+1)*(2^m*(7*(w+1))))+
      exterior+sort
  have cpu := unitPrice_le w 72 13
  have grow : bill (unitPrice w 72 13) steps ≤ bill ((w+1)*unitPrice 1 72 13) (4^7) := by
    dsimp only [bill]
    gcongr
  apply grow.trans
  dsimp only [bill,fixedISAPrice]
  generalize unitPrice 1 72 13=U
  generalize (2:ℕ)^m=N
  ring_nf
  omega

end Hierarchy.DescentCompiler

end OAI
