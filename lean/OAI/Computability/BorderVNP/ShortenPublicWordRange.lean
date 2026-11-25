import OAI.Computability.BorderVNP.ShortenPublicPaddedWords
import OAI.Computability.BorderVNP.ShortenPublicBottomCapacity
import OAI.Computability.BorderVNP.ShortenPublicSegmentRoundWork

/-!
# The actual depth and sorting logarithms of a public stage

For stable row capacities bounded by the processor address range, the canonical
binary width holds every pointer and every multiplied population. The measured
congruence depth, product-address encoding, site catalog and optional pointer
bits then meet the common width hypotheses of the public histogram compiler.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicCapacity

open Cover Cover.AddressCircuit Epoch TeamScales PublicSegments PublicPopulation
open scoped Classical

/-- A checked population count from any bin is bounded by the expanded load
on the complete set of physical old sites. -/
theorem count_words {D : ℕ} {P T : Type*} {A : Type} [Fintype P] [Fintype T] {bits : P → ℕ}
    (N : Crossing.Network D P bits) (tile : N.Site → T) (prior payload : N.Site → ℕ) (cap μ V E : ℕ)
    (hc : ∀ t, localRecords N true prior payload (fun v => tile v=t) ≤ cap)
    (bin : N.Edge → Option A) (a : A) :
    μ * SeedIntervals.count N bin a < 2^wordSize V E μ (Fintype.card T) cap := by
  have total := totalWidth_le_records N tile prior payload cap hc
  have h : SeedIntervals.count N bin a ≤ ∑ e, N.width e := by
    rw [SeedIntervals.count_eq_sum]
    exact Finset.sum_le_sum fun e _ => by split <;> omega
  exact (Nat.mul_le_mul_left μ (h.trans total)).trans_lt (wordSize_fits V E μ (Fintype.card T) cap).2.2

/-- The sort width, high congruence input, and actual site data are simultaneously
at most a fixed multiple of log(2nr). `ptr` allows several width-sized pointer
columns to be carried in each physical site's public record. -/
theorem public_word_ranges (I : Type*) [Fintype I] [Nonempty I] (q tags bins nWord ptr : ℕ) (factor : ℕ := 3) :
    ∃ Z : ℕ, ∀ n r V E l w data, 1 ≤ n → 1 ≤ r →
      V+E+Fintype.card (I → Deck l)+1 ≤ r*n →
      w ≤ factor*logWidth r n →
      data ≤ tags+90*q*(l+2*nWord+1)+ptr*w →
      let W := Z*logWidth r n
      l+2*nWord+1 ≤ W ∧ Nat.clog 2 (V+2*E)+w+data+1 ≤ W ∧
        Nat.clog 2 (E+Fintype.card (I → Deck l)*bins)+(Nat.clog 2 bins+keyWidth q l)+w+1 ≤ W := by
  let Z := 20+factor+2*nWord+tags+90*q*(4+2*nWord)+factor*ptr+Nat.clog 2 (bins+1)+Nat.clog 2 bins+360*q
  refine ⟨Z,?_⟩
  intro n r V E l w data hn hr hrows hw hdata W
  let tiles := Fintype.card (I → Deck l)
  let L := logWidth r n
  have hL : 1 ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from public_logWidth n r]
    have hz : 2 ≤ 2*n*r := by nlinarith [Nat.mul_le_mul hn hr]
    exact (Nat.clog_mono_right 2 hz).trans' (by decide)
  have vr : V+E+tiles+1 ≤ 2*n*r := by
    change V+E+tiles+1 ≤ r*n at hrows
    nlinarith
  have index : Nat.clog 2 (V+2*E) ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from public_logWidth n r]
    apply Nat.clog_mono_right
    change V+E+tiles+1 ≤ r*n at hrows
    nlinarith
  have tileLog : Nat.clog 2 tiles ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact Nat.clog_mono_right 2 (show tiles ≤ 2*n*r by omega)
  have depth := depth_le_clog_tiles I l
  change l ≤ Nat.clog 2 tiles+2 at depth
  have lL : l+1 ≤ 4*L := by omega
  have dn : l+2*nWord+1 ≤ (4+2*nWord)*L := by
    have := Nat.le_mul_of_pos_right (2*nWord) hL
    rw [Nat.add_mul]
    omega
  have dat : data ≤ (tags+90*q*(4+2*nWord)+factor*ptr)*L := by
    have old := Nat.mul_le_mul_left (90*q) dn
    have pointer := Nat.mul_le_mul_left ptr hw
    change w ≤ factor*L at hw
    change ptr*w ≤ ptr*(factor*L) at pointer
    have t := Nat.le_mul_of_pos_right tags hL
    nlinarith only [hdata,old,pointer,t]
  have sortLog : Nat.clog 2 (E+tiles*bins) ≤ Nat.clog 2 (bins+1)+L := by
    apply Nat.clog_le_of_le_pow
    have range : E+tiles*bins ≤ (bins+1)*(2*n*r) := by
      have ht : tiles ≤ 2*n*r := by omega
      nlinarith only [vr,Nat.mul_le_mul_left bins ht]
    rw [pow_add,show L = Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact range.trans (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _))
  have kw : keyWidth q l ≤ 360*q*L := by
    change q*(30*(l+1)*3) ≤ _
    nlinarith only [Nat.mul_le_mul_left (90*q) lL]
  have logs := Nat.le_mul_of_pos_right (Nat.clog 2 (bins+1)) hL
  have binLog := Nat.le_mul_of_pos_right (Nat.clog 2 bins) hL
  change w ≤ factor*L at hw
  change _ ≤ Z*L ∧ _ ≤ Z*L ∧ _ ≤ Z*L
  change Nat.clog 2 (E+tiles*bins) ≤ _ at sortLog
  dsimp [Z]
  constructor
  · exact dn.trans (Nat.mul_le_mul_right L (by omega))
  constructor
  · calc
      _ ≤ L+factor*L+(tags+90*q*(4+2*nWord)+factor*ptr)*L+L := by omega
      _ = (tags+90*q*(4+2*nWord)+factor*ptr+factor+2)*L := by ring
      _ ≤ _ := Nat.mul_le_mul_right L (by omega)
  · change Nat.clog 2 (E+tiles*bins)+(Nat.clog 2 bins+keyWidth q l)+w+1 ≤ _
    calc
      _ ≤ (Nat.clog 2 (bins+1)*L+L)+(Nat.clog 2 bins*L+360*q*L)+factor*L+L := by omega
      _ = (Nat.clog 2 (bins+1)+Nat.clog 2 bins+360*q+factor+2)*L := by ring
      _ ≤ _ := Nat.mul_le_mul_right L (by omega)

/-- The same three-address word also holds both successor pointer arrays,
including the seed and band rectangles reserved at this very stage. -/
theorem successorPointers_fit {D m : ℕ} {K : Type*} [Field K] (e : Crossing.PaidIdentity K D m)
    (s : Shape) (V seeds bins r n : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hcap : s.volume V ≤ r*n) (hseeds : seeds ≤ V*bins) (hfixed : sewFactor e bins ≤ n) :
    StaticRows.siteCapacity e s.sites seeds ≤ 2^(3*logWidth r n) ∧
      StaticRows.edgeCapacity e s.edges seeds ≤ 2^(3*logWidth r n) := by
  let U := 2*n*r
  have hU : 1 ≤ U := by dsimp [U]; nlinarith [Nat.mul_le_mul hn hr]
  have hnu : n ≤ U := by dsimp [U]; nlinarith [Nat.mul_le_mul_left n hr]
  have hsu : s.volume V ≤ U := hcap.trans (by dsimp [U]; nlinarith)
  have cap : (s.sew e seeds).volume V ≤ U^2 :=
    (Shape.sew_volume e s bins V seeds hseeds).trans ((Nat.mul_le_mul (hfixed.trans hnu) hsu).trans_eq (sq U).symm)
  have cube : U^2 ≤ 2^(3*logWidth r n) := by
    rw [public_logWidth, mul_comm 3 _,pow_mul]
    exact (Nat.pow_le_pow_right hU (by decide : 2 ≤ 3)).trans
      (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) 3)
  have ht := cap.trans cube
  change StaticRows.siteCapacity e s.sites seeds + StaticRows.edgeCapacity e s.edges seeds + V + 1 ≤ _ at ht
  omega

end Shortening.PublicCapacity

end BorderVNP
end Computability
end OAI
