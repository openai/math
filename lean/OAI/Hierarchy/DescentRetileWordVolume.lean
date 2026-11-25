import OAI.Hierarchy.DescentOrdinaryOverlapReserve
import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! # The two public ordinary operand and primitive-role retile bills at physical word cost -/
namespace Hierarchy.DescentSIMDLookup.Overlap

theorem page_word_rows (H G A B bits pages h w ratio u₀ u₁ cost : ℕ)
    (live : 0<H) (a : A≤h) (b : B≤h) (table : bits*A≤h/2)
    (before : H*chunks G A*h≤H*h+H*G*u₀) (after : h≤B*u₁) (bus : w≤ratio*h)
    (original : cost≤4096*((pieces G A B+1)*(A+1)*2^(bits*A)+
      (pages+1)*(H*chunks G A+H*chunks G B+pieces G A B+1))) :
    cost*w≤4096*ratio*(pages+1)*(h+3*H*h+H*G*(2*u₀+u₁))+
      (4096*ratio)*(2*(h+1)^2*2^(h/2))*h := by
  let n:=H*chunks G A
  let m:=H*chunks G B
  let Q:=(pieces G A B+1)*(A+1)*2^(bits*A)
  have short : Q≤2*(h+1)^2*2^(h/2):=half_pages h G A B bits a b table
  have piece : pieces G A B≤n:=(Nat.min_le_left ..).trans (Nat.le_mul_of_pos_left _ live)
  have first:=before
  have last :=DescentDatedSeedStartup.chunk_work H G B h u₁ after
  change n*h≤H*h+H*G*u₀ at first
  change m*h≤H*h+H*G*u₁ at last
  have count : (n+m+pieces G A B+1)*h≤h+3*H*h+H*G*(2*u₀+u₁) := by
    calc
      _ ≤ (n+m+n+1)*h :=Nat.mul_le_mul_right _ (by omega)
      _ = h+n*h+m*h+n*h :=by ring
      _ ≤ h+(H*h+H*G*u₀)+(H*h+H*G*u₁)+(H*h+H*G*u₀) :=by gcongr
      _ = _ :=by ring
  change cost≤4096*(Q+(pages+1)*(n+m+pieces G A B+1)) at original
  calc
    _ ≤ (4096*(Q+(pages+1)*(n+m+pieces G A B+1)))*(ratio*h) :=Nat.mul_le_mul original bus
    _ = 4096*ratio*(pages+1)*((n+m+pieces G A B+1)*h)+(4096*ratio)*Q*h :=by ring
    _ ≤ _ :=by gcongr

theorem page_word_bill (H G A B bits pages h w ratio u₀ u₁ cost : ℕ)
    (live : 0<H) (a : A≤h) (b : B≤h) (table : bits*A≤h/2)
    (before : h≤A*u₀) (after : h≤B*u₁) (bus : w≤ratio*h)
    (original : cost≤4096*((pieces G A B+1)*(A+1)*2^(bits*A)+
      (pages+1)*(H*chunks G A+H*chunks G B+pieces G A B+1))) :
    cost*w≤4096*ratio*(pages+1)*(h+3*H*h+H*G*(2*u₀+u₁))+
      (4096*ratio)*(2*(h+1)^2*2^(h/2))*h :=
  page_word_rows H G A B bits pages h w ratio u₀ u₁ cost live a b table
    (DescentDatedSeedStartup.chunk_work H G A h u₀ before) after bus original

end Hierarchy.DescentSIMDLookup.Overlap

end OAI
