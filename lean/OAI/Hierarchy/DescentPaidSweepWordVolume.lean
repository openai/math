import OAI.Hierarchy.DescentPackedChunkWork
import OAI.Hierarchy.DescentOrdinaryOverlapReserve

namespace OAI
/-! # Word-scaled charge for the two native publication scans and one old-pitch transfer -/
namespace Hierarchy.DescentPaidResidentCount.WordVolume
open DescentSIMDLookup DescentDatedSeedStartup
variable (B D p t : ℕ)

def oldCost := 2*B*t+2052*B
def newCost := 2066*B+112*D+120*p+6
def fixedCost := 28*B*t+358*B+1568*D+1730*p+3029
def rowRate := oldCost B t+newCost B D p
def tableRate := fixedCost B D p t+4096+230*D+460*p+230

def expanded (oldRows newRows overlapEntries census masks sums : ℕ) :=
  oldCost B t*oldRows+newCost B D p*newRows+2048*overlapEntries+
    230*D*census+460*p*masks+230*sums+fixedCost B D p t

/-- Occupancy may be weaker than a full preceding word at either pitch. The single
    incomplete group of each physical host is charged once; lookup tables are independent
    of the number of old hosts and groups. -/
theorem charged (H G A M b roc moc soc h w ratio u₀ u₁ : ℕ)
    (word : w≤ratio*h) (source : A≤h) (target : M≤h) (oldBits : b*A≤h/2)
    (census : roc≤h/2) (masks : moc≤h/2) (sums : soc≤h/2)
    (fill₀ : h≤A*u₀) (fill₁ : h≤M*u₁) :
    expanded B D p t (H*chunks G A) (H*chunks G M)
        ((Overlap.pieces G A M+1)*(A+1)*2^(b*A)) (2^roc) (2^moc) (2^soc)*w≤
      ratio*(rowRate B D p t*(H*h+H*G*(u₀+u₁))+
        tableRate B D p t*((h+1)^2*2^(h/2)*h)) :=by
  let work:=H*h+H*G*(u₀+u₁)
  let reserve_:=(h+1)^2*2^(h/2)*h
  have one : 1≤(h+1)^2:=Nat.succ_le_of_lt (by positivity : 0<(h+1)^2)
  have scale : 2^(h/2)≤(h+1)^2*2^(h/2):=by simpa using Nat.mul_le_mul_right (2^(h/2)) one
  have price_ (c : ℕ) (limit : c≤h/2) : 2^c*h≤reserve_ :=
    Nat.mul_le_mul_right _ ((Nat.pow_le_pow_right (by decide : 0<2) limit).trans scale)
  have baseCost : h≤reserve_ := by simpa using price_ 0 (Nat.zero_le _)
  have before : (H*chunks G A)*h≤work := (chunk_work H G A h u₀ fill₀).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_right u₀ u₁)) _)
  have after_ : (H*chunks G M)*h≤work := (chunk_work H G M h u₁ fill₁).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_left u₁ u₀)) _)
  let copies:=(Overlap.pieces G A M+1)*(A+1)*2^(b*A)
  have setup : copies*h≤2*reserve_ := by
    simpa only [copies,reserve_,Nat.mul_assoc] using Nat.mul_le_mul_right h
      (Overlap.half_pages h G A M b source target oldBits)
  let total:=expanded B D p t (H*chunks G A) (H*chunks G M) copies (2^roc) (2^moc) (2^soc)
  have occ := Nat.add_le_add
    (Nat.mul_le_mul_left (oldCost B t) before) (Nat.mul_le_mul_left (newCost B D p) after_)
  have both := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add occ (Nat.mul_le_mul_left 2048 setup)) (Nat.mul_le_mul_left (230*D) (price_ roc census)))
    (Nat.mul_le_mul_left (460*p) (price_ moc masks))) (Nat.mul_le_mul_left 230 (price_ soc sums)))
    (Nat.mul_le_mul_left (fixedCost B D p t) baseCost)
  calc
    total*w ≤ total*(ratio*h) := Nat.mul_le_mul_left _ word
    _ = ratio*(total*h) := by ring
    _ ≤ ratio*(rowRate B D p t*work+tableRate B D p t*reserve_) :=by
      apply Nat.mul_le_mul_left
      convert both using 1 <;> dsimp only [total,expanded,rowRate,tableRate] <;> ring

end Hierarchy.DescentPaidResidentCount.WordVolume

end OAI
