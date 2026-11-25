import OAI.Hierarchy.DescentZipBook
import OAI.Hierarchy.DescentResidentDonorFields
import OAI.Hierarchy.DescentDonorLayoutBit

namespace OAI
/-! # Actual binary gates installed once for the ordinary donor census -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Binary
open DescentPackedZip DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentSIMDLookup
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable (s : DepotRAM.Shape)
local notation "r" => rawBits s
local notation "c" => cableBits s
local notation "o" => ownerBits s
local notation "h" => chartBits s
local notation "f" => freshBits s
local notation "N" => s.blocks*(2*s.cap)
local notation "D" => s.degree+1
local notation "cb" => DescentSignedCableCodec.width s.degree s.cap
local notation "ob" => (Owners.digits s.blocks s.degree s.short*3)*s.blocks
local notation "ub" => s.short*«fields» s.blocks s.degree (2*s.cap)

def concat (a b : ℕ) : Book.Gate := ⟨a,b,a+b,fun x y=>pair a b (x,y)⟩

def gather : Fin 5→Book.Gate :=
  ![concat r c,concat o h,concat h f,concat (r+c) (o+h),concat ((r+c)+(o+h)) (h+f)]

abbrev Kind := Fin 5⊕(Fin N⊕(Fin D⊕Fin 1))
def count := 5+(N+(D+1))

def ordinal : Kind s≃Fin (count s) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

def gates : Kind s→Book.Gate
  | .inl i=>gather s i
  | .inr (.inl i)=>⟨cb*N,cb,cb*N,Gather.setField i⟩
  | .inr (.inr (.inl i))=>⟨ob*D,ob,ob*D,Gather.setField i⟩
  | .inr (.inr (.inr _))=>⟨1,ub,1+ub,Owners.LayoutBit.join ub⟩

def menu (i : Fin (count s)) := gates s ((ordinal s).symm i)

@[simp] theorem menu_at (i : Kind s) : menu s (ordinal s i)=gates s i := by simp [menu]

theorem width (i : Kind s) : (gates s i).left+(gates s i).right≤2*totalBits s+1 := by
  rcases i with i|(i|(i|_))
  · fin_cases i <;> simp [gates,gather,concat,totalBits] <;> omega
  · change cb*N+cb≤_
    have used : 0<N:=Nat.zero_lt_of_lt i.isLt
    have order:=Nat.le_mul_of_pos_right cb used
    change cb*N+cb≤2*(((r+cb*N)+(ob*D+h))+(h+f))+1
    omega
  · have ord:=Nat.le_mul_of_pos_right ob (Nat.succ_pos s.degree)
    change ob≤ob*D at ord
    change ob*D+ob≤2*(((r+c)+(ob*D+h))+(h+f))+1
    omega
  · change 1+ub≤2*((((1+ub)+c)+(o+h))+(h+f))+1
    omega

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Binary

end OAI
