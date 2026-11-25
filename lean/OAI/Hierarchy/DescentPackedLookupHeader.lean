import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Immutable lookup and padding tables for packed lanes -/
namespace Hierarchy.DescentPackedFallbackTree.Image
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {a b w : ℕ}
def literal (f : Cell a→Cell b) (M w : ℕ) (i : Cell (a*M)) : Word w := (table f i).val

/-- A fixed immutable header interval, with the padding masks immediately after its dictionary. -/
def banks (a : ℕ) (source : Bank) (lo maskBits M : ℕ) : Banks :=
  ⟨source,⟨lo,a*M⟩,⟨lo+2^(a*M),maskBits⟩⟩

def header (f : Cell a→Cell b) (H G M w lo : ℕ) (m : Memory w) (addr : ℕ) : Word w :=
  let D:=2^(a*M)
  let N:=H*chunks G M
  if _left : addr<lo then m addr else
    if dict : addr-lo<D then literal f M w ⟨_,dict⟩ else
      if p : addr-(lo+D)<N then (maskWord b M G ((row H G M).symm ⟨_,p⟩).2.val:ℕ) else m addr

theorem header_dictionary (f : Cell a→Cell b) (H G M w lo : ℕ) (m : Memory w) (i : Cell (a*M)) :
    header f H G M w lo m (lo+i.val)=literal f M w i := by simp [header,Nat.not_lt.mpr (Nat.le_add_right lo i.val),i.isLt]

theorem header_mask (f : Cell a→Cell b) (H G M w lo : ℕ) (m : Memory w) (i : Fin (H*chunks G M)) :
    header f H G M w lo m (lo+2^(a*M)+i.val)=
      (maskWord b M G ((row H G M).symm i).2.val:Word w) := by
  have h:=Nat.not_lt.mpr ((Nat.le_add_right lo (2^(a*M))).trans (Nat.le_add_right _ i.val))
  have k : lo+2^(a*M)+i.val-lo=2^(a*M)+i.val := by omega
  have outside:=Nat.not_lt.mpr (Nat.le_add_right (2^(a*M)) i.val)
  simp [header,h,k,outside,i.isLt]

def resident (f : Cell a→Cell b) (g : Banks) (H G M : ℕ) (m : Memory w) : Prop :=
  (∀i : Cell (a*M),m (g.dictionary.base+i.val)=literal f M w i) ∧
    ∀p : Fin (H*chunks G M),m (g.mask.base+p.val)=(maskWord b M G ((row H G M).symm p).2.val:Word w)

theorem resident_header (f : Cell a→Cell b) (source : Bank) (lo mb H G M w : ℕ) (m : Memory w) :
    resident f (banks a source lo mb M) H G M (header f H G M w lo m) :=
  ⟨header_dictionary f H G M w lo m,header_mask f H G M w lo m⟩


def imageBank (H G M out : ℕ) (g : Banks) (m : Memory w) :=
  image out (H*chunks G M) (DescentSIMDLookup.lookup g) m

end
end Hierarchy.DescentPackedFallbackTree.Image

end OAI
