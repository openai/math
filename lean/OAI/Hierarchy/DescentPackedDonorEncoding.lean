import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # The fixed bit encoding of an original donor chip and its measured supply fields -/
namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {loc a c : ℕ}

def pair (a b : ℕ) : Cell a×Cell b ≃ Cell (a+b) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 a b).symm)

def tag (b : Bool) : Cell 1 := ⟨b.toNat,by cases b <;> decide⟩
def flag (v : Cell 1) : Bool := decide (v.val=1)
@[simp] theorem flag_tag (b : Bool) : flag (tag b)=b := by cases b <;> decide

/-- All five endpoint terms use the same bounded local host chart. The eight
supply multiplicities are the genuine chosen profile in units of z. -/
structure Donor (loc a c : ℕ) where
  live : Bool
  picked : Bool
  first : Bool
  layout : Bool
  left : Cell (loc+1+a)
  right : Cell (loc+1+a)
  anchors : Fin 3→Cell (loc+1+a)
  oldUnits : Cell c
  armUnits : Cell c
  supplyUnits : Fin 8→Cell c

def bundleBits (loc a c : ℕ) := 4+5*(loc+1+a)+10*c

def gateTag (d : Donor loc a c) : Fin 4→Cell 1 := ![tag d.live,tag d.picked,tag d.first,tag d.layout]
def legs (d : Donor loc a c) : Fin 5→Cell (loc+1+a) :=
  Fin.append (m:=2) (n:=3) ![d.left,d.right] d.anchors
def powers (d : Donor loc a c) : Fin 10→Cell c := Fin.append (m:=2) (n:=8) ![d.oldUnits,d.armUnits] d.supplyUnits

theorem shapeWidth (loc a c : ℕ) : ((4+(loc+1+a)*5)+c*10)=bundleBits loc a c := by unfold bundleBits;ring

def packDonor (d : Donor loc a c) : Cell (bundleBits loc a c) :=
  (finCongr (congrArg (2^·) (shapeWidth loc a c))) (pair (4+(loc+1+a)*5) (c*10)
    (pair _ _ (encode 1 4 (gateTag d),encode (loc+1+a) 5 (legs d)),encode c 10 (powers d)))

def unpackDonor (x : Cell (bundleBits loc a c)) : Donor loc a c :=
  let word:=(finCongr (congrArg (2^·) (shapeWidth loc a c))).symm x
  let fields:=(pair (4+(loc+1+a)*5) (c*10)).symm word
  let terms:=(pair 4 ((loc+1+a)*5)).symm fields.1
  let f:=(encode 1 4).symm terms.1
  let e:=(encode (loc+1+a) 5).symm terms.2
  let n:=(encode c 10).symm fields.2
  ⟨flag (f 0),flag (f 1),flag (f 2),flag (f 3), e 0,e 1,fun j=>e (Fin.natAdd 2 j),
    n 0,n 1,fun j=>n (Fin.natAdd 2 j)⟩

@[simp] theorem unpack_pack (d : Donor loc a c) : unpackDonor (packDonor d)=d := by
  rcases d with ⟨live,picked,first,layout,left,right,anchors,oldUnits,armUnits,supply⟩
  simp [unpackDonor,packDonor,gateTag,legs,powers,Fin.append,Fin.addCases]
  constructor
  · funext j
    rw [dite_eq_right (show ¬2+j.val≤1 by omega)]
    apply congrArg anchors
    apply Fin.ext
    change 2+j.val-2=j.val
    omega
  · funext j
    rw [dite_eq_right (show ¬2+j.val≤1 by omega)]
    apply congrArg supply
    apply Fin.ext
    change 2+j.val-2=j.val
    omega

end
end Hierarchy.DescentRawCablePanel

end OAI
