import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentColonyLayout
import OAI.Hierarchy.DescentWalshPhysical

namespace OAI
/-! # Short signed Walsh butterfly on two packed source words, including intra-word partners -/

namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup
open scoped Classical Fin.CommRing BigOperators
noncomputable section

abbrev Cube (k : ℕ) := Fin k→Bool
abbrev Axis (hi lo : ℕ) := Fin hi ⊕ Fin lo

/-- The old graph stores the first spatial coordinate in the most significant bit. -/
def ordinal (k : ℕ) : Cube k ≃ Fin (2^k) :=
  (DescentWalshPhysical.coordinates k).symm.trans (DescentColonies.address k)

def above {h l : ℕ} (a : Axis h l) (p : Cube h) (flag : Bool) : Cube h :=
  match a with | .inl j=>Function.update p j flag | .inr _=>p

def below {h l : ℕ} (a : Axis h l) (p : Cube l) (flag : Bool) : Cube l :=
  match a with | .inl _=>p | .inr j=>Function.update p j flag

def upperSign {h l : ℕ} (a : Axis h l) (p : Cube h) : Bool :=
  match a with | .inl j=>p j | .inr _=>false

def subtractAt {h l : ℕ} (a : Axis h l) (up : Bool) (p : Cube l) : Bool :=
  match a with | .inl _=>up | .inr i=>p i

def step {h l b : ℕ} (a : Axis h l) (x : Cube h→Cube l→Cell b) (p : Cube h) (q : Cube l) : Cell b :=
  let low:=x (above a p false) (below a q false)
  let high:=x (above a p true) (below a q true)
  if subtractAt a (upperSign a p) q then low-high else low+high

def chunk {l b : ℕ} (x : Cube l→Cell b) : Cell (b*2^l) :=
  encode b (2^l) (fun j=>x ((ordinal l).symm j))

def rowResult {h l b : ℕ} (a : Axis h l) (up : Bool) (x y : Cell (b*2^l)) : Cell (b*2^l) :=
  chunk (fun q=>
    let u:=(encode b (2^l)).symm x (ordinal l (below a q false))
    let v:=(encode b (2^l)).symm y (ordinal l (below a q true))
    if subtractAt a up q then u-v else u+v)

theorem row_correct {h l b : ℕ} (a : Axis h l) (x : Cube h→Cube l→Cell b) (p : Cube h) :
    rowResult a (upperSign a p) (chunk (x (above a p false))) (chunk (x (above a p true)))=
      chunk (step a x p) := by
  unfold rowResult
  apply congrArg chunk
  funext q
  simp [chunk,step]

def sideKey (t : Bool) : Cell 1 := if t then 1 else 0

theorem sideKey_val (t : Bool) : (sideKey t).val=t.toNat := by cases t <;> decide

def signPair (bits : ℕ) : Cell 1 × Cell bits ≃ Cell (1+bits) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_add]))

def record (b l : ℕ) (upper : Bool) (x y : Cell (b*2^l)) : Cell (1+(b+b)*2^l) :=
  signPair ((b+b)*2^l) (sideKey upper,DescentPackedZip.key b b (2^l) (x,y))

def dictionary {h l b : ℕ} (a : Axis h l) (i : Cell (1+(b+b)*2^l)) : Cell (b*2^l) :=
  let outer := (signPair ((b+b)*2^l)).symm i
  let words := (DescentPackedZip.key b b (2^l)).symm outer.2
  rowResult a (outer.1.val != 0) words.1 words.2

theorem record_read {h l b : ℕ} (a : Axis h l) (s : Bool) (x y : Cell (b*2^l)) :
    dictionary a (record b l s x y)=rowResult a s x y := by
  cases s <;> simp [dictionary,record,sideKey]

theorem record_val {b l : ℕ} (up : Bool) (x y : Cell (b*2^l)) :
    (record b l up x y).val=2^((b+b)*2^l)*up.toNat+(y.val+2^(b*2^l)*x.val) := by
  change (DescentPackedZip.key b b (2^l) (x,y)).val+2^((b+b)*2^l)*(sideKey up).val=_
  rw [DescentPackedZip.key_val,sideKey_val,Nat.add_comm]

end
end Hierarchy.DescentPackedWalsh

end OAI
