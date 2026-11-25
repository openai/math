import OAI.Hierarchy.DescentSharedCableSerial

namespace OAI
/-! # The physical fields and encoding of a short signed cable word -/
namespace Hierarchy.DescentSharedCableNames.Stage
open DescentSIMDLookup
open scoped Fin.CommRing

structure Live (D cap : ℕ) where
  neighbor : Fin D
  wire : Fin cap
  sourceWire : Fin cap
  within : Fin cap
  target : Bool
  markedOut : Bool

def censusTag {D cap : ℕ} : Option (Live D cap)→Cell 2
  | none=>0
  | some u=>if u.markedOut then 3 else 1

end Hierarchy.DescentSharedCableNames.Stage

namespace Hierarchy.DescentSignedCableCodec
open DescentSIMDLookup DescentSharedCableNames Stage
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {D cap : ℕ}

def pair (a b : ℕ) : Cell a × Cell b ≃ Cell (a+b) :=finProdFinEquiv.trans (finCongr (pow_add 2 a b).symm)
def width (D cap : ℕ) := Packed.bits D+(Packed.bits cap+(Packed.bits cap+(Packed.bits cap+2)))

def bits (target marked : Bool) : Cell 2:=finProdFinEquiv (finTwoEquiv.symm target,finTwoEquiv.symm marked)

def encode (x : Option (Live D cap)) : Cell (width D cap) :=
  pair _ _ (Packed.token (x.map Live.neighbor),pair _ _ (Packed.token (x.map Live.wire),
    pair _ _ (Packed.token (x.map Live.sourceWire),pair _ _ (Packed.token (x.map Live.within),
      bits (x.elim false Live.target) (x.elim false Live.markedOut)))))

def decode (D cap : ℕ) (c : Cell (width D cap)) : Option (Live D cap) :=do
  let k:=Packed.bits cap
  let a:=(pair (Packed.bits D) (k+(k+(k+2)))).symm c
  let b:=(pair k (k+(k+2))).symm a.2
  let t:=(pair k (k+2)).symm b.2
  let u:=(pair k 2).symm t.2
  let flag : Fin 2×Fin 2:=finProdFinEquiv.symm u.2
  let near←Packed.readToken D a.1
  let serial←Packed.readToken cap b.1
  let wire←Packed.readToken cap t.1
  let grain←Packed.readToken cap u.1
  return ⟨near,serial,wire,grain,finTwoEquiv flag.1,finTwoEquiv flag.2⟩

@[simp] theorem decode_encode (x : Option (Live D cap)) : decode D cap (encode x)=x :=by
  cases x with
  | none=>simp [encode,decode,bits]
  | some t=>cases t;simp [encode,decode,bits]

def census (c : Cell (width D cap)) : Cell 2:=censusTag (decode D cap c)
def neighbor (c : Cell (width D cap)) : Cell (Packed.bits D):=Packed.token ((decode D cap c).map Live.neighbor)
@[simp] theorem census_at (x : Option (Live D cap)) : census (encode x)=censusTag x :=by simp [census]
@[simp] theorem neighbor_at (x : Option (Live D cap)) : neighbor (encode x)=Packed.token (x.map Live.neighbor) :=by simp [neighbor]

/-- A ghost cell is represented by one shared constant. -/
theorem empty : encode (none : Option (Live D cap))=0 :=by
  have zeroPair {a b : ℕ} [NeZero a] [NeZero b] :
      finProdFinEquiv ((0 : Fin a),(0 : Fin b))=(0 : Fin (a*b)) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val,Fin.val_zero,Nat.mul_zero,Nat.add_zero]
  apply Fin.ext
  simp [encode,pair,bits,Packed.token,finTwoEquiv,zeroPair]

@[simp] theorem census_zero (D cap : ℕ) : census (0 : Cell (width D cap))=0 := by
  rw [←empty,census_at]
  rfl

end
end Hierarchy.DescentSignedCableCodec

end OAI
