import OAI.Hierarchy.DescentDonorWordScale
import OAI.Hierarchy.DescentDonorExponentBounds

namespace OAI
/-! # Uniform numerical exponents of the authentic ordinary donor geometry -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentHostDegree

private structure Point (t gain Dmax : ℕ) where
  age : ℕ
  degree : ℕ
  cap : ℕ
  degree_bound : degree≤Dmax
  cap_bound : cap≤2^(8+gain*((t+1)*age))

def venueGrade (r degree cap : ℕ) :=
  16384*((31+(r+(r*(2*cap)+degree*r))*56)+1+(degree+10)^8)

def donorGrade (r degree cap : ℕ) :=
  800*(max r (max (degree+1) (max cap (2*r))))^4+25*(2*(5+(r*(2*cap)+(degree+1+1)))+3+2*r)+200+venueGrade r degree cap

def donorAmount (k degree cap b C pad : ℕ) :=
  AgeBound.laneAmount (2^k) degree cap (max (k+3) (Nat.clog 2 (degree+1)))
    (Nat.clog 2 (2^(k+1)*(2^(packExponent 20 degree)+2))) (Nat.clog 2 (max (cap*b) (C+1+pad)+1))
    (Nat.clog 2 ((C+2)^8))

/-- Both exponents are selected before the tail, precision or actual branch. -/
theorem donor_uniform (t host gain cut Dmax b C pad : ℕ) :
    ∃s a : ℕ,∀J D cap : ℕ,D≤Dmax→cap≤2^(8+gain*((t+1)*J))→
      let k:=groupBits t J host gain cut
      donorGrade (2^k) D cap≤ scale J s ∧ donorAmount k D cap b C pad≤ scale J a := by
  let I:=Point t gain Dmax
  let age:I→ℕ:=Point.age
  let k:=fun x:I=>groupBits t (age x) host gain cut
  let r:=fun x:I=>2^(k x)
  let d:I→ℕ:=Point.degree
  let q:I→ℕ:=Point.cap
  have rad : AgeBound age r := AgeBound.radix t host gain cut
  have dim : AgeBound age k :=rad.mono (fun x=>Nat.lt_two_pow_self.le)
  have deg : AgeBound age d :=(AgeBound.const age Dmax).mono Point.degree_bound
  have caps : AgeBound age q :=AgeBound.dated_cap (i:=fun x=>(t+1)*age x) (fun _=>le_refl _)
    (fun x=>x.cap_bound)
  have tall:=rad.maximum ((deg.add (AgeBound.const age 1)).maximum (caps.maximum ((AgeBound.const age 2).mul rad)))
  have charged:=(AgeBound.const age 800).mul (tall.pow 4)
  have codes := (AgeBound.const age 5).add
    ((rad.mul ((AgeBound.const age 2).mul caps)).add ((deg.add (AgeBound.const age 1)).add (AgeBound.const age 1)))
  have tables := (((AgeBound.const age 2).mul codes).add (AgeBound.const age 3)).add ((AgeBound.const age 2).mul rad)
  have terrain := (AgeBound.const age 31).add
    ((rad.add ((rad.mul ((AgeBound.const age 2).mul caps)).add (deg.mul rad))).mul (AgeBound.const age 56))
  have venue :=(AgeBound.const age 16384).mul ((terrain.add (AgeBound.const age 1)).add ((deg.add (AgeBound.const age 10)).pow 8))
  have work : AgeBound age (fun x=>donorGrade (r x) (d x) (q x)) :=
    ((charged.add ((AgeBound.const age 25).mul tables)).add (AgeBound.const age 200)).add venue
  have raw := (dim.add (AgeBound.const age 3)).maximum (AgeBound.clog (deg.add (AgeBound.const age 1)))
  have fields : AgeBound age (fun x=>donorAmount (k x) (d x) (q x) b C pad) :=
    AgeBound.normalized_amount rad deg caps raw (AgeBound.ranked_labels dim deg)
      (AgeBound.const age (Nat.clog 2 ((C+2)^8))) b C pad
  obtain ⟨s,fee⟩:=work
  obtain ⟨a,words⟩:=fields
  exact ⟨s,a,fun J D cap bounded room=>⟨fee ⟨J,D,cap,bounded,room⟩,words ⟨J,D,cap,bounded,room⟩⟩⟩

end Hierarchy.DescentCompiler.TerminalScale

end OAI
