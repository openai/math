import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Packed ordinary routing on bounded local operand fragments -/

namespace Hierarchy.DescentPackedOperand
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {k : ℕ}

inductive Kind where | carried | cable | pin deriving DecidableEq
def Kind.code : Kind→ℕ | .carried=>0 | .cable=>1 | .pin=>2
def Kind.parse (i : ℕ) := if i=0 then Kind.carried else if i=1 then Kind.cable else Kind.pin

/-- An input is one aligned occurrence. The donor, peer and parallel-cable names
belong to its current local charts. The old alias identifies an entire prior
private word, including its chunk. -/
structure Fragment (k : ℕ) where
  kind : Kind
  donor : Cell (k+2)
  peer : Cell (k+2)
  name : Cell (k+2)
  chunk : Cell (k+2)
  firstCapture : Bool
  secondCapture : Bool
  marked : Bool
  start : Cell (k+2)
  grain : Cell (k+2)

inductive Key where
  | carried (donor oldAlias : ℕ)
  | first (root peer ticket chunk : ℕ)
  | second (root peer ticket chunk : ℕ)
  | cable (peer ticket chunk : ℕ)
  | pin (port chunk : ℕ)
  deriving DecidableEq

def resolve (x : Fragment k) : Key :=
  match x.kind with
  | .carried=>.carried x.donor.val x.name.val
  | .pin=>.pin x.name.val x.chunk.val
  | .cable=>
    if x.firstCapture then .first x.donor.val x.peer.val x.name.val x.chunk.val
    else if x.secondCapture then .second x.donor.val x.peer.val x.name.val x.chunk.val
    else if x.marked then .cable x.peer.val (x.start.val+x.chunk.val/x.grain.val) (x.chunk.val%x.grain.val)
    else .cable x.peer.val x.start.val x.chunk.val

/-- Tags distinguish an inherited alias, each of the two actual captures,
a surviving local peer/cable ticket, and an external port. -/
def Key.fields : Key→Fin 5→ℕ
  | .carried d a=>![0,d,0,a,0]
  | .first d v a j=>![1,d,v,a,j]
  | .second d v a j=>![2,d,v,a,j]
  | .cable v a j=>![3,0,v,a,j]
  | .pin p j=>![4,0,0,p,j]

theorem Key.fields_injective : Function.Injective Key.fields := by
  intro x y eqn
  have a:=congrFun eqn 0
  have b:=congrFun eqn 1
  have c:=congrFun eqn 2
  have d:=congrFun eqn 3
  have e:=congrFun eqn 4
  cases x <;> cases y <;> simp [Key.fields] at a b c d e ⊢ <;> simp_all

private theorem floorRoom (k : ℕ) : 4≤2^(k+2) := by
  exact Nat.pow_le_pow_right (by decide : 0<2) (show 2≤k+2 by omega)

private def flag (k : ℕ) (t : Bool) : Cell (k+2) :=
  ⟨t.toNat,by have:=floorRoom k;cases t <;> simp⟩

def sourceFields (x : Fragment k) : Fin 10→Cell (k+2) :=
  ![⟨x.kind.code,by have:=floorRoom k;cases x.kind <;> simp [Kind.code]; omega⟩,
    x.donor,x.peer,x.name,x.chunk,flag k x.firstCapture,flag k x.secondCapture,flag k x.marked,x.start,x.grain]

def decode (f : Fin 10→Cell (k+2)) : Fragment k :=
  ⟨Kind.parse (f 0).val,f 1,f 2,f 3,f 4,decide ((f 5).val≠0),decide ((f 6).val≠0),
    decide ((f 7).val≠0),f 8,f 9⟩

theorem source_read (x : Fragment k) : decode (sourceFields x)=x := by
  rcases x with ⟨j,d,p,n,c,a,b,m,s,g⟩
  cases j <;> cases a <;> cases b <;> cases m <;> rfl

theorem field_room (x : Fragment k) (j : Fin 5) : (resolve x).fields j<2^(k+4) := by
  have wide : 2^(k+4)=4*2^(k+2) := by rw [show k+4=(k+2)+2 by omega,pow_add];ring
  have u:=floorRoom k
  have a:=x.donor.isLt;have b:=x.peer.isLt;have c:=x.name.isLt
  have t:=x.chunk.isLt;have s:=x.start.isLt
  have q:=Nat.div_le_self x.chunk.val x.grain.val
  have r:=Nat.mod_le x.chunk.val x.grain.val
  cases h : x.kind <;> cases p : x.firstCapture <;> cases l : x.secondCapture <;> cases m : x.marked <;>
    fin_cases j <;> simp [resolve,h,p,l,m,Key.fields,wide] <;> omega

def inputWidth (k : ℕ) := (k+2)*10
def outputWidth (k : ℕ) := (k+4)*5
def packed (x : Fragment k) : Cell (inputWidth k) := encode (k+2) 10 (sourceFields x)
def word (x : Fragment k) : Cell (outputWidth k) :=
  encode (k+4) 5 fun j=>⟨(resolve x).fields j,field_room x j⟩

/-- The common truth table performs the ordinary transition on every possible
local bit pattern; its definition is independent of the private scalar data. -/
def transition (k : ℕ) (v : Cell (inputWidth k)) : Cell (outputWidth k) :=
  word (decode ((encode (k+2) 10).symm v))

theorem transition_read (x : Fragment k) : transition k (packed x)=word x := by
  simp only [transition,packed,Equiv.symm_apply_apply,source_read]

theorem word_read (x : Fragment k) (j : Fin 5) : digit (k+4) j.val (word x).val=(resolve x).fields j :=
  digit_encode _ _

/-- The physical loop operates once per packed occurrence row and returns the
individual five fields of every live occurrence. -/
theorem native (k H r M w : ℕ) (g : Banks) (out : ℕ)
    (fit : Fits g (inputWidth k) (outputWidth k) M H r w out)
    (x : Fin H→Fin r→Fragment k) (positive : 0<M) :
    (program g out H r M w).Spec (PinFrame (M:=M) g (transition k) (fun h i=>packed (x h i)))
      (fun _ m=>∀v j (f : Fin 5),
        digit (k+4) f.val (digit (outputWidth k) (lane j positive).val
          (m (out+(row H r M (position v j positive)).val)).val)=(resolve (x v j)).fields f)
      (4+44*(H*chunks r M)) ∧ ProtocolRAM.CheapCode (program g out H r M w) := by
  obtain ⟨kernel,cheap⟩:=spec g out fit (transition k) (fun h i=>packed (x h i))
  refine ⟨?_,cheap⟩
  apply kernel.mono (fun _ ok=>ok)
  · intro src m stored v j f
    rw [physical_read g out fit (transition k) (fun p i=>packed (x p i)) m stored.2 v j positive,transition_read]
    exact word_read _ _
  · simp [lookup_work,Nat.mul_comm]

/-- One charge per packed row, with one shared dictionary for all sites. -/
theorem price (k H r w : ℕ) (g : Banks) (wide : 2*max (inputWidth k) (outputWidth k)≤w) :
    let M:=lanes w (max (inputWidth k) (outputWidth k))
    (4+44*(H*chunks r M))*w≤4*w+44*(H*w+4*H*r*(max (inputWidth k) (outputWidth k))) ∧
      (2^(inputWidth k*M)+3*(H*chunks r M))*w≤
        2^(w/2)*w+3*(H*w+4*H*r*(max (inputWidth k) (outputWidth k))) := by
  have ha : 0 < inputWidth k := by unfold inputWidth;omega
  have pos : 0 < max (inputWidth k) (outputWidth k) := ha.trans_le (le_max_left ..)
  simpa only [lookup_work,show 2*20+4=44 by decide,Nat.mul_comm (H*chunks r (lanes w (max (inputWidth k) (outputWidth k)))) 44]
    using invoice g H r (inputWidth k) (outputWidth k) w pos wide

end
end Hierarchy.DescentPackedOperand

end OAI
