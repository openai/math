import OAI.Hierarchy.DescentExteriorContent
import OAI.Hierarchy.DescentExteriorPublicPins

namespace OAI
/-! # The exact constant, external, and shared witness pins of the exterior memory image -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentExteriorFetch DescentGL Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.Diagonal TraceBanks
open scoped Classical BigOperators Fin.CommRing
noncomputable section

abbrev Public (e j r t : ℕ) := (Fin e × Plane j r) × Fin t
abbrev Inputs (e j r t : ℕ) := Public e j r t ⊕ Hidden e j r t
variable {w e j r t : ℕ}
local notation "R" => 2^(j+r)
local notation "n" => e*R
local notation "k" => j+(j+r)
local notation "H" => span j r t e
local notation "I" => Fin n

def readBit (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) : Inputs e j r t→Bool :=
  Sum.elim (fun a=>x a.1.1 a.1.2 a.2) z

def inputBit (s : Fin 3) (i : I) (p : Bits j) (b : Fin t) : Inputs e j r t :=
  let v : Plane j r := (p,dest i)
  ![.inl ((slab i,v),b),.inr ((false,slab i,flip v),b),.inr ((true,slab i,flip v),b)] s

def proposedBit (s : Fin 2) (i : I) (p : Bits j) (b : Fin t) : Inputs e j r t :=
  .inr ((phase s,slab i,(p,dest i)),b)

def packedPin {A : Type} (pin : I→Bits j→Fin t→A) (u : ℕ) (b : Fin (w+1)) : A⊕Bool :=
  if hu : u<n then
    if hb : b.val<2^j*t then
      let part:=(pos j t).symm ⟨b.val,hb⟩
      .inl (pin ⟨u,hu⟩ part.1 part.2)
    else .inr false
  else .inr false

theorem packedPin_read {A : Type} (room : 2^j*t≤w) (pin : I→Bits j→Fin t→A) (val : A→Bool)
    (u : ℕ) (b : Fin (w+1)) :
    (packedPin pin u b).elim val id=TraceWords.bits (wide
      (padWord (fun i:I=>((pack (fun p q=>val (pin i p q))).val:Word w)) u)) b := by
  by_cases hu:u<n
  · let v:=pack (fun p q=>val (pin ⟨u,hu⟩ p q))
    have fit:=v.isLt.trans_le (Nat.pow_le_pow_right (by decide) room)
    simp only [packedPin,dite_eq_left hu,padWord,TraceWords.bits,wide]
    change _=(v.val%2^w).testBit b.val
    rw [Nat.mod_eq_of_lt fit]
    by_cases hb:b.val<2^j*t
    · rw [dite_eq_left hb]
      let l : Fin (2^j*t):=⟨b.val,hb⟩
      rw [show v.val.testBit b.val=wordBits _ v l from Computability.VPVNP.LiveHeader.testBit_wordBits v l]
      change val (pin ⟨u,hu⟩ ((pos j t).symm l).1 ((pos j t).symm l).2)=
        wordBits (2^j*t) (pack (fun p q=>val (pin ⟨u,hu⟩ p q))) l
      simp only [pack,Equiv.apply_symm_apply]
    · rw [dite_eq_right hb]
      exact (Nat.testBit_lt_two_pow (v.isLt.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hb)))).symm
  · simp [packedPin,padWord,hu,TraceWords.bits,wide]

def wires (i : Fin 17) (u : ℕ) (b : Fin (w+1)) : Inputs e j r t ⊕ Bool :=
  let literal (a : Fin 17) : Inputs e j r t ⊕ Bool := Sum.inr (TraceWords.bits (wide (columnWords (t:=t) (r:=r) (j:=j) (e:=e)
    (fun _=>LinearEquiv.refl _ _) (fun _ _ _=>false) (fun _=>false) a u : Word w)) b)
  ![literal 0,literal 1,literal 2,literal 3,literal 4,literal 5,literal 6,literal 7,literal 8,
    packedPin (inputBit 0) u b,packedPin (inputBit 1) u b,packedPin (inputBit 2) u b,
    literal 12,literal 13,literal 14,packedPin (proposedBit 0) u b,packedPin (proposedBit 1) u b] i

set_option maxHeartbeats 1500000 in
theorem wires_read (room : 2^j*t≤w) (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool)
    (i : Fin 17) (u : ℕ) (b : Fin (w+1)) :
    (wires i u b).elim (readBit x z) id=
      TraceWords.bits (wide (columnWords (fun _=>LinearEquiv.refl _ _) x z i u)) b := by
  have raw (s : Fin 3) := packedPin_read (e:=e) (j:=j) (r:=r) (t:=t)
    room (inputBit s) (readBit x z) u b
  have guess (s : Fin 2) := packedPin_read (e:=e) (j:=j) (r:=r) (t:=t)
    room (proposedBit s) (readBit x z) u b
  let column (a : Fin 17) : Prop :=
    (wires a u b).elim (readBit x z) id =
      TraceWords.bits (wide (columnWords (fun _=>LinearEquiv.refl _ _) x z a u)) b
  change column i
  fin_cases i
  case' «0» => change column 0
  case' «1» => change column 1
  case' «2» => change column 2
  case' «3» => change column 3
  case' «4» => change column 4
  case' «5» => change column 5
  case' «6» => change column 6
  case' «7» => change column 7
  case' «8» => change column 8
  case' «9» => change column 9
  case' «10» => change column 10
  case' «11» => change column 11
  case' «12» => change column 12
  case' «13» => change column 13
  case' «14» => change column 14
  case' «15» => change column 15
  case' «16» => change column 16
  all_goals simp only [column,wires,columnWords,Matrix.cons_val,Sum.elim_inr,id_eq]
  case «9» => exact raw 0
  case «10» => exact raw 1
  case «11» => exact raw 2
  case «15» => exact guess 0
  case «16» => exact guess 1

/-- After the constant initial image only the matrix bank is updated
by the previous stages. Both permutations of every guessed bit are wired
before any dynamic layout or exterior value has been selected. -/
def initialPin (a : Fin (17*H)) (b : Fin (w+1)) : Inputs e j r t ⊕ Bool :=
  wires (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2.val b

theorem initial_read (room : 2^j*t≤w) (origin : ℕ) (m : Memory w) (x : Fin e→Plane j r→Fin t→Bool)
    (z : Hidden e j r t→Bool) (a : Fin (17*H)) (b : Fin (w+1)) :
    (initialPin a b).elim (readBit x z) id = TraceWords.bits (wide
      (staged origin (fun _=>LinearEquiv.refl _ _) x z m (origin+a.val))) b := by
  obtain ⟨⟨i,u⟩,rfl⟩:=finProdFinEquiv.surjective a
  have eq : origin+(finProdFinEquiv (i,u)).val=(bank j r t e origin i.val).base+u.val := by
    change origin+(u.val+H*i.val)=origin+i.val*H+u.val;ring
  rw [eq,staged,store_read]
  simpa [initialPin] using wires_read room x z i u.val b

end
end Hierarchy.DescentExteriorShelf

end OAI
