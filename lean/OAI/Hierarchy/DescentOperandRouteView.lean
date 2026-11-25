import OAI.Hierarchy.DescentOrdinaryNodeArguments
import OAI.Hierarchy.DescentHiddenOrder
import OAI.Hierarchy.DescentOperandRouteRAM

namespace OAI
/-! # The numbers printed for a scalar's actual bound variable, cable, or external port -/

namespace Hierarchy.DescentOperandRouteRAM
open Computability.BorderVNP.Crossing DescentKernelHistory DescentKernelHistory.NodeOrder
open DescentNetworkPartition DescentHistoryOrder DescentCableUnbundling
open scoped Classical
noncomputable section

variable {E E' U P V : Type} [Fintype V] {D d : ℕ} {bits : P→ℕ}
variable (N : Network D P bits) (r : SiteBits (U:=U) N)

def view (ports : P→ℕ) (privateId : Hidden N r→ℕ) (v : N.Site) :
    BitRef (boundaryWidth N v) ⊕ BitRef (r v).hiddenWidth → Ref N.Edge × ℕ
  | .inl ⟨.inl e,t⟩=>(.cable e.val,t.val)
  | .inl ⟨.inr p,t⟩=>(.port (ports p.val),t.val)
  | .inr ⟨h,t⟩=>(.hidden (privateId ⟨v,h⟩),t.val)

def numbered (ord : E→ℕ) : Ref E × ℕ→Ref ℕ × ℕ
  | (.cable e,t)=>(.cable (ord e),t)
  | (.port p,t)=>(.port p,t)
  | (.hidden h,t)=>(.hidden h,t)

variable (loc : N.Site→V) (pos : V→EuclideanSpace ℝ (Fin d)) (ball : ∀v,‖pos v‖≤1)
local notation "Q" => quotient N loc pos ball
local notation "qr" => quotientBits N loc pos ball r

def occupiedStep (edge : N.Edge→ℕ) : Ref N.Edge × ℕ→Ref ℕ × ℕ
  | (.cable e,t)=>if loc (N.src e)=loc (N.dst e) then (.hidden (2*edge e),t) else (.cable (edge e),t)
  | (.hidden h,t)=>(.hidden (2*h+1),t)
  | (.port p,t)=>(.port p,t)

/-- At each of the actual quotients the numerical test is equality of the two owners,
and the private tag is the real parity tag of the quotient history. -/
theorem occupied_read (ports : P→ℕ) (edge : N.Edge↪ℕ) (old : Hidden N r↪ℕ)
    (v : V) (u : {s //loc s=v})
    (x : BitRef (boundaryWidth N u.val) ⊕ BitRef (r u.val).hiddenWidth) :
    numbered (fun e : (Q).Edge=>edge e.val)
        (view (Q) (qr) ports (quotientHidden N r loc pos ball edge old) v (NodeOrder.quotientRef N loc pos ball r v u x)) =
      occupiedStep N loc edge (view N r ports old u.val x) := by
  rcases x with ⟨e|p,t⟩|⟨h,t⟩
  · by_cases collapsed : loc (N.src e.val)=loc (N.dst e.val) <;>
      simp [view,numbered,occupiedStep,NodeOrder.quotientRef,DescentKernelHistory.quotientBit,collapsed]; rfl
  · rfl
  · cases u with | mk u eqn=>subst v;rfl

variable (core : Finset N.Edge) (multiplicity : N.Edge→ℕ) (grain : ℕ)
variable (fits : ∀e∈core,N.width e=multiplicity e*grain)
local notation "S" => network N core multiplicity grain
local notation "sr" => unbundleBits N core multiplicity grain fits r

def splitStep (start : N.Edge→ℕ) : Ref N.Edge × ℕ→Ref ℕ × ℕ
  | (.cable e,t)=>if e∈core then (.cable (start e+t/grain),t%grain) else (.cable (start e),t)
  | (.hidden h,t)=>(.hidden h,t)
  | (.port p,t)=>(.port p,t)

theorem split_read (ports : P→ℕ) (old : Hidden N r→ℕ) (rank : N.Edge→ℕ)
    (unique : Function.Injective rank) (v : N.Site)
    (x : BitRef (boundaryWidth N v) ⊕ BitRef (r v).hiddenWidth) :
    numbered (fun e : (S).Edge=>(chronological N core multiplicity grain rank unique e).val)
      (view (S) (sr) ports old v (x.map (pieceBit N core multiplicity grain fits v) id)) =
      splitStep N core grain (ProtocolRAMPortRanks.«prefix» (span N core multiplicity) rank)
        (view N r ports old v x) := by
  rcases x with ⟨e|p,t⟩|⟨h,t⟩
  · let readPiece (b : BitRef (boundaryWidth (S) v)) : Ref ℕ × ℕ :=
      numbered (fun a : (S).Edge=>(chronological N core multiplicity grain rank unique a).val)
        (view (S) (sr) ports old v (.inl b))
    let start := ProtocolRAMPortRanks.«prefix» (span N core multiplicity) rank e.val
    change readPiece (pieceBit N core multiplicity grain fits v ⟨.inl e,t⟩) =
      if e.val∈core then (.cable (start+t.val/grain),t.val%grain) else (.cable start,t.val)
    by_cases active : e.val∈core
    · simp only [DescentKernelHistory.pieceBit,dite_eq_left active,ite_eq_left active]; rfl
    · simp only [DescentKernelHistory.pieceBit,dite_eq_right active,ite_eq_right active]; rfl
  · rfl
  · rfl

def liftRef (f : E→E') : Ref E × ℕ→Ref E' × ℕ
  | (.cable e,t)=>(.cable (f e),t)
  | (.port p,t)=>(.port p,t)
  | (.hidden h,t)=>(.hidden h,t)

/-- One quotient retains the original handle on every surviving cable. -/
def absorb (edge : E→ℕ) (inside : E→Bool) : Ref E × ℕ→Ref E × ℕ
  | (.cable e,t)=>if inside e then (.hidden (2*edge e),t) else (.cable e,t)
  | (.hidden h,t)=>(.hidden (2*h+1),t)
  | (.port p,t)=>(.port p,t)

def emit (marked : E→Bool) (start : E→ℕ) (grain : ℕ) : Ref E × ℕ→Ref ℕ × ℕ
  | (.cable e,t)=>if marked e then (.cable (start e+t/grain),t%grain) else (.cable (start e),t)
  | (.hidden h,t)=>(.hidden h,t)
  | (.port p,t)=>(.port p,t)

theorem occupied_lift (ports : P→ℕ) (edge : N.Edge↪ℕ) (old : Hidden N r↪ℕ)
    (v : V) (u : {s //loc s=v}) (x : BitRef (boundaryWidth N u.val) ⊕ BitRef (r u.val).hiddenWidth) :
    liftRef (fun e : (Q).Edge=>e.val)
        (view (Q) (qr) ports (quotientHidden N r loc pos ball edge old) v (NodeOrder.quotientRef N loc pos ball r v u x)) =
      absorb edge (fun e=>decide (loc (N.src e)=loc (N.dst e))) (view N r ports old u.val x) := by
  rcases x with ⟨e|p,t⟩|⟨h,t⟩
  · by_cases same : loc (N.src e.val)=loc (N.dst e.val) <;>
      simp [view,liftRef,absorb,NodeOrder.quotientRef,DescentKernelHistory.quotientBit,same]; rfl
  · rfl
  · cases u with | mk u eqn=>subst v;rfl

theorem lift_absorb (f : E→E') (edge : E'→ℕ) (inside : E'→Bool) (v : Ref E × ℕ) :
    liftRef f (absorb (edge∘f) (inside∘f) v)=absorb edge inside (liftRef f v) := by
  rcases v with ⟨a,t⟩
  cases a with
  | port _=>rfl
  | hidden _=>rfl
  | cable e=>cases test : inside (f e) <;> simp [absorb,liftRef,Function.comp_apply,test]

theorem emit_lift (f : E→E') (marked : E'→Bool) (start : E'→ℕ) (g : ℕ) (v : Ref E × ℕ) :
    emit (marked∘f) (start∘f) g v=emit marked start g (liftRef f v) := by
  rcases v with ⟨(_|_|e),t⟩ <;> rfl

/-- This is exactly the case-dispatch of the native output column, in chronological
order: physical contraction, hub contraction, subdivision of the surviving cable. -/
theorem two_quotients_and_split (h : Headers E) (edge : E→ℕ) (grain : ℕ) (v : Ref E) (q : ℕ) :
    emit h.marked h.«prefix» grain
      (absorb edge (fun e=>decide (h.lastSrc e=h.lastDst e))
        (absorb edge (fun e=>decide (h.firstSrc e=h.firstDst e)) (v,q))) =
      transported h edge grain q v := by
  cases v with
  | port p=>rfl
  | hidden p=>simp [emit,absorb,transported]; omega
  | cable e=>
    by_cases a : h.firstSrc e=h.firstDst e <;> by_cases b : h.lastSrc e=h.lastDst e <;>
      cases k : h.marked e <;> simp [emit,absorb,transported,a,b,k] <;> omega

/-- Aligned p-bit words need a single quotient lookup per word. Every bit of the
word enters the same child; successive within-word coordinates remain consecutive. -/
theorem aligned_quotient (p grain q k : ℕ) (hp : 0<p) (hg : 0<grain) (hk : k<p) :
    (q*p+k)/(grain*p)=q/grain ∧ (q*p+k)%(grain*p)=(q%grain)*p+k := by
  have small : q%grain*p+k<grain*p := by
    calc
      q%grain*p+k < q%grain*p+p := Nat.add_lt_add_left hk _
      _ = (q%grain+1)*p := (Nat.succ_mul _ _).symm
      _ ≤ grain*p := Nat.mul_le_mul_right _ (Nat.mod_lt _ hg)
  have original : q*p+k=(q%grain*p+k)+(grain*p)*(q/grain) := by
    calc
      _ = (q%grain+grain*(q/grain))*p+k := by rw [Nat.mod_add_div]
      _ = _ := by ring
  constructor
  · rw [original,Nat.add_mul_div_left _ _ (Nat.mul_pos hg hp),Nat.div_eq_of_lt small,zero_add]
  · rw [original,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small]

end
end Hierarchy.DescentOperandRouteRAM

end OAI
