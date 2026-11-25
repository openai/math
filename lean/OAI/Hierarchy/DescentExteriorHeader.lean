import OAI.Hierarchy.DescentExteriorPinTypes
import OAI.Hierarchy.DescentExteriorLookup
import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.ThreeFlat.Diagonal.TraceBanks
import OAI.ThreeFlat.Diagonal.TraceWordTests

namespace OAI
/-! # Fixed wiring of the proposed exterior words in both chunk orders -/
namespace Hierarchy.DescentExterior
open DescentGL Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.Diagonal TraceBanks
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def projected {e j r t : ℕ} (z : Hidden e j r t→Bool) (which : Bool) (a : Fin e) (v : Plane j r) :
    Fin t→Bool := fun b=>z ((which,a,v),b)

def gathered {e j r t : ℕ} (z : Hidden e j r t→Bool) (c : Column e j r) : Word (2^j*t) :=
  let a:=projected z c.1 c.2.2.1
  let b:=if c.2.1 then swapWire a else a
  pack (fun v=>b (v,c.2.2.2))

def wire {e j r t w : ℕ} (c : Column e j r) (b : Fin (w+1)) : Hidden e j r t ⊕ Bool :=
  if h : b.val<2^j*t then
    let p:=(pos j t).symm ⟨b.val,h⟩
    let x:Plane j r := (p.1,c.2.2.2)
    .inl ((c.1,c.2.2.1,if c.2.1 then flip x else x),p.2)
  else .inr false

theorem gather_read {e j r t w : ℕ} (fit : 2^j*t≤w) (z : Hidden e j r t→Bool)
    (c : Column e j r) (b : Fin (w+1)) :
    (wire c b).elim z id=TraceWords.bits (wide ((gathered z c).val:Word w)) b := by
  have bound : (gathered z c).val<2^w :=
    (gathered z c).isLt.trans_le (Nat.pow_le_pow_right (by decide) fit)
  change _=((gathered z c).val%(2^w)).testBit b.val
  rw [Nat.mod_eq_of_lt bound]
  by_cases small : b.val<2^j*t
  · let i : Fin (2^j*t):=⟨b.val,small⟩
    rw [show (gathered z c).val.testBit b.val=wordBits _ (gathered z c) i from
      Computability.VPVNP.LiveHeader.testBit_wordBits (gathered z c) i]
    obtain ⟨⟨v,k⟩,eq⟩:=(pos j t).surjective i
    let field : Plane j r → Fin t → Bool :=
      if c.2.1 then swapWire (projected z c.1 c.2.2.1) else projected z c.1 c.2.2.1
    change _=wordBits (2^j*t) (pack (fun v => field (v,c.2.2.2))) i
    rw [←eq,pack_bit (j:=j) (t:=t) (fun v => field (v,c.2.2.2)) v k]
    unfold wire
    rw [dite_eq_left small]
    have posEq : (pos j t).symm ⟨b.val,small⟩=(v,k) :=
      (congrArg (pos j t).symm eq.symm).trans ((pos j t).symm_apply_apply _)
    cases side : c.2.1 <;> simp [field,side,posEq,projected,swapWire]
  · rw [wire,dite_eq_right small]
    exact (Nat.testBit_lt_two_pow ((gathered z c).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt small)))).symm

/-- Pulling the observed words directly back to their shared physical
pins imposes exactly the two phase equations, on both full arrays. -/
theorem gathered_correct {e j r t : ℕ} (M : Fin e→Layout (j+(j+r)))
    (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) :
    (∀a,stagesOK (M a) (x a) (projected z false a) (projected z true a)) ↔
      (∀a v,gathered z (false,false,a,v)=
          pack (fun l=>push (plan (M a)).first (x a) (l,v))) ∧
      (∀a v,gathered z (true,false,a,v)=
        pack (fun l=>push (plan (M a)).middle (swapWire (projected z false a)) (l,v))) := by
  have unpack {f g : Bits j→Fin t→Bool} (eq : pack f=pack g) (l : Bits j) (b : Fin t) :
      f l b=g l b := by
    simpa only [pack_bit] using congrArg (fun v=>wordBits _ v (pos j t (l,b))) eq
  constructor
  · intro ok
    constructor
    · intro a v
      change pack (fun l => projected z false a (l,v)) = _
      rw [((stages_iff ..).mp (ok a)).1]
    · intro a v
      change pack (fun l => projected z true a (l,v)) = _
      rw [((stages_iff ..).mp (ok a)).2]
  · rintro ⟨one,two⟩ a
    apply (stages_iff ..).mpr
    constructor
    · funext i b
      obtain ⟨l,v⟩ := i
      exact unpack (f := fun k => projected z false a (k,v))
        (g := fun k => push (plan (M a)).first (x a) (k,v)) (one a v) l b
    · funext i b
      obtain ⟨l,v⟩ := i
      exact unpack (f := fun k => projected z true a (k,v))
        (g := fun k => push (plan (M a)).middle (swapWire (projected z false a)) (k,v))
        (two a v) l b

/-- The two physically proposed arrays for all exterior sites are uniquely
determined by the selected linear transforms and the literal exterior input. -/
def canonical {e j r t : ℕ} (M : Fin e→Layout (j+(j+r)))
    (x : Fin e→Plane j r→Fin t→Bool) (i : Hidden e j r t) : Bool :=
  let a:=i.1.2.1
  let f:=push (plan (M a)).first (x a)
  let g:=push (plan (M a)).middle (swapWire f)
  (if i.1.1 then g else f) i.1.2.2 i.2

theorem canonical_iff {e j r t : ℕ} (M : Fin e→Layout (j+(j+r)))
    (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) :
    (∀a,stagesOK (M a) (x a) (projected z false a) (projected z true a)) ↔ z=canonical M x := by
  constructor
  · intro ok
    funext ⟨⟨side,a,i⟩,b⟩
    obtain ⟨one,two⟩:=(stages_iff ..).mp (ok a)
    cases side with
    | false=> exact congrFun (congrFun one i) b
    | true=>
      rw [one] at two
      exact congrFun (congrFun two i) b
  · rintro rfl a
    exact (stages_iff ..).mpr ⟨rfl,rfl⟩

theorem sum_headers {e j r t : ℕ} {F : Type} [CommSemiring F]
    (M : Fin e→Layout (j+(j+r))) (x : Fin e→Plane j r→Fin t→Bool)
    (finish : (Fin e→Plane j r→Fin t→Bool)→F) :
    (∑z : Hidden e j r t→Bool,if ∀a,stagesOK (M a) (x a)
        (projected z false a) (projected z true a) then
      finish (fun a=>output (M a) (projected z true a)) else 0) =
      finish (fun a h=>x a (coords j r ((M a).symm ((coords j r).symm h)))) := by
  simp_rw [canonical_iff]
  rw [Finset.sum_ite_eq',ite_eq_left (Finset.mem_univ _)]
  apply congrArg finish
  funext a h
  have ok:=(canonical_iff M x (canonical M x)).mpr rfl a
  simpa only [LinearEquiv.apply_symm_apply] using
    output_wire (M a) (x a) _ _ ok ((M a).symm ((coords j r).symm h))

end
end Hierarchy.DescentExterior

end OAI
