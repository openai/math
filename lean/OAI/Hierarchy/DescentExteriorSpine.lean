import OAI.Hierarchy.DescentExteriorCoordinates

namespace OAI
/-! # A checked exterior coordinate through active and frozen binary digits -/

namespace Hierarchy.DescentExterior
open DescentGL
noncomputable section

/-- The common host depends on the initial slab/host and the frozen digits.
All active digits are kept for later linear remixes. -/
structure Spine {E A B : Type} {a b : ℕ} (initial : E→Bits a) (current : E→Bits b)
    (first : E→A) (last : E→B) (f : ℕ) where
  cut : Bits a ≃ₗ[ZMod 2] Bits b × Bits f
  active_eq : ∀e,(cut (initial e)).1=current e
  host_eq : ∀e e',first e=first e'→(cut (initial e)).2=(cut (initial e')).2→last e=last e'

namespace Spine
variable {E A B C : Type} {a b c f g : ℕ}
variable {initial : E→Bits a} {middle : E→Bits b} {final : E→Bits c}
variable {first : E→A} {mid : E→B} {last : E→C}

def start (raw : E→Bits a) (host : E→A) : Spine raw raw host host 0 where
  cut:={toFun:=fun x=>(x,0),invFun:=Prod.fst,left_inv:=fun _=>rfl,
        right_inv:=fun ⟨x,y⟩=>Prod.ext rfl (Subsingleton.elim _ _),
        map_add':=fun x y=>by simp,map_smul':=fun x y=>by simp}
  active_eq _:=rfl
  host_eq _ _ h _:=h

def append (x : Spine initial middle first mid f) (y : Spine middle final mid last g) :
    Spine initial final first last (g+f) where
  cut := ((x.cut.trans (y.cut.prodCongr (LinearEquiv.refl (ZMod 2) (Bits f)))).trans
    (LinearEquiv.prodAssoc (ZMod 2) (Bits c) (Bits g) (Bits f))).trans
    ((LinearEquiv.refl (ZMod 2) (Bits c)).prodCongr (splitRows g f).symm)
  active_eq e := by change (y.cut (x.cut (initial e)).1).1=_;rw [x.active_eq,y.active_eq]
  host_eq e e' h eqn := by
    change (splitRows g f).symm ((y.cut (x.cut (initial e)).1).2,(x.cut (initial e)).2)=
      (splitRows g f).symm ((y.cut (x.cut (initial e')).1).2,(x.cut (initial e')).2) at eqn
    have parts:=(splitRows g f).symm.injective eqn
    have before:=x.host_eq e e' h (congrArg (fun pair : Bits g × Bits f=>pair.2) parts)
    apply y.host_eq e e' before
    have now:=congrArg (fun pair : Bits g × Bits f=>pair.1) parts
    simpa only [x.active_eq] using now

theorem width (x : Spine initial middle first mid f) : b+f=a := by
  have eq:=Fintype.card_congr x.cut.toEquiv
  have power : (2:ℕ)^a=2^(b+f) := by
    simpa [Bits,Fintype.card_fun,Fintype.card_prod,ZMod.card,pow_add] using eq
  simpa only [Nat.log2_two_pow] using congrArg Nat.log2 power.symm

/-- Reassemble the actual encounter into one binary layout for the exterior matrix program. -/
def record (x : Spine initial middle first mid f) (digits : b+f=a) :
    Record initial (fun e=>castBits digits ((splitRows b f).symm (middle e,(x.cut (initial e)).2))) :=
  ⟨(x.cut.trans (splitRows b f).symm).trans (castBits digits),fun e=>by
    change castBits digits ((splitRows b f).symm (middle e,(x.cut (initial e)).2)) =
      castBits digits ((splitRows b f).symm (x.cut (initial e)))
    rw [←x.active_eq e]⟩

end Spine
end
end Hierarchy.DescentExterior

end OAI
