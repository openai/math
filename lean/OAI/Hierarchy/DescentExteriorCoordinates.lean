import OAI.Hierarchy.DescentExteriorChunks
import OAI.Hierarchy.DescentColonyLayout

namespace OAI
/-! # Exterior hub coordinates through true colony remixes and dyadic grouping -/
namespace Hierarchy.DescentExterior
open DescentGL DescentColonies
open scoped Classical
noncomputable section

/-- The prefix is the quotient and the retained coordinates are the actual
remainder, in the big-endian contiguous block encoding used by the compiler. -/
theorem split_value (h g : ℕ) (x : Bits (h+g)) :
    (address (h+g) x).val=(address h ((splitRows h g x).1)).val*2^g+
      (address g ((splitRows h g x).2)).val := by
  change value (h+g) x=value h _*2^g+value g _
  induction g with
  | zero=>
    simp only [pow_zero,mul_one,value,Nat.add_zero]
    rfl
  | succ g ih=>
    let prev:=headRows (Nat.le_succ (h+g)) x
    have a : (splitRows h g prev).1=(splitRows h (g+1) x).1 := rfl
    have b : (splitRows h g prev).2=
        headRows (Nat.le_succ g) ((splitRows h (g+1) x).2) := rfl
    change 2*value (h+g) prev+_=value h _*2^(g+1)+(2*value g _+_)
    rw [ih prev,a,b,pow_succ]
    let hpart:=value h ((splitRows h (g+1) x).1)
    let gpart:=value g (headRows (Nat.le_succ g) ((splitRows h (g+1) x).2))
    let lpart:=(x (Fin.last (h+g))).val
    change 2*(hpart*2^g+gpart)+lpart=hpart*(2^g*2)+(2*gpart+lpart)
    ring

theorem split_index (h g : ℕ) (L : Layout (h+g)) (b : Block (h+g)) :
    let x:=L ((address _).symm b)
    (address h (splitRows h g x).1).val=group h (rearrange L b) ∧
    (address g (splitRows h g x).2).val=(rearrange L b).val%2^g := by
  intro x
  have value_eq := split_value h g x
  have y : rearrange L b=address _ x := rfl
  have low := (address g (splitRows h g x).2).isLt
  constructor
  · change value h (headRows (Nat.le_add_right h g) x)=_
    rw [y,prefix_value]
  · rw [y,value_eq,Nat.mul_add_mod_of_lt low]

def permute {k : ℕ} (e : Equiv.Perm (Fin k)) : Layout k where
  toFun y := y∘e.symm
  invFun y := y∘e
  left_inv x := funext fun i=>congrArg x (e.symm_apply_apply i)
  right_inv x := funext fun i=>congrArg x (e.apply_symm_apply i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Act on the current active block coordinates, retain all earlier stack
digits exactly, and move the resulting coordinate fields by fixed wiring. -/
def promote {k h r : ℕ} (arity : k=h+r) (into out : Equiv.Perm (Fin k)) (L : Layout h) : Layout k :=
  let sections:=(castBits arity).trans (splitRows h r)
  (((permute into).trans sections).trans (L.prodCongr (LinearEquiv.refl _ _))).trans
    (sections.symm.trans (permute out))

theorem promote_read {k h r : ℕ} (arity : k=h+r) (into out : Equiv.Perm (Fin k)) (L : Layout h) (x : Bits k) :
    let sec:=(castBits arity).trans (splitRows h r)
    sec ((permute out).symm (promote arity into out L x))=
      (L (sec (permute into x)).1,(sec (permute into x)).2) := by
  simp [promote,LinearEquiv.trans_apply]

/-- A recorded stage retains the true exterior label before and after its
chosen transformation. Composition is an actual binary linear layout. -/
structure Record {k : ℕ} {E : Type} (before after : E→Bits k) where
  layout : Layout k
  read : ∀z,after z=layout (before z)

def Record.refl {k : ℕ} {E : Type} (x : E→Bits k) : Record x x :=
  ⟨LinearEquiv.refl _ _,fun _=>rfl⟩

def Record.then {k : ℕ} {E : Type} {a b c : E→Bits k}
    (r : Record a b) (s : Record b c) : Record a c :=
  ⟨r.layout.trans s.layout,fun v=>(s.read v).trans (congrArg s.layout (r.read v))⟩

theorem Record.exterior {j r : ℕ} {E : Type} {a b : E→Bits (j+(j+r))}
    (rec : Record a b) (z : E) :
    coords j r (b z)=(plan rec.layout).last.apply (flip ((plan rec.layout).middle.apply
      (flip ((plan rec.layout).first.apply (coords j r (a z)))))) :=
  (congrArg (coords j r) (rec.read z)).trans (plan_apply rec.layout (a z))

end
end Hierarchy.DescentExterior

end OAI
