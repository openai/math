import OAI.Hierarchy.DescentPackedSumWords
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMHistogram

namespace OAI
/-! # Pairing a measured contact shape and its returned peer slot in each native lane -/
namespace Hierarchy.DescentContactCoordinateJoint
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {H G b M w : ℕ}

def number (radix shape halo : ℕ) :=radix*shape+halo
def join (radix : ℕ) (shape halo : Cell b) : Cell b :=number radix shape.val halo.val
def expr (radix : ℕ) (shape halo : Expr) := Expr.op .add (ProtocolRAM.scale radix shape) halo

theorem number_inj {radix a b c d : ℕ} (small : b<radix) (short : d<radix) :
    number radix a b=number radix c d ↔ a=c ∧ b=d :=by
  constructor
  · intro eqn
    have pos : 0<radix:=Nat.zero_lt_of_lt small
    have first:=congrArg (·/radix) eqn
    have second:=congrArg (·%radix) eqn
    simp [number,Nat.mul_add_div pos,Nat.div_eq_of_lt small,Nat.div_eq_of_lt short] at first
    simp [number,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt short] at second
    exact ⟨first,second⟩
  · rintro ⟨rfl,rfl⟩;rfl

theorem work (radix : ℕ) (shape halo : Expr) :
    (expr radix shape halo).work=2+radix*(shape.work+1)+halo.work :=by
  simp [expr,Expr.work,ProtocolRAM.scale_work]; omega

theorem scaled_fits (shape : Expr) {floor : ℕ} (fit : shape.Fits w floor) (radix : ℕ) :
    (ProtocolRAM.scale radix shape).Fits w floor := by
  induction radix with
  | zero=>trivial
  | succ k ih=>exact ⟨fit,ih⟩

theorem fits (radix : ℕ) (shape halo : Expr) {floor : ℕ} (a : shape.Fits w floor) (b : halo.Fits w floor) :
    (expr radix shape halo).Fits w floor :=⟨scaled_fits shape a radix,b⟩

theorem source (radix : ℕ) (shape halo : Expr) (m : Memory w) (x y : Fin H→Fin G→Cell b)
    (word : ∀h g,number radix (x h g).val (y h g).val<2^b)
    (first : Source shape x M m) (second : Source halo y M m) :
    Source (expr radix shape halo) (fun h g=>join radix (x h g) (y h g)) M m :=by
  intro q
  have pack : radix*(data x q).val+(data y q).val=(data (fun h g=>join radix (x h g) (y h g)) q).val:=by
    simp only [DescentPackedSumWords.lanes_val,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases live : q.2.val*M+j.val<G
    · let g : Fin G := ⟨q.2.val*M+j.val,live⟩
      have value : (join radix (x q.1 g) (y q.1 g)).val =
          number radix (x q.1 g).val (y q.1 g).val :=
        Fin.val_cast_of_lt (word q.1 g)
      simp only [dite_eq_left live]
      rw [value]
      simp only [g,number,Nat.add_mul,Nat.mul_assoc]
    · simp [live]
  change (ProtocolRAM.scale radix shape).eval m _+halo.eval m _=_
  rw [ProtocolRAM.eval_scale,first q,second q,←Nat.cast_mul,←Nat.cast_add,pack]

theorem joint_at (radix : ℕ) (a c i j : Cell b) (hi : i.val<radix) (hj : j.val<radix)
    (x : number radix a.val i.val<2^b) (y : number radix c.val j.val<2^b) :
    join radix a i=join radix c j ↔ a=c ∧ i=j :=by
  rw [Fin.ext_iff]
  simp only [join,Fin.val_cast_of_lt x,Fin.val_cast_of_lt y,number_inj hi hj,Fin.ext_iff]

end
end Hierarchy.DescentContactCoordinateJoint

end OAI
