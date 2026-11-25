import OAI.ThreeFlat.LocalTableNetwork
import OAI.ThreeFlat.BitNetworkGlue
import Mathlib.Tactic

namespace OAI
/-! # Enabling a trivalent local check with one flag

If the guard is clear, every private summation bit is fixed to zero. This
ensures that an inactive test contributes the unit over every field.
-/

namespace Hierarchy.Tagged.Guard
open ThreeFlat
open scoped BigOperators Classical
noncomputable section

private def lift {z p : ℕ} : BitSource z p → BitSource z (p+1)
  | .hidden i => .hidden i
  | .pin i => .pin i.succ
  | .constant b => .constant b

private theorem read_lift {z p : ℕ} (s : BitSource z p) (h : Fin z → Bool)
    (enable : Bool) (x : Fin p → Bool) :
    (lift s).read h (Fin.cases enable x) = s.read h x := by cases s <;> simp [lift, BitSource.read]

private def weight {F : Type*} [Zero F] [One F] {p : ℕ} (N : BitNetwork F p)
    (g : Fin N.cells ⊕ Fin N.internal) (v : Fin 4 → Bool) : F :=
  match g with
  | .inl i => if v 0 then N.table i (v ∘ Fin.succ) else 1
  | .inr _ => if !v 0 && v 1 then 0 else 1

private def wire {F : Type*} {p : ℕ} (N : BitNetwork F p) (g : Fin N.cells ⊕ Fin N.internal) :
    Fin 4 → BitSource N.internal (p+1) :=
  Fin.cases (.pin 0) (g.elim (fun i j => lift (N.source i j)) (fun i _ => .hidden i))

def network {F : Type*} [Zero F] [One F] {p : ℕ} (N : BitNetwork F p) : BitNetwork F (p+1) :=
  BitNetwork.glue (fun g => TableCompiler.localTableNetwork (weight N g)) (wire N)

theorem value {F : Type*} [CommSemiring F] {p : ℕ} (N : BitNetwork F p) (enable : Bool)
    (x : Fin p → Bool) : (network N).eval (Fin.cases enable x) = if enable then N.eval x else 1 := by
  have row (en : Bool) (h : Fin N.internal → Bool) (i : Fin N.cells) :
      weight N (.inl i) (fun j => (wire N (.inl i) j).read h (Fin.cases en x)) =
        if en then N.factor x h i else 1 := by
    cases en with
    | false => rfl
    | true =>
      apply congrArg (N.table i)
      funext j
      exact read_lift (N.source i j) h true x
  have hidden (en : Bool) (h : Fin N.internal → Bool) (i : Fin N.internal) :
      weight N (.inr i) (fun j => (wire N (.inr i) j).read h (Fin.cases en x)) =
        if en then 1 else if h i=false then 1 else 0 := by
    change (if !en && h i then 0 else 1) = _
    cases en <;> cases h i <;> rfl
  rw [network,BitNetwork.glue_eval]
  simp only [TableCompiler.localTableNetwork_eval,Fintype.prod_sum_type,row,hidden]
  cases enable with
  | true => simp [BitNetwork.eval,BitNetwork.weight]
  | false =>
    have all (h : Fin N.internal → Bool) : (∀i,h i=false) ↔ h=fun _ => false := funext_iff.symm
    simp [Fintype.prod_boole,all]

theorem size {F : Type*} [Zero F] [One F] {p : ℕ} (N : BitNetwork F p) :
    (network N).cells+(network N).internal = 176*N.cells + 177*N.internal := by
  simp [network, TableCompiler.localTableNetwork_cells, TableCompiler.localTableNetwork_internal]
 ; omega

/-- Renaming or fixing an input to one of the two Boolean constants uses no cells. -/
def rename {F : Type*} {p q : ℕ} (N : BitNetwork F p) (port : Fin p → Fin q ⊕ Bool) :
    BitNetwork F q where
  cells := N.cells
  internal := N.internal
  table := N.table
  source i j := match N.source i j with
    | .hidden h => .hidden h
    | .constant b => .constant b
    | .pin t => (port t).elim BitSource.pin BitSource.constant

theorem rename_value {F : Type*} [CommSemiring F] {p q : ℕ} (N : BitNetwork F p)
    (port : Fin p → Fin q ⊕ Bool) (x : Fin q → Bool) :
    (rename N port).eval x = N.eval (Sum.elim x id ∘ port) := by
  unfold BitNetwork.eval BitNetwork.weight
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro i _
  change N.table i _ = N.table i _
  congr 1
  funext j
  change (match N.source i j with
    | .hidden a => BitSource.hidden a
    | .constant b => BitSource.constant b
    | .pin t => (port t).elim BitSource.pin BitSource.constant).read h x = _
  cases src : N.source i j with
  | hidden a => rfl
  | constant _ => rfl
  | pin t => cases eq : port t <;> simp [BitSource.read, eq]


/-- Negate one exposed pin without allocating a gate. -/
def flip {F : Type*} {p : ℕ} (N : BitNetwork F p) (pin : Fin p) : BitNetwork F p where
  internal := N.internal
  cells := N.cells
  source := N.source
  table i b := N.table i fun j => match N.source i j with
    | .pin v => if v = pin then !(b j) else b j
    | _ => b j

theorem flip_eval {F : Type*} [CommSemiring F] {p : ℕ} (N : BitNetwork F p) (pin : Fin p)
    (x : Fin p → Bool) : (flip N pin).eval x = N.eval (fun i => if i = pin then !(x i) else x i) := by
  unfold BitNetwork.eval BitNetwork.weight
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (N.table i)
  funext j
  change (match N.source i j with
    | .pin v => if v=pin then !((N.source i j).read a x) else (N.source i j).read a x
    | _ => (N.source i j).read a x) = (N.source i j).read a _
  cases N.source i j <;> rfl

private def alternative {F : Type*} [Zero F] [One F] {p : ℕ}
    (A B : BitNetwork F p) : Bool → BitNetwork F (p+1)
  | false => flip (network A) 0
  | true => network B

/-- The hidden branch bit selects one of two row conditions. -/
def either {F : Type*} [Zero F] [One F] {p : ℕ} (A B : BitNetwork F p) : BitNetwork F p :=
  BitNetwork.glue (alternative A B) fun _ => Fin.cases (.hidden (0 : Fin 1)) BitSource.pin

theorem either_eval {F : Type*} [CommSemiring F] {p : ℕ} (A B : BitNetwork F p) (x : Fin p → Bool) :
    (either A B).eval x = A.eval x + B.eval x := by
  rw [either, BitNetwork.glue_eval, ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  have read (s : Bool) : (fun j : Fin (p+1) => (Fin.cases (motive := fun _ : Fin (p+1) => BitSource 1 p) (.hidden 0) BitSource.pin j).read
      ((Equiv.funUnique (Fin 1) Bool).symm s) x) = Fin.cases s x := by
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
  have neg (s : Bool) : (fun i : Fin (p+1) => if i = 0 then !(Fin.cases s x i) else Fin.cases s x i) =
      Fin.cases (!s) x := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> simp
  simp only [read, Fintype.prod_bool, alternative, flip_eval, neg, value]
  simp [add_comm]

theorem either_size {F : Type*} [Zero F] [One F] {p : ℕ} (A B : BitNetwork F p) :
    (either A B).cells + (either A B).internal ≤
      1 + 177*(A.cells + A.internal + B.cells + B.internal) := by
  have a := size A
  have b := size B
  simp only [either, BitNetwork.glue_cells, BitNetwork.glue_internal, Fintype.sum_bool, alternative, flip]
  omega


def both {F : Type*} {p : ℕ} (A B : BitNetwork F p) : BitNetwork F p :=
  BitNetwork.glue (fun b : Bool => if b then B else A) fun _ (i : Fin p) =>
    (BitSource.pin i : BitSource 0 p)

theorem both_eval {F : Type*} [CommSemiring F] {p : ℕ} (A B : BitNetwork F p) (x : Fin p → Bool) :
    (both A B).eval x = A.eval x * B.eval x := by
  simp [both, BitNetwork.glue_eval, BitSource.read, mul_comm]

theorem both_size {F : Type*} {p : ℕ} (A B : BitNetwork F p) :
    (both A B).cells+(both A B).internal = A.cells+A.internal+(B.cells+B.internal) := by
  simp [both]
 ; omega


end
end Hierarchy.Tagged.Guard

end OAI
