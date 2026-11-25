import OAI.Hierarchy.DescentCableDonorNames

namespace OAI
/-! # Comparing sparse reset ordinals by their actually issued component digits -/
namespace Hierarchy.DescentResetOrdinalDigits
open scoped Classical
noncomputable section

inductive Layout
  | digit : Nat→Layout
  | append : Layout→Layout→Layout
  | product : Layout→Layout→Layout

namespace Layout
def size : Layout→Nat
  | .digit n=>n
  | .append a b=>a.size+b.size
  | .product a b=>a.size*b.size

def Value : Layout→Type
  | .digit n=>Fin n
  | .append a b=>Sum a.Value b.Value
  | .product a b=>a.Value×b.Value

def place : (l : Layout)→l.Value≃Fin l.size
  | .digit _=>Equiv.refl _
  | .append a b=>(Equiv.sumCongr a.place b.place).trans finSumFinEquiv
  | .product a b=>(Equiv.prodCongr a.place b.place).trans finProdFinEquiv

/-- A branch crossing a previous arithmetic sum uses one bit. For a pair,
comparison proceeds to the second original digit only on a tie in the first. -/
def before : (l : Layout)→l.Value→l.Value→Prop
  | .digit n,x,y=>(x : Fin n).val < (y : Fin n).val
  | .append a _,.inl x,.inl y=>a.before x y
  | .append _ _,.inl _,.inr _=>True
  | .append _ _,.inr _,.inl _=>False
  | .append _ b,.inr x,.inr y=>b.before x y
  | .product a b,(u,x),(v,y)=>a.before u v ∨ u=v ∧ b.before x y

theorem before_iff (l : Layout) (x y : l.Value) : l.before x y ↔ l.place x<l.place y := by
  induction l with
  | digit n=>rfl
  | append a b ia ib=>
    cases x with
    | inl u=>cases y with
      | inl v=>
        change a.before u v ↔ (a.place u).val<(a.place v).val
        exact (ia u v).trans Fin.lt_def
      | inr v=>
        change True ↔ (a.place u).val<a.size+(b.place v).val
        exact ⟨fun _=>(a.place u).isLt.trans_le (Nat.le_add_right a.size _),fun _=>trivial⟩
    | inr u=>cases y with
      | inl v=>
        change False ↔ a.size+(b.place u).val<(a.place v).val
        exact ⟨False.elim,not_lt_of_ge ((a.place v).isLt.le.trans (Nat.le_add_right a.size _))⟩
      | inr v=>
        change b.before u v ↔ a.size+(b.place u).val<a.size+(b.place v).val
        rw [Nat.add_lt_add_iff_left]
        exact (ib u v).trans Fin.lt_def
  | product a b ia ib=>
    obtain ⟨u,x⟩:=x
    obtain ⟨v,y⟩:=y
    change a.before u v ∨ u=v ∧ b.before x y ↔ (finProdFinEquiv (a.place u,b.place x)).val<(finProdFinEquiv (a.place v,b.place y)).val
    rw [ia,ib]
    have mul (q : a.Value) (j : b.Value) : (finProdFinEquiv (a.place q,b.place j)).val=(a.place q).val*b.size+(b.place j).val := by
      simp only [finProdFinEquiv_apply_val]; ring
    rw [mul,mul,DescentCableDonorNames.digit_lt (b.place x).isLt (b.place y).isLt]
    have same : (a.place u).val=(a.place v).val ↔ u=v :=
      ⟨fun h=>a.place.injective (Fin.ext h),fun h=>by rw [h]⟩
    rw [same]; rfl

end Layout
end
end Hierarchy.DescentResetOrdinalDigits

end OAI
