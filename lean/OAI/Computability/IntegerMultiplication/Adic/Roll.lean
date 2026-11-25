import OAI.Computability.IntegerMultiplication.Adic.Packet
import OAI.Computability.IntegerMultiplication.Adic.Arrange
import OAI.Computability.IntegerMultiplication.Strip.Route

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open Matrix Strip Strip.Dims IntegerMultiplication.Code IntegerMultiplication.Port
variable {p j : ℕ} [NeZero p]
noncomputable section
variable (a b : Nug p)
def slide (o : Tower p j) (x : Tower p j) : Tower p j :=
  ↑(a.own j)*↑((b.own j)⁻¹)*x+o
def roll (o : Tower p j) : Tower p j ≃ Tower p j where
  toFun := slide a b o
  invFun := fun y => ↑(b.own j)*↑((a.own j)⁻¹)*(y-o)
  left_inv x := by
    unfold slide
    have hh (y : Tower p j) :
        (↑(b.own j)*↑((a.own j)⁻¹)*(↑(a.own j)*↑((b.own j)⁻¹)*y) : Tower p j) = y := by
      calc
       _ = (↑((a.own j)⁻¹)*↑(a.own j):Tower p j)*
          (↑(b.own j)*↑((b.own j)⁻¹):Tower p j)*y := by ac_rfl
       _ = _ := by rw [Units.inv_mul, Units.mul_inv, one_mul, one_mul]
    change _*(_+o-o)=_
    rw [add_sub_cancel_right, hh]
  right_inv x := by
    unfold slide
    have hh (y : Tower p j) :
        (↑(a.own j)*↑((b.own j)⁻¹)*(↑(b.own j)*↑((a.own j)⁻¹)*y) : Tower p j) = y := by
      calc
       _ = (↑((b.own j)⁻¹)*↑(b.own j):Tower p j)*
          (↑(a.own j)*↑((a.own j)⁻¹):Tower p j)*y := by ac_rfl
       _ = _ := by rw [Units.inv_mul, Units.mul_inv, one_mul, one_mul]
    change _*(_*(x-o))+_= _
    rw [hh, sub_add_cancel]
def swift (o : Tower p j) : Block p j ≃ Block p j :=
  ((index p j).trans (roll a b o)).trans (index p j).symm
@[simp] theorem arrive (o : Tower p j) (x) : index p j (swift a b o x) = slide a b o (index p j x) := by
  rw [swift,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl
@[simp] theorem arriveBack (o : Tower p j) (y) : slide a b o (index p j ((swift a b o).symm y)) =
    index p j y := by rw [← arrive,Equiv.apply_symm_apply]
omit [NeZero p] in
@[simp] theorem slide_spec (o x : Tower p j) :
    (b.count:Tower p j)*slide a b o x = a.count*x+b.count*o := by
  have e := Nug.identifies b j
  rw [← e,slide,mul_add,← mul_assoc,mul_left_comm,mul_assoc (↑(a.own j):Tower p j)]
  rw [Units.mul_inv,one_mul,e,Nug.identifies]

/-- Classify a mapping by the pair of high carries from (a*x+b*o) and (b*y). -/
abbrev Seal := Fin (a.count+b.count+1) × Fin (b.count+0+1)
def mark (x o y : Raw p) : Seal a b :=
  ((merge a.count b.count 0 (x,o)).2, (merge b.count 0 0 (y,y)).2)

theorem earn (x o y : Raw p) {vx vo vy : Tower p j} (hx : Holds j x vx)
    (ho : Holds j o vo) (hy : Holds j y vy) (rel : vy=slide a b vo vx) :
    a.count*code x+b.count*code o+p^j*(mark a b x o y).2.val =
      b.count*code y+p^j*(mark a b x o y).1.val := by
  obtain ⟨m,e⟩ := merged a.count b.count 0 x o (hx.length.trans ho.length.symm)
  obtain ⟨l,k⟩ := merged b.count 0 0 y y rfl
  have equal : (merge a.count b.count 0 (x,o)).1=(merge b.count 0 0 (y,y)).1 := by
    have hv0 : ∀ i, (0:Fin (i+1)).val = 0 := by simp
    apply Holds.single (merge_core _ _ _ x o hx ho)
    have e1 := merge_core b.count 0 (0:Fin (b.count+0+1)) y y hy hy
    rw [hv0] at e1 ⊢
    simpa [rel,slide_spec] using e1
  rw [Fin.val_zero,zero_mul,add_zero,add_zero, hy.length,← equal] at k
  rw [Fin.val_zero,add_zero,hx.length] at e
  rw [k,e,mark]
  simp only ; omega

-- Compute y
def ahead (o x : Raw p) :=
  add 1 1 0 (by decide) (applyScale ⟨false,a,b⟩ x,o)
def ret (o y : Raw p) :=
  applyScale ⟨false,b,a⟩ (add 1 1 0 (by decide) (y,negative o))

@[simp] theorem ahead_correct (o x : Raw p) {u v : Tower p j} (h : Holds j o u) (e : Holds j x v) :
    Holds j (ahead a b o x) (slide a b u v) := by
  simpa [Span.land,Span.fold,Span.polarity,slide, ahead] using
    (sum 1 1 0 (by decide) (scaled ⟨false,a,b⟩ e) h)

theorem return_correct (o y : Raw p) {u v : Tower p j} (h : Holds j o u) (e : Holds j y v) :
    Holds j (ret a b o y) ((roll a b u).symm v) := by
  have q : (roll a b u).symm v = ↑(b.own j)*↑((a.own j)⁻¹)*(v-u) := rfl
  simpa [ret,q,Span.land,Span.fold,Span.polarity,sub_eq_add_neg] using
    (scaled ⟨false,b,a⟩ (sum 1 1 0 (by decide) e (neg_correct h)))

def flag (o : Tower p j) (x : Block p j) :=
  mark a b (least x) (least ((index p j).symm o)) (least (swift a b o x))

def admiral (o : Tower p j) :
    Ranger (layout (field p j)) (layout (field p j)) (T:=Seal a b)
      (flag a b o) (flag a b o ∘ (swift a b o).symm) where
  run := swift a b o
  spot := number
  next := number
  ps := clean p j
  pt := clean p j
  same i := by simp
  mono := by
    intro k l e h
    let Q := least ((index p j).symm o)
    have x (k : Block p j) := earn a b (least k) Q (least (swift a b o k))
      (Holds.std _) (Holds.stdRev _) (Holds.std _) (arrive a b o k)
    have x1 := x k; have x2 := x l
    have e0 : mark a b (least k) Q (least (swift a b o k)) =
      mark a b (least l) Q (least (swift a b o l)) := e
    rw [e0] at x1
    have v : a.count > 0 := Nat.pos_of_ne_zero a.pos
    unfold number at *
    by_contra! i
    have n₁ := Nat.mul_lt_mul_of_pos_left h v
    have n₂ := Nat.mul_le_mul_left b.count i
    omega

end
end Adic

end IntegerMultiplication
end Computability
end OAI
