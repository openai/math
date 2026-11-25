import OAI.Computability.IntegerMultiplication.Param.Progression

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- CRT axis parameter stream. Index from 0. Short second from last when >=2.
Tapes use these formulas (not choose/min over relation). -/
namespace Param
open Filter

def abbreviated n := lanes n-2
def short n (i : ℕ) := i=abbreviated n
instance decShort n i : Decidable (short n i) := Nat.decEq i (abbreviated n)
def axle n i :=
  if short n i then reach n else span_ n
def side n i := (2:ℕ)^axle n i
def nugget n := max 1 (root_ (lanes n) (room n))
def moduli n i :=
  if short n i then (nugget n)^2 else stage (lanes n) (wall n) (red (lanes n) (nugget n)) i

instance axisPos (n i) : NeZero (moduli n i) := by
  refine ⟨?_⟩
  unfold moduli
  split
  · apply ne_of_gt (pow_pos _ _); unfold nugget; omega
  · unfold stage; omega
instance sidePos n i : NeZero (side n i) := ⟨pow_ne_zero _ (by decide)⟩

theorem sides (n i) :
    side n i= if short n i then room n else wall n := by
  unfold side axle; split <;> rfl

theorem side_le (n i) :
    room n ≤ side n i ∧ side n i ≤ wall n := by
  rw [sides]; split <;> have h:=room_le n <;> omega

theorem square_size :
    Large fun n=> (256*lanes n)^2 ≤ room n := by
  filter_upwards [room_facts (256^2) 2] with n v
  refine le_trans ?_ v
  have f := Nat.factorial_pos (lanes n)
  calc
   _ ≤ (256*(lanes n+1))^2 := by gcongr; omega
   _ ≤ _ := by rw [mul_pow]; exact Nat.le_mul_of_pos_right _ (by positivity)

theorem nugget_s :
    Large fun n=> let d:=lanes n; let J:=nugget n; Odd J ∧
      64*d ≤ J ∧ Margin d (room n) (J^2) := by
  filter_upwards [square_size] with n v
  let d := lanes n
  have x := square_ (lanes_pos _) v
  dsimp only at x
  have d₁ : 0<lanes n := lanes_pos n
  have e : nugget n=root_ (lanes n) (room n) :=
    max_eq_right (by omega)
  dsimp only
  rw [e]
  exact x

theorem progression_size :
    Large fun n=> let d := lanes n; 128*d^2*red d (nugget n) ≤ wall n := by
  filter_upwards [nugget_s,room_facts 65536 4] with n h q
  dsimp only at h ⊢
  let d:=lanes n
  let J:=nugget n
  let f := Nat.factorial d
  have t₀ : 1≤f := Nat.factorial_pos _
  have r₀ : 1≤ room n := Nat.pow_pos (by decide)
  have d₁ := lanes_pos n
  have z : J^2≤wall n := Nat.le_trans (Nat.le_of_lt (h.2.2.strict r₀ d₁)) (room_le _)
  have s : (128*d^2*(2*f))^2 ≤ wall n := by
    calc
      _ = 65536*d^4*f^2 := by ring
      _ ≤ 65536*(d+1)^4*f^4 := by gcongr; omega; omega
      _ ≤ wall n := q.trans (room_le _)
  have e := Nat.mul_le_mul s z
  rw [← mul_pow,pow_two] at e -- e both sides?
  unfold red
  change 128*d^2*(2*f*J) ≤ _
  rw [← Nat.mul_assoc]
  exact Nat.mul_self_le_mul_self_iff.mp e

theorem axis_margins :
    Large fun n=> ∀ i < lanes n, Margin (lanes n) (side n i) (moduli n i) ∧ Odd (moduli n i) := by
  filter_upwards [nugget_s,progression_size] with n h q i v
  dsimp only at h q
  rw [sides,moduli]
  split
  · exact ⟨h.2.2,h.1.pow⟩
  · exact ⟨stage_margin (lanes_pos n) (show 1≤red (lanes n) (nugget n) by
      unfold red; have s:= lanes_pos n; have t := Nat.factorial_pos (lanes n)
      have j : 0<nugget n := by unfold nugget; omega
      exact Nat.mul_pos (Nat.mul_pos (by decide) t) j) v q,stage_odd⟩

theorem axis_more :
    Large fun n=> ∀ i < lanes n,
      budget n ≤ moduli n i ∧ moduli n i < side n i ∧ side n i ≤ 2^budget n := by
  filter_upwards [axis_margins,rooms 2 1] with n h v i t
  obtain ⟨x,_⟩ := h i t
  refine ⟨?_,x.strict (Nat.pow_pos (by decide)) (lanes_pos _),(side_le n i).2.trans (upright _)⟩
  have q := x.far (lanes_pos _)
  have e := (side_le n i).1
  rw [pow_one] at v
  omega

theorem axis_separation n {i j : ℕ} (h : i<lanes n) (q : j<lanes n) (t : i≠j) :
    Nat.Coprime (moduli n i) (moduli n j) := by
  unfold moduli
  split <;> rename_i v
  · split
    · rename_i w; exact (t (v.trans w.symm : i=j)).elim -- short not transparent (.trans?)
    exact rel_square.symm
  split
  · exact rel_square
  exact disjoint_ t h q

theorem axis_ratio :
    Large fun n=> ∀ i<lanes n, ((1:ℝ)+1/(8*(lanes n)))*(moduli n i:ℝ) ≤ side n i := by
  filter_upwards [axis_margins] with n h i v
  exact (h i v).1.ratio (lanes_pos n)
end Param

end IntegerMultiplication
end Computability
end OAI
