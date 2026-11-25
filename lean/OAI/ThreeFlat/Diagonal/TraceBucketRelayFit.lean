import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.Diagonal.TraceBucketRelayExpr

namespace OAI
/-! # Word fits and the exact value of the native initial relay metadata kernel -/

namespace ThreeFlat.Diagonal.TraceBucketRelay

open RAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

variable {W n : ℕ}

private theorem slot_fits (d o q : Formula n) (data : Param → ℕ) (m : ℕ → ℕ) (v : Fin n → ℕ)
    (hd : d.Fits W data m v) (ho : o.Fits W data m v) (hq : q.Fits W data m v)
    (vd : d.natural W data m v+1<2^W) (vo : o.natural W data m v<2^W)
    (vq : q.natural W data m v+1<2^W) (lit : 3<2^W) :
    (slotFormula d o q).Fits W data m v := by
  have both {c : Comparison} {x y a b : Formula n}
      (hx : x.Fits W data m v) (hy : y.Fits W data m v)
      (lx : x.natural W data m v<2^W) (ly : y.natural W data m v<2^W)
      (ha : a.Fits W data m v) (hb : b.Fits W data m v) :
      (Formula.select c x y a b).Fits W data m v := by
    refine ⟨hx,hy,lx,ly,?_⟩
    split <;> assumption
  have dc : d.natural W data m v<2^W := by omega
  have qc : q.natural W data m v<2^W := by omega
  have cut : (sub o d).Fits W data m v := ⟨ho,hd,vo,dc⟩
  have lc : (sub o d).natural W data m v<2^W := (Nat.sub_le ..).trans_lt vo
  have left : (eqz o (add q (L 1)) (L 1) (L 0)).Fits W data m v :=
    both ho ⟨hq,trivial,trivial⟩ vo vq trivial trivial
  have right : (lt q (sub o d) (L 1) (L 0)).Fits W data m v :=
    both hq cut qc lc trivial trivial
  unfold slotFormula
  exact both ho trivial vo (show 0<2^W by omega) trivial
    (both ho ⟨hd,trivial,trivial⟩ vo vd left right)

structure Bounds (W : ℕ) (v : Fin 10 → ℕ) : Prop where
  inputs : ∀ i, v i < 2^W
  literal : 3 < 2^W
  bank : v 2*v 3 < 2^W
  dimension : v 5+1 < 2^W
  position : v 6+v 7+1 < 2^W

theorem bounds_arguments {arcs tags perOffset d low stage extra equality row field : ℕ}
    (hA : 2≤arcs) (ht : 0<tags) (hper : perOffset≤tags) (hrow : row<arcs*tags+tags)
    (hfield : field<4) (hlit : 3<2^W) (hpin : 2+extra+2*(arcs*tags)≤2^W)
    (hd : d+1<2^W) (hi : low+stage+1<2^W) (heq : equality<2^W) :
    Bounds W (arguments arcs tags perOffset d low stage extra equality row field) := by
  have ha := Nat.le_mul_of_pos_right arcs ht
  have hs := Nat.le_mul_of_pos_left tags (show 0<arcs by omega)
  refine ⟨?_,hlit,?_,hd,hi⟩
  · intro q
    fin_cases q <;> simp [arguments] <;> omega
  · change arcs*tags<2^W
    omega

theorem fits (data : Param → ℕ) (m : ℕ → ℕ) (v : Fin 10 → ℕ) (h : Bounds W v) :
    formula.Fits W data m v := by
  let tag : Formula 10 := rem (.reg 0) (.reg 3)
  let off : Formula 10 := div tag (.reg 4)
  let now : Formula 10 := add (.reg 6) (.reg 7)
  let prior : Formula 10 := add (.reg 6) (sub (.reg 7) (L 1))
  have g (i : Fin 10) := h.inputs i
  have lit := h.literal
  have offBound : (v 0%v 3)/v 4 < 2^W :=
    (Nat.div_le_self ..).trans_lt ((Nat.mod_le ..).trans_lt (g 0))
  have offFit : off.Fits W data m v := by
    simp [off,tag,Formula.Fits,Formula.natural,natOp,opFits,g,(Nat.mod_le ..).trans_lt (g 0)]
  have cur := slot_fits (.reg 5) off now data m v trivial offFit
    (by simp [now,Formula.Fits,opFits]) h.dimension offBound h.position lit
  have prev := slot_fits (.reg 5) off prior data m v trivial offFit
    (by simp only [prior,Formula.Fits,opFits,Formula.natural,true_and,and_true];exact ⟨g 7,by omega⟩) h.dimension offBound
    (by change v 6+(v 7-1)+1<2^W;have := h.position;omega) lit
  have bound := h.bank
  have modFit := (Nat.mod_le (v 0) (v 3)).trans_lt (g 0)
  have divFit := (Nat.div_le_self (v 0) (v 3)).trans_lt (g 0)
  have small (a b c : ℕ) : chooseSlot a b c < 2^W := (slot_le ..).trans_lt (by omega)
  change (slotFormula (.reg 5) (div (rem (.reg 0) (.reg 3)) (.reg 4)) (add (.reg 6) (.reg 7))).Fits W data m v at cur
  change (slotFormula (.reg 5) (div (rem (.reg 0) (.reg 3)) (.reg 4)) (add (.reg 6) (sub (.reg 7) (L 1)))).Fits W data m v at prev
  simp only [formula,Formula.Fits,cur,prev,Formula.natural,slot_natural,natOp,opFits,natTest,
    true_and,and_true,decide_eq_true_eq,g,bound,small,divFit]
  repeat' first | apply And.intro | split
  all_goals first | trivial | omega

theorem program_eval {K : ℕ} (p : Param → Fin K) (data : Fin K → ℕ) (m : ℕ → ℕ)
    (v : Fin 10 → ℕ) (h : Bounds W v) :
    (program W K p).eval (fun i => (data i : Word W)) (fun i => (m i : Word W)) (fun i => (v i : Word W)) =
      (values v : Word W) := by
  rw [program,Formula.eval_compile,← formula_natural W (data ∘ p) m v]
  exact Formula.value_eq_natural _ _ _ _ (fits _ _ _ h)

theorem program_eval_memory {K : ℕ} (p : Param → Fin K) (data : Fin K → Word W)
    (m : Memory W) (v : Fin 10 → ℕ) (h : Bounds W v) :
    (program W K p).eval data m (fun i => (v i : Word W)) = (values v : Word W) := by
  simpa using program_eval p (fun i => (data i).val) (fun i => (m i).val) v h

theorem values_lt (v : Fin 10 → ℕ) (h : Bounds W v) (degree : 2≤v 2) (tags : 0<v 3)
    (endPins : 2+v 8+2*(v 2*v 3) ≤ 2^W) : values v < 2^W := by
  have t := Nat.mod_lt (v 0) tags
  have two := Nat.mul_le_mul_right (v 3) degree
  have small (a q j : ℕ) := Nat.mul_le_mul_left (v 3) (slot_le a q j)
  have h1 := small (v 5) ((v 0%v 3)/v 4) (v 6+v 7)
  have h2 := small (v 5) ((v 0%v 3)/v 4) (v 6+(v 7-1))
  have hlut := h.inputs 9
  simp only [Nat.mul_one] at h1 h2
  unfold values
  dsimp only
  split_ifs <;> omega

end ThreeFlat.Diagonal.TraceBucketRelay

end OAI
