import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineBudget
import OAI.Computability.NearSquareRoot.InterchangeROMAddressMirrorHeader

/-! # Connecting projected addresses and class masks to the actual layout -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace AffineAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry
  IntegerMultiplication.Bits IntegerMultiplication.Strip IntegerMultiplication.Adic
  IntegerMultiplication.Port IntegerMultiplication.Loom IntegerMultiplication.Strip.Dims
open InterchangeROMAddress (location projection projection_correct header)
open InterchangeAffineMask (inspect)

theorem follow_cast {A B : Type} {s : Series A} {t : Series B} (e : Adopt s t)
    (i : Fin s.count) : t.follow (Fin.cast e.cost i) = e.cast (s.follow i) := by
  have tab := e.route id
  let j : Fin t.count := Fin.cast e.cost i
  have left : j.val < (t.tab id).length := by simpa only [Series.card] using j.isLt
  have right : i.val < (s.tab (id ∘ e.cast)).length := by simpa only [Series.card] using i.isLt
  have p : (t.tab id)[j.val]'left = (s.tab (id ∘ e.cast))[i.val]'right :=
    List.getElem_of_eq tab _
  rw [t.get id j, s.get (id ∘ e.cast) i] at p
  exact p

theorem cast_index {A B : Type} {s : Series A} {t : Series B} (e : Adopt s t)
    (x : A) : t.index (e.cast x) = Fin.cast e.cost (s.index x) := by
  have g := follow_cast e (s.index x)
  rw [Series.follow_index] at g
  rw [← g,Series.index_follow]

variable {J : Type} {n b f : ℕ} (ord : J ≃ Fin n) (P G B : Tape)
    (validP : solid P) (validG : solid G) (validB : solid B) (hb : 2 ≤ b)

private theorem goodField (hb : 2 ≤ b) : solid (field b f) := by
  induction f with
  | zero => simp [field,solid]
  | succ f ih => exact (solid_cons ..).mpr ⟨hb,ih⟩

private theorem goodRack (d : Tape) (ok : solid d) (m : ℕ) : solid (Loom.Rack d m) := by
  induction m with
  | zero => simp [Loom.Rack,solid]
  | succ m ih => exact (solid_cat ..).mpr ⟨ok,ih⟩

def selected (ord : J ≃ Fin n) (P G B : Tape) (validP : solid P) (validG : solid G)
    (validB : solid B) (hb : 2 ≤ b) (s : Spot J) : Geometry where
  pre := preamble ord P G (field b f) s
  field := field b f
  post := appendix ord G B (field b f) s
  preSolid := by
    obtain ⟨t,j⟩ := s
    cases t <;> simp [leftF,goodRack _ (goodField hb),validP,validG]
  fieldSolid := goodField hb
  postSolid := by
    obtain ⟨t,j⟩ := s
    cases t <;> simp [rightF,goodRack _ (goodField hb),validB,validG]

variable [DecidableEq J] [NeZero b]

noncomputable def comparison (ord : J ≃ Fin n) (P G B : Tape) (validP : solid P) (validG : solid G)
    (validB : solid B) (hb : 2 ≤ b) (x y : Spot J) (h : InterchangeAffineMask.Header Word) : Comparison :=
  ⟨selected (f:=f) ord P G B validP validG validB hb x,
    selected (f:=f) ord P G B validP validG validB hb y,
    (oneStop ord x (p:=b) (j:=f) (P:=P) (G:=G) (B:=B)).view.cost.symm.trans
      (oneStop ord y (p:=b) (j:=f) (P:=P) (G:=G) (B:=B)).view.cost,
    h⟩

omit [NeZero b] in
theorem input (x y : Spot J) (h : InterchangeAffineMask.Header Word) :
    (comparison (f:=f) ord P G B validP validG validB hb x y h).desc =
      (h, projection (location ord b x, header f P G B),
          projection (location ord b y, header f P G B)) := by
  rw [projection_correct,projection_correct]
  rfl

theorem answer (x y : Spot J) (h : InterchangeAffineMask.Header Word) :
    (comparison (f:=f) ord P G B validP validG validB hb x y h).result =
      stripe (arrays ord (line b f) P G B) (fun z =>
        send (inspect (h,born (number (ask z x)),born (number (ask z y))))) := by
  let a := oneStop ord x (p:=b) (j:=f) (P:=P) (G:=G) (B:=B)
  let b' := oneStop ord y (p:=b) (j:=f) (P:=P) (G:=G) (B:=B)
  let c := comparison (f:=f) ord P G B validP validG validB hb x y h
  refine (a.view.packet (fun z => send (inspect (c.query z)))).trans ?_
  apply congrArg (stripe _)
  funext z
  have eA := (one_use ord x z (ask z x)).1
  have eB := (one_use ord y z (ask z y)).1
  change (a.view.cast z).2.1 = _ at eA
  change (b'.view.cast z).2.1 = _ at eB
  let aR := Board (preamble ord P G (field b f) x) (line b f) (appendix ord G B (field b f) x)
  let bR := Board (preamble ord P G (field b f) y) (line b f) (appendix ord G B (field b f) y)
  have iA := cast_index a.view z
  have iB := cast_index b'.view z
  have position : Fin.cast c.aligned (aR.index (a.view.cast z)) = bR.index (b'.view.cast z) := by
    rw [iA,iB]
    rfl
  have right : bR.follow (Fin.cast c.aligned (aR.index (a.view.cast z))) = b'.view.cast z := by
    exact (congrArg bR.follow position).trans (bR.follow_index _)
  have left : aR.follow (Fin.cast rfl (aR.index (a.view.cast z))) = a.view.cast z := by
    exact aR.follow_index _
  change send (inspect (h,born (((line b f).index (aR.follow (Fin.cast rfl (aR.index (a.view.cast z)))).2.1)).val,
    born (((line b f).index (bR.follow (Fin.cast c.aligned (aR.index (a.view.cast z)))).2.1)).val)) = _
  rw [left,right,rank_number,rank_number,eA,eB]

omit [NeZero b] in
include validP validG validB hb in
/-- Each addressed field occurs on both wings. The two rank enumerations
therefore cost at most a constant times the enclosing volume. -/
theorem square_fit (i : J) : room (field b f)^2 ≤ (arrays ord (line b f) P G B).count := by
  let d := field b f
  let fieldLine := line b f
  let wing := threads fieldLine ord
  have one : fieldLine.count = room d := Dims.space _
  have hD : solid d := goodField hb
  obtain ⟨slot,_⟩ := monoRay fieldLine ord (Adopt.same _) i
  have low : room d ≤ wing.count := by
    rw [show wing.count = _ from slot.view.cost]
    simp only [Board,Series.count_cart,Dims.space]
    rw [one]
    have hl := wide _ (goodRack d hD (ord i).val)
    have hr := wide _ (goodRack d hD (n-(ord i).val-1))
    exact (Nat.le_mul_of_pos_right _ hr).trans (Nat.le_mul_of_pos_left _ hl)
  have z : wing.count*wing.count ≤ (arrays ord fieldLine P G B).count := by
    simp only [arrays,Loom.Path,Board,Series.count_cart,Dims.space]
    have p := wide _ validP
    have g := wide _ validG
    have q := wide _ validB
    have z₁ := Nat.le_mul_of_pos_right wing.count q
    exact (Nat.mul_le_mul_left wing.count (z₁.trans (Nat.le_mul_of_pos_left _ g))).trans
      (Nat.le_mul_of_pos_left _ p)
  exact (by simpa only [pow_two] using (Nat.mul_le_mul low low).trans z)

omit [NeZero b] in
theorem comparison_budget (x y : Spot J) (h : InterchangeAffineMask.Header Word) (d : ℕ) :
    let c := comparison (f:=f) ord P G B validP validG validB hb x y h
    c.budget d ≤ ((arrays ord (line b f) P G B).count+1)*localPrice d (size c.desc) := by
  let c := comparison (f:=f) ord P G B validP validG validB hb x y h
  have h₁ : (arrays ord (line b f) P G B).count = c.first.rows.count := (oneStop ord x).view.cost
  have h₂ : (arrays ord (line b f) P G B).count = c.second.rows.count := (oneStop ord y).view.cost
  have sq := square_fit (f:=f) ord P G B validP validG validB hb x.2
  exact (c.budget_le d (sq.trans h₁.le) (sq.trans h₂.le)).trans (by rw [h₁])

end AffineAddress

end NearSquareRoot
end Computability
end OAI
