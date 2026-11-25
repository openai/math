import OAI.Computability.IntegerMultiplication.Port.Specialize
import OAI.Computability.IntegerMultiplication.Net.First

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Shuttle
open Motif Halo IntegerMultiplication.Port Matrix Finset Tensor
noncomputable section
-- Labels that occur; collect from ops or simply limit to past≤3
abbrev live (m : Mark) : Prop := limit m

variable {T : Type} [DecidableEq T] [Fintype T]
def fixture : Finset (Place T) :=
  (univ.image Place.opening) ∪
  ((univ : Finset (Fin 4 × Keys T)).image (fun w => Place.box w.1.val w.2)) ∪
  ((univ : Finset (Fin 4 × Keys T)).image (fun w => Place.ybox w.1.val w.2)) ∪
  ((univ : Finset (S × Motif.Sub T)).image (fun w => Place.low w.1 w.2)) ∪
  ((univ : Finset (S × Motif.Sub T × T)).image (fun w => Place.leanOn w.1 w.2.1 w.2.2)) ∪
  ((univ : Finset (S × Motif.Sub T)).image (fun w => Place.high w.1 w.2)) ∪
  {.full,.clear}
attribute [local irreducible] fixture
private theorem cardedG (m : (Place T)) (h : limit m) : m∈fixture := by
  simp only [fixture,mem_union]
  cases m with
  | opening x =>
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (?_))))))
    exact mem_image.mpr ⟨x,mem_univ _,rfl⟩
  | box k a =>
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (?_))))))
    exact mem_image.mpr ⟨(⟨k,(by change k≤3 at h; omega)⟩,a),mem_univ _,rfl⟩
  | ybox k a =>
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (?_)))))
    exact mem_image.mpr ⟨(⟨k,(by change k≤3 at h; omega)⟩,a),mem_univ _,rfl⟩
  | low k a =>
    refine Or.inl (Or.inl (Or.inl (Or.inr (?_))))
    exact mem_image.mpr ⟨(k,a),mem_univ _,rfl⟩
  | leanOn k a t =>
    refine Or.inl (Or.inl (Or.inr (?_)))
    exact mem_image.mpr ⟨(k,a,t),mem_univ _,rfl⟩
  | high k a =>
    refine Or.inl (Or.inr (?_))
    exact mem_image.mpr ⟨(k,a),mem_univ _,rfl⟩
  | clear =>
    refine Or.inr (?_)
    simp
  | full =>
    refine Or.inr (?_)
    simp

-- choose bill-of-materials once
open Classical in
def manifestQ (a b : Mark) :=
  if x : Place.road align a b then (usage a b x).choose else []
theorem obligation (a b : Mark) (x : Place.road align a b) :
    addressFrame b - addressFrame a = ((manifestQ a b).map value).sum ∧
      ((manifestQ a b).length : ℤ) ≤ allow a b := by
  rw [manifestQ,dite_eq_left x]
  exact (usage a b x).choose_spec

-- Need finite set of a,b either for live ones or those connected. road nonstation forces.
theorem checked (a b : Mark) (x : Place.road align a b) (d : a ≠ b) :
    live a ∧ live b := by
  have ht (j : S) : j.val+1 ≤ 3 := by omega
  let : Nonempty Piece := pieces
  have e : ∀ t u, align t u → t≠u := by rintro t u e rfl; simp [align, Triple.bit] at e
  obtain ⟨i,j,_⟩ := Or.resolve_left
    (Halo.passes Triple.rational (fun _ => True) align (Triple.ratPermission) e a b x) d
  exact ⟨i,j⟩

def gather {L I : Type} [DecidableEq I] [Fintype I]
    (F : Finset L) (M : L→Mat I ℚ) (book : L → L → List (Outer I ℚ)) : Finset ℚ :=
  ((F ×ˢ ((univ:Finset I) ×ˢ (univ:Finset I))).image
    (fun v => M v.1 v.2.1 v.2.2)) ∪
  ((F ×ˢ F).biUnion fun v =>
    (book v.1 v.2).toFinset.biUnion fun x => univ.image x.1 ∪ univ.image x.2)

private theorem mem_g {L I : Type} [DecidableEq I] [Fintype I]
    (F : Finset L) (M : L→Mat I ℚ) (book : L → L → List (Outer I ℚ)) (a b : L) (ha : a ∈ F) (hb : b∈F) (i l : I) :
    M a i l ∈ gather F M book ∧ ∀ v∈ book a b, v.1 i ∈ gather F M book ∧ v.2 i∈ gather F M book := by
  constructor
  · unfold gather
    apply Finset.mem_union_left
    exact mem_image.mpr ⟨⟨a,i,l⟩,by simp [ha],rfl⟩
  intro v h
  have hh : (a,b)∈F ×ˢ F := Finset.mem_product.mpr ⟨ha,hb⟩
  have e (r : ℚ) (h' : r∈univ.image v.1 ∪ univ.image v.2) : r∈gather F M book := by
    unfold gather
    exact mem_union_right _
      (mem_biUnion.mpr ⟨(a,b),hh,mem_biUnion.mpr ⟨v,by simpa using h,h'⟩⟩)
  exact ⟨e _ (mem_union_left _ (mem_image_of_mem _ (mem_univ _))),e _ (mem_union_right _ (mem_image_of_mem _ (mem_univ _)))⟩

def catalog : Finset ℚ := gather fixture addressFrame manifestQ
theorem cited (a : Mark) (x : live a) (i j : Point) :
    addressFrame a i j ∈ catalog := (mem_g fixture addressFrame manifestQ a a (cardedG _ x) (cardedG _ x) i j).1
theorem partQ (a b : Mark) (x : live a) (y : live b) (v : Outer Point ℚ)
    (h : v ∈ manifestQ a b) (i : Point) : v.1 i ∈ catalog ∧ v.2 i ∈ catalog :=
    (mem_g fixture addressFrame manifestQ a b (cardedG _ x) (cardedG _ y) i i).2 v h

attribute [irreducible] catalog
def base : ℕ := (eventually catalog).choose
private theorem base_clause : base.Prime ∧ 2<base ∧ ∀ x∈catalog, x.den<base ∧ x.num.natAbs<base :=
  (eventually catalog).choose_spec
theorem base_prime : base.Prime := base_clause.1
theorem base_large : 2<base := base_clause.2.1
attribute [irreducible] base
theorem mTitle {x : ℚ} (h : x∈catalog) : x.den<base ∧ x.num.natAbs<base := base_clause.2.2 x h
theorem base_record {x : ℚ} (h : x∈catalog) (j : ℕ) : Token x (read base j x) ∧
    (x ≠ 0 → IsUnit (read base j x)) :=
  ⟨match_denom base_prime j _ (base_clause.2.2 x h).1,
    recorded base_prime _ _ (base_clause.2.2 x h).1 (base_clause.2.2 x h).2⟩

def deck (j : ℕ) (a : Mark) : Mat Point (Tower base j) :=
  Matrix.of fun x y => read base j (addressFrame a x y)
def vector (j : ℕ) (v : Vec Point ℚ) : Vec Point (Tower base j) :=
  fun x => read base j (v x)
def component (j : ℕ) (v : Outer Point ℚ) : Mat Point (Tower base j) :=
  vecMulVec (vector j v.1) (vector j v.2)
theorem sum_from (a b : Mark) (x : Place.road align a b) (j : ℕ) :
    ((manifestQ a b).map (component j)).sum = deck j b - deck j a := by
  have e := (obligation _ _ x).1
  by_cases d : a=b
  · subst b
    have : manifestQ a a=[] := List.eq_nil_of_length_eq_zero (by
      have z := (obligation a a x).2; simp only [allow,Place.stay_allowance] at z; omega)
    simp [this]
  obtain ⟨la,lb⟩ := checked a b x d
  ext i k
  have ih : ∀ s : List (Outer Point ℚ), (∀ v∈s, ∀ l, v.1 l∈catalog ∧ v.2 l∈catalog) →
    Token ((s.map value).sum i k) ((s.map (component j)).sum i k) := by
    intro s; induction s with
    | nil => intro _; exact Token.zero
    | cons f s ih =>
      intro h
      simp only [List.map_cons, List.sum_cons,Matrix.add_apply]
      apply Token.add _ (ih _)
      · exact ((base_record (h f List.mem_cons_self i).1 j).1).mul ((base_record (h f List.mem_cons_self k).2 j).1)
      exact fun f z l => h f (List.mem_cons_of_mem _ z) l
  have hs := ih (manifestQ a b) (partQ a b la lb)
  rw [← e] at hs
  apply hs.unique
  exact Token.sub (base_record (cited _ lb i k) j).1 (base_record (cited _ la i k) j).1

open Carnival
theorem corridor (w : FPbit) : live (circuit.init w) ∧ live (circuit.sink (route w)) := by
  rw [circuit,init_net,sink_net]
  rcases w with a|a|⟨j,k,r⟩
  · change live (.opening a) ∧ live (.ybox 3 a)
    simp [live, limit]
  · change live (.ybox 0 a) ∧ live (.box 3 a)
    simp [live, limit]
  · have hj : j.val < 3 := j.isLt
    change live (if j.val < 0 then .full else .clear) ∧
      live (if j.val < 3 then .full else .clear)
    simp [live, limit, hj]

theorem flowEnds (j : ℕ) (w : FPbit) :
    deck j (circuit.sink (route w)) - deck j (circuit.init w) = 1 := by
  have ⟨a,b⟩ := corridor w
  ext i k
  have hs := Token.sub (base_record (cited _ b i k) j).1 (base_record (cited _ a i k) j).1
  change Token ((addressFrame _ - addressFrame _) i k)
      ((deck j (circuit.sink (route w)) - deck j _) i k) at hs
  rw [terminals,Matrix.one_apply] at hs
  rw [Matrix.one_apply]
  split_ifs with e
  · rw [ite_eq_left e] at hs; exact hs.unique Token.unit
  rw [ite_eq_right e] at hs; exact hs.unique Token.zero

end
end Net.Shuttle

end IntegerMultiplication
end Computability
end OAI
