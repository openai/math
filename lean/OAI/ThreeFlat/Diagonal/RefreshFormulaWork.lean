import OAI.ThreeFlat.Diagonal.RefreshWidthWriter

namespace OAI
/-! # Uniform instruction counts of the refresh demand and width expressions -/

namespace ThreeFlat.Diagonal.RefreshDemandRows.Static

open RAM.PhysicalPinsExpr RAM.MotifRows
open scoped Classical
noncomputable section

variable {n a h k : ℕ}
abbrev Same (f g : Formula n) := f.work=g.work
abbrev PairSame (f g : Formula n × Formula n) := Same f.1 g.1 ∧ Same f.2 g.2
abbrev ColSame (C D : Columns (Formula n)) := C.map Formula.work=D.map Formula.work

theorem folds {I : Type} (l : List I) (f g : I → Formula n) (hf : ∀ i, Same (f i) (g i)) :
    Same (totals (l.map f)) (totals (l.map g)) ∧ Same (biggest (l.map f)) (biggest (l.map g)) := by
  induction l with
  | nil => exact ⟨rfl,rfl⟩
  | cons i l ih =>
    change Same (plus (f i) (totals (l.map f))) (plus (g i) (totals (l.map g))) ∧
      Same (.select .lt (f i) (biggest (l.map f)) (biggest (l.map f)) (f i))
        (.select .lt (g i) (biggest (l.map g)) (biggest (l.map g)) (g i))
    simp only [Same,plus,Formula.work,hf i,ih.1,ih.2,and_self]

theorem demand_work (C D : Columns (Formula n)) (r s b b' : Formula n) (hc : ColSame C D)
    (hr : Same r s) (hb : Same b b') (d : ℕ) (dir : Bool) (i j : ℕ) :
    Same (demand d C r b dir i j) (demand d D s b' dir i j) := by
  have c₀ := congrArg Columns.widths hc
  have c₁ := congrArg Columns.sourceBase hc
  have c₂ := congrArg Columns.sourceSlot hc
  have c₃ := congrArg Columns.portShift hc
  have c₄ := congrArg Columns.laneShift hc
  dsimp only [Columns.map] at c₀ c₁ c₂ c₃ c₄
  cases dir <;> simp only [Same,demand,ite_eq_right (by decide : false ≠ true),↓reduceIte,readColumn,wordAddress,Formula.work,c₀,c₁,c₂,c₃,c₄,hr,hb]

private theorem required_work (z : ℕ) {a b x y : Formula n} (hab : Same a b) (hxy : Same x y) :
    Same (required a x z) (required b y z) := by
  unfold required
  split <;> simp only [Same,Formula.work,hab,hxy]

private theorem score_work {E : Type} [Fintype E] (f g : E → Formula n) (d : E → ℕ)
    (hs : ∀ i, Same (f i) (g i)) : Same (scoreFields f d) (scoreFields g d) := by
  unfold scoreFields
  apply (folds _ _ _ _).2
  intro e
  apply required_work _ _ (hs e)
  change _ + _ + 1 = _ + _ + 1
  rw [(folds _ f g hs).1]

private theorem better_work {x y a b : Formula n × Formula n} (h : PairSame x y) (s : PairSame a b) :
    PairSame (better x a) (better y b) := by
  simp only [PairSame,Same,better,Formula.work,h.1,h.2,s.1,s.2,and_self]

theorem choice_work {E : Type} [Fintype E] (f g : E → Formula n) (d : Fin (k+1) → E → ℕ)
    (hs : ∀ i, Same (f i) (g i)) : PairSame (chooseFields f d) (chooseFields g d) := by
  let rf : Fin (k+1) → Formula n × Formula n := fun j => (scoreFields f (d j),Formula.lit j.val)
  let rg : Fin (k+1) → Formula n × Formula n := fun j => (scoreFields g (d j),Formula.lit j.val)
  have rows (i) : PairSame (rf i) (rg i) := ⟨score_work f g _ hs,rfl⟩
  have fold (l : List (Fin k)) (x y : Formula n × Formula n) (hxy : PairSame x y) :
      PairSame ((l.map fun i => rf i.succ).foldl better x)
        ((l.map fun i => rg i.succ).foldl better y) := by
    induction l generalizing x y with
    | nil => exact hxy
    | cons i l ih => exact ih _ _ (better_work hxy (rows _))
  exact fold _ _ _ (rows _)

theorem refresh_work (C D : Columns (Formula n)) (r s b b' : Formula n)
    (hc : ColSame C D) (hr : Same r s) (hb : Same b b')
    (d : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ) :
    PairSame (refreshChoice C r b d) (refreshChoice D s b' d) :=
  choice_work _ _ _ (fun _e => demand_work C D r s b b' hc hr hb _ _ _ _)

theorem lookup_work {size : ℕ} (f g : Fin size → Formula n) {i j : Formula n} (h : Same i j)
    (hs : ∀ u, Same (f u) (g u)) : Same (rowAt size f i) (rowAt size g j) := by
  induction size with
  | zero => rfl
  | succ s ih =>
    change _ + _ + (f (Fin.last s)).work + _ + 1 = _ + _ + (g (Fin.last s)).work + _ + 1
    rw [h,hs,ih (fun u => f u.castSucc) (fun u => g u.castSucc) (fun u => hs u.castSucc)]

theorem pool_work {size : ℕ} (pool : Fin size → ℕ) (b : ℕ) {c r c' r' : Formula n}
    (hc : Same c c') (hr : Same r r') : Same (outputWidth pool c r b) (outputWidth pool c' r' b) := by
  unfold outputWidth
  change (r.work+_+1)+_+1=(r'.work+_+1)+_+1
  rw [hr]
  congr 2
  apply (folds _ _ _ _).1
  intro j; simp only [Same,RAM.MotifRows.field,Formula.work,hc]

theorem width_work (C D : Columns (Formula n)) (rem rem' i i' count count' : Formula n)
    (hc : ColSame C D) (hr : Same rem rem') (hi : Same i i') (hn : Same count count')
    (pad stride : ℕ) (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ) :
    Same (generateWidth C rem i count pad stride base size bits pool)
      (generateWidth D rem' i' count' pad stride base size bits pool) := by
  let d := 1+h+pad
  let x := cursor (mPort a) d rem i
  let y := cursor (mPort a) d rem' i'
  have hb : Same x.block y.block := by simp only [Same,x,y,cursor,Formula.work,hr,hi]
  have hp : Same x.port y.port := by simp only [Same,x,y,cursor,Formula.work,hr,hi]
  have ht : Same x.slot y.slot := by simp only [Same,x,y,cursor,Formula.work,hr,hi]
  have cut : Same (.cut x.slot (.lit 1)) (.cut y.slot (.lit 1)) := by
    simp only [Same,Formula.work,ht]
  have counts : Same (plus count (.op .mul x.block (.lit stride)))
      (plus count' (.op .mul y.block (.lit stride))) := by
    simp only [Same,plus,Formula.work,hn,hb]
  let chosen := refresh_work C D rem rem' x.block y.block hc hr hb base
  unfold generateWidth
  apply lookup_work _ _ hp
  intro p
  have ext : Same (externalWidth C rem x.block p) (externalWidth D rem' y.block p) :=
    (folds (List.finRange (mPort a)) _ _ (fun j : Fin (mPort a) =>
      demand_work C D rem rem' x.block y.block hc hr hb (mPort a) false j.val p.val)).1
  change x.slot.work+_+(externalWidth C rem x.block p).work+_+1 =
    y.slot.work+_+(externalWidth D rem' y.block p).work+_+1
  rw [ht,ext]
  congr 2
  apply lookup_work _ _ cut
  intro s
  apply lookup_work _ _ chosen.2
  intro j
  exact pool_work _ _ counts chosen.1

end
end ThreeFlat.Diagonal.RefreshDemandRows.Static

end OAI
