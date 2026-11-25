import OAI.Computability.NearSquareRoot.PrecisionBlockPhaseRank
import OAI.Computability.NearSquareRoot.SynchronizedAxisLayout
import OAI.Computability.NearSquareRoot.CRTTableCoefficients
import OAI.Computability.NearSquareRoot.SynchronizedPlacedTables
import OAI.Computability.NearSquareRoot.SynchronizedPlacementTape

/-! # Removing an axis field from a packed block address

Number spectator fibers by deleting the selected field of the padded mixed-radix
address. The column is the field itself. Both projections are divisions and
reductions on the original block rank.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FieldSplit
open Finset

/-- Number of assignments of the coordinates above the selected field. -/
def upper {n : ℕ} (r : Fin n → ℕ) (j : Fin n) := ∏ i ∈ Ioi j, r i

private theorem fullRadix {n : ℕ} (r : Fin n → ℕ) (j : Fin n) :
    (∏ i, r i) = upper r j * r j * CRT.«prefix» r j := by
  have split : univ = insert j (Ioi j ∪ Iio j) := by
    ext t
    simp only [mem_univ, mem_insert, mem_union, mem_Ioi, mem_Iio, true_iff]
    exact (lt_trichotomy t j).elim (fun h => Or.inr (Or.inr h))
      (fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))
  have disj : Disjoint (Ioi j) (Iio j) :=
    disjoint_left.mpr fun _ h₁ h₂ => (not_lt_of_ge (mem_Ioi.mp h₁).le) (mem_Iio.mp h₂)
  rw [split, prod_insert (by simp), prod_union disj]
  unfold upper CRT.«prefix»
  ac_rfl

private theorem prefix_fin {n : ℕ} (r : Fin n → ℕ) (j : Fin n) :
    CRT.«prefix» r j = ∏ t : Fin j.val, r (Fin.castLE j.isLt.le t) := by
  unfold CRT.«prefix»
  exact prod_bij' (fun t ht => (⟨t.val, show t < j from mem_Iio.mp ht⟩ : Fin j.val))
    (fun t _ => Fin.castLE j.isLt.le t)
    (fun _ _ => mem_univ _) (fun t _ => mem_Iio.mpr t.isLt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Remove a middle field from a number with lower, middle and upper radices
`p,m,h`. The first component retains the original order of all other bits. -/
def split (p m h : ℕ) : Fin (h*m*p) ≃ Fin (h*p) × Fin m :=
  finProdFinEquiv.symm.trans <|
    (finProdFinEquiv.symm.prodCongr (Equiv.refl (Fin p))).trans <|
    (Equiv.prodAssoc (Fin h) (Fin m) (Fin p)).trans <|
    ((Equiv.refl (Fin h)).prodCongr (Equiv.prodComm _ _)).trans <|
    (Equiv.prodAssoc (Fin h) (Fin p) (Fin m)).symm.trans
      (finProdFinEquiv.prodCongr (Equiv.refl _))

/-- Executable projections of a block rank. -/
def row (p m q : ℕ) := q%p + p*(q/(p*m))
def col (p m q : ℕ) := q/p%m

theorem split_snd {p m h : ℕ} (q : Fin (h*m*p)) :
    ((split p m h q).2).val = col p m q.val := rfl

theorem split_fst {p m h : ℕ} (q : Fin (h*m*p)) :
    ((split p m h q).1).val = row p m q.val := by
  change q.val%p+p*(q.val/p/m) = _
  rw [Nat.div_div_eq_div_mul]
  rfl

private theorem split_inv {p m h : ℕ} (s : Fin (h*p)) (t : Fin m) :
    ((split p m h).symm (s,t)).val = s.val%p + p*(t.val + m*(s.val/p)) := rfl

/-- Splice a padded column back into the original block field. -/
def join (p m fiber slot : ℕ) : ℕ := fiber%p + p*(slot + m*(fiber/p))

theorem join_projections {p m h : ℕ} (q : Fin (h*m*p)) :
    join p m (row p m q.val) (col p m q.val) = q.val := by
  rw [← split_fst q, ← split_snd q]
  exact (split_inv (split p m h q).1 (split p m h q).2).symm.trans
    (congrArg Fin.val ((split p m h).symm_apply_apply q))

private theorem column_eq {n : ℕ} (r : Fin n → ℕ) (j : Fin n) (x : ∀ i, Fin (r i)) :
    col (CRT.«prefix» r j) (r j) (finPiFinEquiv x).val = (x j).val := by
  rw [prefix_fin]
  exact congrArg Fin.val (congrFun (finPiFinEquiv.symm_apply_apply x) j)

private theorem rank_change {n : ℕ} (r : Fin n → ℕ) (j : Fin n)
    (x y : ∀ i, Fin (r i)) (same : ∀ i, i ≠ j → x i = y i) :
    (finPiFinEquiv x).val + CRT.«prefix» r j * (y j).val =
      (finPiFinEquiv y).val + CRT.«prefix» r j * (x j).val := by
  rw [← CRT.rank_eq_finPiFinEquiv r x, ← CRT.rank_eq_finPiFinEquiv r y, CRT.rank, CRT.rank]
  rw [← sum_erase_add _ _ (mem_univ j), ← sum_erase_add (f := fun i => CRT.«prefix» r i * (y i).val) _ (mem_univ j)]
  have e : (∑ i ∈ univ.erase j, CRT.«prefix» r i * (x i).val) =
      ∑ i ∈ univ.erase j, CRT.«prefix» r i * (y i).val :=
    sum_congr rfl fun i hi => by rw [same i (ne_of_mem_erase hi)]
  rw [e]
  ac_rfl

private def packing {n : ℕ} (r : Fin n → ℕ) (j : Fin n) :
    (∀ i, Fin (r i)) ≃ Fin (upper r j * CRT.«prefix» r j) × Fin (r j) :=
  finPiFinEquiv.trans ((finCongr (fullRadix r j)).trans (split ..))

private theorem packing_snd {n : ℕ} (r : Fin n → ℕ) (j : Fin n) (x : ∀ i, Fin (r i)) :
    (packing r j x).2 = x j := Fin.ext (column_eq r j x)

private theorem packing_indep {n : ℕ} (r : Fin n → ℕ) (j : Fin n)
    (x y : ∀ i, Fin (r i)) (same : ∀ i, i ≠ j → x i = y i) :
    (packing r j x).1 = (packing r j y).1 := by
  let z := packing r j x
  let w := packing r j y
  have inv (a : ∀ i, Fin (r i)) :
      (finPiFinEquiv a).val =
        (packing r j a).1.val % CRT.«prefix» r j + CRT.«prefix» r j *
        ((a j).val + r j * ((packing r j a).1.val / CRT.«prefix» r j)) := by
    have h := split_inv (packing r j a).1 (packing r j a).2
    rw [Prod.mk.eta] at h
    change ((split _ _ _).symm (split _ _ _ _)).val = _ at h
    rw [Equiv.symm_apply_apply, packing_snd] at h
    exact h
  have eq := rank_change r j x y same
  rw [inv x, inv y] at eq
  let p := CRT.«prefix» r j
  let m := r j
  change z.1.val%p + p*((x j).val + m*(z.1.val/p)) + p*(y j).val =
    w.1.val%p + p*((y j).val + m*(w.1.val/p)) + p*(x j).val at eq
  have eql : z.1.val%p + (p*m)*(z.1.val/p) = w.1.val%p + (p*m)*(w.1.val/p) := by
    nlinarith only [eq]
  have pp : 0 < p := prod_pos fun i _ => (x i).pos
  have pm : 0 < m := (x j).pos
  have zu := Nat.mod_lt z.1.val pp
  have wu := Nat.mod_lt w.1.val pp
  have pmge : p ≤ p*m := Nat.le_mul_of_pos_right _ pm
  have low := congrArg (· % (p*m)) eql
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (zu.trans_le pmge),
    Nat.mod_eq_of_lt (wu.trans_le pmge)] at low
  have high : z.1.val / p = w.1.val / p := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos pp pm) (by omega)
  apply Fin.ext
  change z.1.val = w.1.val
  rw [← Nat.mod_add_div z.1.val p, low, high, Nat.mod_add_div]

private abbrev Remaining {n : ℕ} (r : Fin n → ℕ) (j : Fin n) := (s : {i // i ≠ j}) → Fin (r s.val)

private def layoutDigits {n : ℕ} (r : Fin n → ℕ) (j : Fin n) :
    Fin (r j) × Remaining r j ≃ Fin (upper r j * CRT.«prefix» r j) × Fin (r j) :=
  (Equiv.piSplitAt j _).symm.trans (packing r j)

private theorem layoutDigits_snd {n : ℕ} (r : Fin n → ℕ) (j : Fin n) (u : Fin (r j) × Remaining r j) :
    (layoutDigits r j u).2 = u.1 := by
  let e := Equiv.piSplitAt j (fun i => Fin (r i))
  change (packing r j (e.symm u)).2 = u.1
  exact (packing_snd r j (e.symm u)).trans (congrArg Prod.fst (e.apply_symm_apply u))

/-- Rank the remaining digits by fixing the removed field to `z`. Removing
the field recovers the same rank regardless of its value. -/
private def spectatorRank {n : ℕ} (r : Fin n → ℕ) (j : Fin n) (z : Fin (r j)) :
    Remaining r j ≃ Fin (upper r j * CRT.«prefix» r j) where
  toFun s := (layoutDigits r j (z,s)).1
  invFun t := ((layoutDigits r j).symm (t,z)).2
  left_inv s := by
    have pair : ((layoutDigits r j (z,s)).1,z) = layoutDigits r j (z,s) :=
      Prod.ext rfl (layoutDigits_snd r j (z,s)).symm
    change ((layoutDigits r j).symm ((layoutDigits r j (z,s)).1,z)).2 = s
    rw [pair, Equiv.symm_apply_apply]
  right_inv t := by
    let u := (layoutDigits r j).symm (t,z)
    have eval : layoutDigits r j u = (t,z) := Equiv.apply_symm_apply ..
    have fix : z = u.1 := (congrArg Prod.snd eval).symm.trans (layoutDigits_snd r j u)
    change (layoutDigits r j (z,u.2)).1 = t
    rw [fix]
    exact congrArg Prod.fst eval

private theorem spectatorRank_val {n : ℕ} (r : Fin n → ℕ) (j : Fin n) (z : Fin (r j))
    (x : ∀ i, Fin (r i)) :
    (spectatorRank r j z (fun t => x t.val)).val =
      row (CRT.«prefix» r j) (r j) (finPiFinEquiv x).val := by
  let y := (Equiv.piSplitAt j (fun i => Fin (r i))).symm (z, fun t => x t.val)
  change (packing r j y).1.val = _
  rw [packing_indep r j y x (fun i hi => by simp [y, Equiv.piSplitAt_symm_apply, hi])]
  exact split_fst _

/-- An explicit spectator ordering for the synchronized block. Numbering the
local fields by their supplied ranks fixes this equivalence completely. -/
def orderedSpectators {n : ℕ} {A : Fin n → Type} [∀ i, Fintype (A i)]
    (r : Fin n → ℕ) (e : ∀ i, A i ≃ Fin (r i)) (j : Fin n) (z : Fin (r j)) :
    ((s : {i // i ≠ j}) → A s.val) ≃ Fin (Fintype.card ((s : {i // i ≠ j}) → A s.val)) :=
  let equiv := (Equiv.piCongrRight (fun s : {i // i ≠ j} => e s.val)).trans (spectatorRank r j z)
  equiv.trans (finCongr (by simpa using (Fintype.card_congr equiv).symm))

theorem orderedSpectators_val {n : ℕ} {A : Fin n → Type} [∀ i, Fintype (A i)]
    (r : Fin n → ℕ) (e : ∀ i, A i ≃ Fin (r i)) (j : Fin n) (z : Fin (r j)) (x : ∀ i,A i) :
    (orderedSpectators r e j z (fun s => x s.val)).val =
      row (CRT.«prefix» r j) (r j) (finPiFinEquiv (fun i => e i (x i))).val :=
  spectatorRank_val r j z (fun i => e i (x i))

end FieldSplit

namespace FieldSplit
open IntegerMultiplication Code Strip Staff

theorem prefix_take {n : ℕ} (r : Fin n → ℕ) (j : Fin n) :
    CRT.«prefix» r j = ((List.ofFn r).take j.val).prod := (CRT.take_ofFn_prod_prefix r j).symm

theorem row_realizes {J : Type} {s : Regime J} {p m q : J → ℕ}
    (P : Realizes s p) (M : Realizes s m) (Q : Realizes s q) :
    Realizes s (fun i => row (p i) (m i) (q i)) :=
  (Q.rem P).plus (P.times (Q.dividing (P.times M)))

theorem col_realizes {J : Type} {s : Regime J} {p m q : J → ℕ}
    (P : Realizes s p) (M : Realizes s m) (Q : Realizes s q) :
    Realizes s (fun i => col (p i) (m i) (q i)) :=
  (Q.dividing P).rem M

theorem join_realizes {J : Type} {s : Regime J} {p m f t : J → ℕ}
    (P : Realizes s p) (M : Realizes s m) (F : Realizes s f) (T : Realizes s t) :
    Realizes s (fun i => join (p i) (m i) (f i) (t i)) :=
  (F.rem P).plus (P.times (T.plus (M.times (F.dividing P))))

end FieldSplit

namespace BoxFin
open SynchronizedBlocks ShortFourier BatchWord

variable {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box)
    [∀ i, NeZero (modulus box i)]

/-- The local powers of two, ordered from least to most significant. -/
def blockFieldRadix (box : List (ℕ × ℕ)) (b : Fin (box.length/4)) (i : Fin (count b)) : ℕ :=
  2^(box.get (axis b i)).1

/-- Explicit spectator-fiber numbering for the `BatchWord.axisLayout` of
any selected coordinate in a synchronized block. -/
noncomputable def blockSpectators (b : Fin (box.length/4)) (t : Fin (count b)) :
    Spectators (fun i => modulus box (axis b i)) (fun i => padding box (axis b i)) t ≃
      Fin (Fintype.card (Spectators (fun i => modulus box (axis b i)) (fun i => padding box (axis b i)) t)) :=
  FieldSplit.orderedSpectators (blockFieldRadix box b) (fun i => field hb (axis b i)) t
    ⟨0,Nat.two_pow_pos _⟩

/-- Deleting the selected bit field is exactly the row read by the borrowed
batch lookup. Retaining that field gives its padded column. -/
theorem blockAxisLayout_fields (b : Fin (box.length/4)) (t : Fin (count b))
    (x : BlockAddress (BoxAxis box) b) :
    let d := blockFieldRadix box b
    let q := (blockAddressRank hb b x).val
    let addr := axisLayout (fun i => modulus box (axis b i)) (fun i => padding box (axis b i))
      (blockSpectators hb b) t x
    addr.1.val = FieldSplit.row (CRT.«prefix» d t) (d t) q ∧
      (finSumFinEquiv addr.2).val = FieldSplit.col (CRT.«prefix» d t) (d t) q := by
  let d := blockFieldRadix box b
  let e (i : Fin (count b)) := field hb (axis b i)
  exact ⟨FieldSplit.orderedSpectators_val d e t ⟨0,Nat.two_pow_pos _⟩ x,
    (FieldSplit.column_eq d t (fun i => e i (x i))).symm⟩

/-- Inserting a row and column in the selected physical field recovers the
original tape position. This is the inverse map for relabeling a block by an
explicit permutation of its spectator and axis addresses. -/
theorem blockAxisLayout_inverse (b : Fin (box.length/4)) (t : Fin (count b))
    (u : Fin (Fintype.card (Spectators (fun i => modulus box (axis b i))
      (fun i => padding box (axis b i)) t)) × (Fin (modulus box (axis b t)) ⊕ Fin (padding box (axis b t)))) :
    let d := blockFieldRadix box b
    let e := axisLayout (fun i => modulus box (axis b i)) (fun i => padding box (axis b i))
      (blockSpectators hb b) t
    (blockAddressRank hb b (e.symm u)).val =
      FieldSplit.join (CRT.«prefix» d t) (d t) u.1.val (finSumFinEquiv u.2).val := by
  let d := blockFieldRadix box b
  let e := axisLayout (fun i => modulus box (axis b i)) (fun i => padding box (axis b i))
    (blockSpectators hb b) t
  let q := blockAddressRank hb b (e.symm u)
  have h := blockAxisLayout_fields hb b t (e.symm u)
  change (e (e.symm u)).1.val = FieldSplit.row _ _ q.val ∧
    (finSumFinEquiv (e (e.symm u)).2).val = FieldSplit.col _ _ q.val at h
  rw [Equiv.apply_symm_apply] at h
  change q.val = FieldSplit.join (CRT.«prefix» d t) (d t) u.1.val (finSumFinEquiv u.2).val
  rw [h.1,h.2]
  exact (FieldSplit.join_projections ((finCongr (FieldSplit.fullRadix d t)) q)).symm

/-- The block-rank decoder returns the actual cell selected by the
fifteen-batch scheduler, including every padded and inactive address. -/
theorem blockAxisLayout_lookup (b : Fin (box.length/4)) (t : Fin (count b))
    (x : BlockAddress (BoxAxis box) b) (s : ℕ) (batch : Fin 15) :
    let d := blockFieldRadix box b
    let p := CRT.«prefix» d t
    let a := modulus box (axis b t)
    let q := (blockAddressRank hb b x).val
    let fiberCount := Fintype.card (Spectators (fun i => modulus box (axis b i))
      (fun i => padding box (axis b i)) t)
    let addr := axisLayout (fun i => modulus box (axis b i)) (fun i => padding box (axis b i))
      (blockSpectators hb b) t x
    cellLookup s batch addr = if FieldSplit.col p (d t) q < a then
      SynchronizedBorrowing.lookupRank (SynchronizedBorrowing.first fiberCount batch)
        (SynchronizedBorrowing.size fiberCount batch) a s
        (FieldSplit.row p (d t) q * a + FieldSplit.col p (d t) q) else none := by
  dsimp only
  unfold cellLookup
  obtain ⟨hrow,hcol⟩ := blockAxisLayout_fields hb b t x
  rw [hrow,hcol]

end BoxFin

end NearSquareRoot
end Computability
end OAI
