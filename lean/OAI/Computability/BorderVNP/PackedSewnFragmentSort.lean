import OAI.Computability.BorderVNP.PackedSewnFragmentSource
import OAI.Computability.BorderVNP.PackedCellAddressCircuit

/-! # Sorting sparse exterior fragments by site and predecessor offset

Each comparator moves a whole four-word record. The two leading bits distinguish padding
and disabled slots. Enabled zero-width records are disabled before sorting.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open VPVNP.VerifierNetwork ParseBatchSort ParseBatchCounts PackedHistogram
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private eqWord eqWord_eval eqWord_size from OAI.Computability.BorderVNP.ParseBatchRowFrame
open private zero_value from OAI.Computability.BorderVNP.PackedCellAddressCircuit

variable {n w : ℕ}

private abbrev bits (w : ℕ) := Fintype.card (Column w)
private abbrev rankBits (w : ℕ) := (w+w)+2
private abbrev totalBits (w : ℕ) := bits w + rankBits w
private abbrev level (n : ℕ) := Nat.clog 2 n

private def widthWord (i : Fin n) (j : Fin w) : Expr (Pin n w) := .input (i,.inr (2,j))

private def enable (i : Fin n) : Expr (Pin n w) :=
  .and (.input (i,.inl false)) (.not (eqWord (widthWord i) (fun _ => .const false)))

private def normBit : Pin n w → Expr (Pin n w)
  | (i,.inl false) => enable i
  | q => .input q

private noncomputable def normalize (n w : ℕ) : Frame (Pin n w) (Pin n w) :=
  (Frame.initial id).step normBit

private theorem norm_values (x : Pin n w → Bool) (i : Fin n) :
    let z := (normalize n w).eval x
    (active z i = true ↔ active x i = true ∧ 0 < (parse x i).run.width) ∧
      (∀ c : Column w, c ≠ .inl false → z (i,c) = x (i,c)) ∧ parse z i = parse x i := by
  intro z
  have init : (Frame.initial (id : Pin n w → _)).eval x = x := funext fun c => Frame.initial_eval id x c
  have field (c : Column w) (h : c ≠ .inl false) : z (i,c) = x (i,c) := by
    cases c with
    | inl b => cases b <;> simp_all [z,normalize,normBit,StatementCircuit.Expr.eval]
    | inr a => simp [z,normalize,normBit,init,StatementCircuit.Expr.eval]
  refine ⟨?_,field,?_⟩
  · have test := eqWord_eval (widthWord (w := w) i) (fun _ => .const false) x
    change _ ↔ (parse x i).run.width = value (fun _ : Fin w => false) at test
    rw [zero_value] at test
    simp only [active,z,normalize,Frame.step_eval,normBit,enable,init,StatementCircuit.Expr.eval,
      Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,Nat.pos_iff_ne_zero]
    exact and_congr_right fun _ => not_congr test
  · simp [parse,parseRow,word,field]

private def keyBits {α : Type*} (pad dead : α) (site start : Fin w → α) : Fin (rankBits w) → α :=
  Fin.cons pad (Fin.cons dead (ParseBatchLookup.prepend site start))

private def raw (i : Fin (2^level n)) (c : Column w) : Expr (Pin n w) :=
  if h : i.val < n then .input (⟨i.val,h⟩,c) else .const false

private noncomputable def encode (i : Fin (2^level n)) : Fin (totalBits w) → Expr (Pin n w) :=
  ParseBatchLookup.prepend
    (keyBits (.const (decide (n ≤ i.val))) (.not (raw i (.inl false)))
      (fun j => raw i (.inr (0,j))) (fun j => raw i (.inr (1,j))))
    (fun j => raw i ((Fintype.equivFin (Column w)).symm j))

private noncomputable def loaded (n w : ℕ) : Frame (Pin n w) (Pins (level n) (totalBits w)) :=
  (normalize n w).step (fun q => encode q.1 q.2)

private def index (i : Fin n) : Fin (2^level n) := i.castLE (Nat.le_pow_clog (by decide) n)

/-- Sort the live sparse rectangle. All four numerical fields and the copy flag remain
attached to their original row. The enabled positive-width rows occupy its initial slots. -/
noncomputable def sortedFrame (n w : ℕ) : Frame (Pin n w) (Pin n w) :=
  (phases (level n) le_rfl (loaded n w)).select (fun q =>
    (index q.1,ParseBatchLookup.lowPin (rankBits w) (Fintype.equivFin (Column w) q.2)))

private theorem bound_prepend {α : Type*} {a l : ℕ} (P : α → Prop) (h : Fin a → α) (t : Fin l → α)
    (hh : ∀ i,P (h i)) (ht : ∀ i,P (t i)) (i : Fin (l+a)) : P (ParseBatchLookup.prepend h t i) := by
  induction a with
  | zero => exact ht i
  | succ a ih =>
    refine Fin.cases (hh 0) (fun j => ?_) i
    simpa only [ParseBatchLookup.prepend,Fin.cons_succ] using ih (fun k => h k.succ) (fun k => hh k.succ) j

private theorem encode_size (i : Fin (2^level n)) (j : Fin (totalBits w)) : (encode i j).size ≤ 2 := by
  have h (c : Column w) : (raw i c).size = 1 := by unfold raw; split <;> rfl
  apply bound_prepend (fun e : Expr (Pin n w) => e.size ≤ 2)
  · intro k
    refine Fin.cases (by decide : (1:ℕ) ≤ 2) (fun m => ?_) k
    refine Fin.cases (by change (raw i (.inl false : Column w)).size+1 ≤ 2; rw [h]) (fun a => ?_) m
    change (ParseBatchLookup.prepend (fun j => raw i (.inr (0,j))) (fun j => raw i (.inr (1,j))) a : Expr (Pin n w)).size ≤ 2
    exact bound_prepend (fun e : Expr (Pin n w) => e.size ≤ 2) _ _ (fun b => (h _).le.trans (by decide))
      (fun b => (h _).le.trans (by decide)) _
  · intro k; exact (h _).le.trans (by decide)

/-- The sort costs a linear number of rows times a polynomial in word width and
the ceiling of the binary logarithm of the number of rows, including an empty input. -/
theorem sortedFrame_size (n w : ℕ) : (sortedFrame n w).size ≤
    n*(2+4*w)*(30*w+6) + 2*(n+1)*(6*w+4)*(2) +
    (Nat.clog 2 n)^2*(2*(n+1)*(24*(6*w+4)+1)) := by
  have norms (q : Pin n w) : (normBit q).size ≤ 30*w+6 := by
    rcases q with ⟨i,b|c⟩
    · cases b
      · have h := eqWord_size (widthWord (w := w) i) (fun _ => .const false) (fun _ => le_rfl) (fun _ => le_rfl)
        simp only [normBit,enable,StatementCircuit.Expr.size]; omega
      · change 1 ≤ _; omega
    · change 1 ≤ _; omega
  have hn := Frame.step_size_le (Frame.initial (id : Pin n w → _)) normBit _ norms
  have hl := Frame.step_size_le (normalize n w) (fun q : Pins (level n) (totalBits w) => encode q.1 q.2) 2
    (fun q => encode_size q.1 q.2)
  have hs := phases_size (level n) le_rfl (loaded n w)
  have hbits : totalBits w = 6*w+4 := by simp [totalBits,bits,rankBits,Column]; omega
  have hpad : 2^level n ≤ 2*(n+1) := by
    cases n with
    | zero => decide
    | succ m => exact (TeamSorting.padding_lt_twice (Nat.succ_pos m)).le.trans (by omega)
  simp only [Pin,Column,Fintype.card_prod,Fintype.card_sum,Fintype.card_bool,Fintype.card_fin,Frame.initial_size,
    zero_add] at hn
  change (normalize n w).size ≤ _ at hn
  simp only [Pins,Fintype.card_prod,Fintype.card_fin,hbits] at hl
  change (loaded n w).size ≤ _ at hl
  simp only [sortedFrame,Frame.select_size]
  apply hs.trans
  apply Nat.add_le_add (hl.trans (Nat.add_le_add hn (by gcongr)))
  rw [hbits]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpad)

private def rowAt (x : Pin n w → Bool) (i : Fin (2^level n)) (c : Column w) : Bool :=
  if h : i.val < n then x (⟨i.val,h⟩,c) else false

private theorem encoded (x : Pin n w → Bool) (i : Fin (2^level n)) :
    let a := rowAt ((normalize n w).eval x) i
    (fun j => (loaded n w).eval x (i,j)) =
      ParseBatchLookup.prepend (keyBits (decide (n ≤ i.val)) (!a (.inl false))
        (fun j => a (.inr (0,j))) (fun j => a (.inr (1,j)))) (a ∘ (Fintype.equivFin (Column w)).symm) := by
  intro a
  let z := (normalize n w).eval x
  let ev (e : Expr (Pin n w)) := e.eval z
  have hr (c : Column w) : ev (raw i c) = a c := by
    by_cases h : i.val < n <;> simp [ev,raw,a,rowAt,z,h,StatementCircuit.Expr.eval]
  simp only [loaded,Frame.step_eval]
  change (ev ∘ encode i) = _
  unfold encode keyBits
  rw [prepend_map,Fin.comp_cons,Fin.comp_cons,prepend_map]
  have hd : ev (.not (raw i (.inl false))) = !a (.inl false) := congrArg Bool.not (hr _)
  simp only [Function.comp_def,hr,hd]
  rfl

private theorem head_le {m : ℕ} {a b : Bool} {s t : Fin m → Bool}
    (h : value (Fin.cons a s) ≤ value (Fin.cons b t)) : a.toNat ≤ b.toNat := by
  have ht := value_lt (fun i => t i)
  cases a <;> cases b <;> simp_all [value]
  omega

private theorem strip_head {m : ℕ} {a : Bool} {s t : Fin m → Bool}
    (h : value (Fin.cons a s) ≤ value (Fin.cons a t)) : value s ≤ value t := by
  simpa only [value,Fin.cons_zero,Fin.cons_succ,Nat.add_le_add_iff_left] using h

private theorem restrict_positions {N m : ℕ} (fit : m ≤ N) (π : Equiv.Perm (Fin N))
    (initial : ∀ i j : Fin N, i ≤ j → (π j).val < m → (π i).val < m) :
    ∀ i, (π i).val < m ↔ i.val < m := by
  intro i
  constructor
  · intro h
    let f (k : Fin (i.val+1)) : Fin m := ⟨(π ⟨k.val,by have := k.isLt; have := i.isLt; omega⟩).val,
      initial _ i (by change k.val ≤ i.val; omega) h⟩
    have inj : Function.Injective f := by
      intro a b eq
      have e : π (a.castLE (Nat.succ_le_of_lt i.isLt)) = π (b.castLE (Nat.succ_le_of_lt i.isLt)) :=
        Fin.ext (congrArg (@Fin.val m) eq)
      exact Fin.castLE_injective _ (π.injective e)
    have card := Fintype.card_le_of_injective f inj
    simp only [Fintype.card_fin] at card
    omega
  · intro hi
    by_contra h
    have small (k : Fin m) : (π.symm (k.castLE fit)).val < i.val := by
      by_contra! hh
      apply h
      exact initial i (π.symm (k.castLE fit)) hh (by simp)
    let f (k : Fin m) : Fin i.val := ⟨_,small k⟩
    have inj : Function.Injective f := by
      intro a b eq
      have e : π.symm (a.castLE fit) = π.symm (b.castLE fit) := Fin.ext (congrArg (@Fin.val i.val) eq)
      exact Fin.castLE_injective _ (π.symm.injective e)
    have card := Fintype.card_le_of_injective f inj
    simp only [Fintype.card_fin] at card
    omega


private theorem sorted_rows (x : Pin n w → Bool) :
    let z := (normalize n w).eval x
    let y := (sortedFrame n w).eval x
    ∃ π : Equiv.Perm (Fin n), (∀ i c, y (i,c) = z (π i,c)) ∧
      Monotone (fun i : Fin n => value (Fin.cons (!active y i) (ParseBatchLookup.prepend
        (fun j => y (i,.inr (0,j))) (fun j => y (i,.inr (1,j)))))) := by
  intro z y
  let f := loaded n w
  obtain ⟨ρ,rows⟩ := phases_order f x
  let a (i : Fin (2^level n)) := rowAt z (ρ i)
  let key (i : Fin (2^level n)) := keyBits (decide (n ≤ (ρ i).val)) (!(a i (.inl false)))
    (fun j => a i (.inr (0,j))) (fun j => a i (.inr (1,j)))
  have wordAt (i : Fin (2^level n)) :
      (fun j => (phases (level n) le_rfl f).eval x (i,j)) =
        ParseBatchLookup.prepend (key i) (a i ∘ (Fintype.equivFin (Column w)).symm) :=
    (funext (rows i)).trans (encoded x (ρ i))
  have keys : Monotone (fun i => value (key i)) := by
    intro i j hij
    have h := phases_monotone f x hij
    change value _ ≤ value _ at h
    rw [wordAt,wordAt] at h
    simpa only [ordinal_of_return] using (Nat.div_le_div_right (c := 2^bits w) h)
  have fit := Nat.le_pow_clog (by decide : 1 < 2) n
  have bounds := restrict_positions fit ρ (by
    intro i j hij hj
    have h := head_le (keys hij)
    by_contra! hi
    simp only [hi,decide_true,Bool.toNat_true,not_le_of_gt hj,decide_false,Bool.toNat_false] at h
    omega)
  let π : Equiv.Perm (Fin n) :=
    { toFun := fun i => ⟨(ρ (index i)).val,(bounds _).2 i.isLt⟩
      invFun := fun i => ⟨(ρ.symm (index i)).val,(bounds _).1 (by rw [ρ.apply_symm_apply]; exact i.isLt)⟩
      left_inv := fun i => by apply Fin.ext; change (ρ.symm (ρ (index i))).val = i.val; simp [index]
      right_inv := fun i => by apply Fin.ext; change (ρ (ρ.symm (index i))).val = i.val; simp [index] }
  have real (i : Fin n) : (ρ (index i)).val < n := (bounds _).2 i.isLt
  have a_real (i : Fin n) (c) : a (index i) c = z (π i,c) := by simp only [a,rowAt,real,dite_true]; rfl
  have copy (i : Fin n) (c) : y (i,c) = z (π i,c) := by
    simp only [y,sortedFrame,Frame.select_eval]
    have h := congrFun (wordAt (index i)) (ParseBatchLookup.lowPin (rankBits w) (Fintype.equivFin _ c))
    simpa only [prepend_low,Function.comp_apply,Equiv.symm_apply_apply,a_real,f] using h
  refine ⟨π,copy,?_⟩
  intro i j hij
  have h := keys (show index i ≤ index j from hij)
  simp only [key,keyBits,not_le_of_gt (real _),decide_false,a_real] at h
  simp only [active,copy]
  exact strip_head h

private theorem prefix_count {α : Type*} (p : Fin n → Bool) (f : Fin n → α)
    (closed : ∀ i j, i ≤ j → p j = true → p i = true) (i : Fin n) :
    p i = true ↔ i.val < ((List.finRange n).filterMap (fun j => if p j then some (f j) else none)).length := by
  induction n with
  | zero => exact i.elim0
  | succ m ih =>
    by_cases h : p 0 = true
    · rw [List.finRange_succ,List.filterMap_cons]
      simp only [h,ite_true,List.filterMap_map,List.length_cons]
      refine Fin.cases (by simpa only [Fin.val_zero,h,true_iff] using Nat.succ_pos _) (fun k => ?_) i
      exact (ih (fun j => p j.succ) (fun j => f j.succ) (fun a b ab => closed _ _ (Fin.succ_le_succ_iff.mpr ab)) k).trans
        Nat.succ_lt_succ_iff.symm
    · have hn (j : Fin (m+1)) : p j ≠ true := fun hj => h (closed 0 j (Fin.zero_le j) hj)
      have hempty : (List.finRange (m+1)).filterMap (fun j => if p j then some (f j) else none) = [] :=
        List.filterMap_eq_nil_iff.mpr (fun j _ => by simp [hn j])
      rw [hempty]
      simp [hn i]

/-- The order used by the exterior interval scan. -/
def Parsed.before (a b : Parsed) : Prop :=
  a.site < b.site ∨ (a.site = b.site ∧ a.run.oldStart ≤ b.run.oldStart)

/-- Output guarantees of the physical sparse sort. The single permutation preserves every
payload bit even in disabled slots. Its enable bit also checks the original width. -/
structure Sorted (x y : Pin n w → Bool) : Prop where
  rows : ∃ π : Equiv.Perm (Fin n), ∀ i,
    (active y i = true ↔ active x (π i) = true ∧ 0 < (parse x (π i)).run.width) ∧
      (∀ c : Column w, c ≠ .inl false → y (i,c) = x (π i,c)) ∧ parse y i = parse x (π i)
  perm : (list y).Perm ((list x).filter (fun p => decide (0 < p.run.width)))
  compact : ∀ i : Fin n, active y i = true ↔ i.val < (list y).length
  ordered : (list y).Pairwise Parsed.before

/-- Actual Batcher sorting gives the positive enabled fragments in lexicographic order,
followed by the disabled tail, for every physical input and every word width. -/
theorem sortedFrame_values (x : Pin n w → Bool) : Sorted x ((sortedFrame n w).eval x) := by
  let z := (normalize n w).eval x
  let y := (sortedFrame n w).eval x
  change Sorted x y
  obtain ⟨π,copy,mono⟩ := sorted_rows x
  have act (i : Fin n) : active y i = true ↔ active x (π i) = true ∧ 0 < (parse x (π i)).run.width := by
    have he : active y i = active z (π i) := copy i _
    rw [he]
    exact (norm_values x (π i)).1
  have parsed (i : Fin n) : parse y i = parse x (π i) := by
    have he : parse y i = parse z (π i) := congrArg parseRow (funext (copy i))
    exact he.trans (norm_values x (π i)).2.2
  have closed (i j : Fin n) (hij : i ≤ j) (hj : active y j = true) : active y i = true := by
    have h := head_le (mono hij)
    change (!active y i).toNat ≤ (!active y j).toNat at h
    cases hi : active y i with
    | false => simp [hi,hj] at h
    | true => rfl
  refine ⟨⟨π,fun i => ⟨act i,fun c hc => (copy i c).trans ((norm_values x (π i)).2.1 c hc),parsed i⟩⟩,?_,
    prefix_count (active y) (parse y) closed,?_⟩
  · let source (i : Fin n) := (if active x i then some (parse x i) else none).filter (fun p => decide (0<p.run.width))
    have hv (i : Fin n) : (if active y i then some (parse y i) else none) = source (π i) := by
      by_cases ha : active x (π i) = true <;> by_cases hp : 0 < (parse x (π i)).run.width <;>
        simp [source,act,ha,hp,parsed,Option.filter]
    have perm := π.map_finRange_perm.filterMap source
    simpa only [list,List.filter_filterMap,hv,source,List.filterMap_map,Function.comp_def] using perm
  · apply List.pairwise_filterMap.mpr
    apply (List.pairwise_lt_finRange n).imp
    intro i j hij u hu v hv
    by_cases hi : active y i = true
    · by_cases hj : active y j = true
      · simp only [hi,hj,ite_true,Option.some.injEq] at hu hv
        subst u; subst v
        have h := mono hij.le
        change value (Fin.cons (!active y i) _) ≤ value (Fin.cons (!active y j) _) at h
        simp only [hi,hj,Bool.not_true] at h
        have ht := strip_head h
        have site := Nat.div_le_div_right (c := 2^w) ht
        simp only [ordinal_of_return] at site
        change (parse y i).site ≤ (parse y j).site at site
        rcases site.lt_or_eq with lt | eq
        · exact Or.inl lt
        · refine Or.inr ⟨eq,?_⟩
          simp only [ParseBatchLookup.value_prepend] at ht
          change (parse y i).site*2^w + (parse y i).run.oldStart ≤
            (parse y j).site*2^w + (parse y j).run.oldStart at ht
          rw [eq] at ht
          exact Nat.le_of_add_le_add_left ht
      · simp [hj] at hv
    · simp [hi] at hu

/-- A uniquely keyed, ordered roster of the same physical fragments is exactly the
list emitted by the sort, including the associated widths and optional source starts. -/
theorem Sorted.list_eq {x y : Pin n w → Bool} (h : Sorted x y) (roster : List Parsed)
    (same : ((list x).filter (fun p => decide (0 < p.run.width))).Perm roster)
    (ordered : roster.Pairwise Parsed.before)
    (unique : ∀ a ∈ roster, ∀ b ∈ roster, a.site = b.site → a.run.oldStart = b.run.oldStart → a = b) :
    list y = roster := by
  have perm := h.perm.trans same
  apply perm.eq_of_pairwise _ h.ordered ordered
  intro a b ha hb hab hba
  apply unique a (perm.subset ha) b hb <;> unfold Parsed.before at hab hba <;> omega

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
