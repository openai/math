import OAI.Computability.VPVNP.CompressorChoicePreparation

/-!
# Native lookup of the rounded demand-grid point

For a fixed rational grid, the public data list the address offsets and the
two cleared coefficients of every comparison. The instruction table reads the
demand widths, tests each row in order and returns the first covering index.
The table length is the sentinel for a failed search.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GridRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM MotifAdmission
open scoped Fin.CommRing

variable {D : Type*} {d t w : ℕ}

private def slot (j : Fin t) (i : Fin d) (f : Fin 3) : Fin (t*d*3) :=
  finProdFinEquiv (finProdFinEquiv (j,i), f)

/-- Fixed public words, ordered by grid row, demand coordinate and field. -/
def coefficients [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ)
    (x : Fin (t*d*3)) : Word w :=
  let (a, f) := finProdFinEquiv.symm x
  let (j, i) := finProdFinEquiv.symm a
  let r := rows j (order i)
  if f = 0 then i.val else if f = 1 then (r.den^2 * denominator p : ℕ) else (r.num.natAbs^2 : ℕ)

private theorem coefficient_slot [Fintype D] (order : Fin d ≃ D) (p : D → ℚ)
    (rows : Fin t → D → ℚ) (j : Fin t) (i : Fin d) (f : Fin 3) :
    coefficients (w := w) order p rows (slot j i f) =
      if f = 0 then i.val else if f = 1 then ((rows j (order i)).den^2 * denominator p : ℕ)
      else ((rows j (order i)).num.natAbs^2 : ℕ) := by
  simp [coefficients,slot]

/-- Word-fit conditions on the final products, allowing modular intermediate
products because the register arithmetic is a ring. -/
def OperandsFit [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ)
    (b : D → ℕ) (w : ℕ) : Prop :=
  ∀ j i, b (order i)^2 * ((rows j (order i)).den^2 * denominator p) < 2^w ∧
    energy p b * (rows j (order i)).num.natAbs^2 < 2^w

/-- This grid-dependent coefficient bounds all comparison operands after
multiplication by the squared input-width scale. -/
def operandConstant [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ) : ℕ :=
  ∑ j, ∑ i, ((rows j (order i)).den^2 * denominator p +
    (∑ e, weight p e) * (rows j (order i)).num.natAbs^2)

theorem operandsFit_of_width [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ)
    (b : D → ℕ) (M : ℕ) (hb : ∀ e, b e ≤ M)
    (hfit : operandConstant order p rows * (M+1)^2 < 2^w) : OperandsFit order p rows b w := by
  intro j i
  let c := fun j i => (rows j (order i)).den^2 * denominator p +
    (∑ e, weight p e) * (rows j (order i)).num.natAbs^2
  have h : c j i ≤ operandConstant order p rows :=
    (Finset.single_le_sum (f := c j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun j => ∑ i, c j i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  obtain ⟨hl,hr⟩ := grid_operands_le p b M hb (order i) (rows j (order i))
  rw [mul_pow, mul_assoc] at hl
  exact ⟨hl.trans_lt ((Nat.mul_le_mul_right _ ((Nat.le_add_right ..).trans h)).trans_lt hfit),
    hr.trans_lt ((Nat.mul_le_mul_right _ ((Nat.le_add_left ..).trans h)).trans_lt hfit)⟩

private def keep : Flow 8 (t*d*3) := .line (.copy 5 5)
private def clear : Flow 8 (t*d*3) := .line (.constant 5 0)

/-- One coordinate comparison. The sign of a fixed rational is resolved at
table generation. A negative coordinate clears the row's validity bit. -/
def compareCoordinate (order : Fin d ≃ D) (rows : Fin t → D → ℚ) (j : Fin t) (i : Fin d) :
    Flow 8 (t*d*3) :=
  .seq (.line (.stateWord 2)) <|
  .seq (.line (.publicWord 4 (slot j i 0))) <|
  .seq (.line (.binary .add 2 2 4)) <|
  .seq (.line (.read 3 2)) <|
  .seq (.line (.binary .mul 3 3 3)) <|
  .seq (.line (.publicWord 4 (slot j i 1))) <|
  .seq (.line (.binary .mul 3 3 4)) <|
  .seq (.line (.publicWord 4 (slot j i 2))) <|
  .seq (.line (.binary .mul 7 0 4))
    (.ifLt 7 3 clear (if 0 ≤ rows j (order i) then keep else clear))

private def compareEvents (a x : Word w) : List (Event w) :=
  [.tick,.tick,.tick,.read a x,.tick,.tick,.tick,.tick,.tick,.tick,.tick]

private theorem compare_exec [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ)
    (s : Word w) (mem : Memory w) (rs : Regs w 8) (j : Fin t) (i : Fin d)
    (he : (rs 0).val = energy p (DemandPreparation.demandAt order s mem))
    (fit : OperandsFit order p rows (DemandPreparation.demandAt order s mem) w) :
    let a := s + (i.val : Word w)
    ∃ out, Flow.Exec (coefficients order p rows) s (compareCoordinate order rows j i) rs mem
      (compareEvents a (mem a.val)) out mem ∧
      out 0 = rs 0 ∧ out 1 = rs 1 ∧ out 6 = rs 6 ∧
      out 5 = (if coversCoordinate p (DemandPreparation.demandAt order s mem) (order i)
        (rows j (order i)) then rs 5 else 0) := by
  dsimp only
  let pub := coefficients (w := w) order p rows
  let r := rows j (order i)
  let b := DemandPreparation.demandAt order s mem
  let a := s + (i.val : Word w)
  let x := mem a.val
  have hx : b (order i) = x.val := by simp [b,x,a,DemandPreparation.demandAt]
  let u := Function.update rs 2 s
  let v := Function.update u 4 (pub (slot j i 0))
  let z := Function.update v 2 (v 2 + v 4)
  have hz : z 2 = a := by simp (config := {decide := true}) [z,v,u,a,pub,coefficient_slot,Function.update]
  let g := Function.update z 3 x
  let h := Function.update g 3 (g 3 * g 3)
  let l := Function.update h 4 (pub (slot j i 1))
  let m := Function.update l 3 (l 3 * l 4)
  let n := Function.update m 4 (pub (slot j i 2))
  let y := Function.update n 7 (n 0 * n 4)
  have lhs : (y 3).val = b (order i)^2 * (r.den^2 * denominator p) := by
    have hw : y 3 = ((b (order i)^2 * (r.den^2 * denominator p) : ℕ) : Word w) := by
      simp (config := {decide := true}) [y,n,m,l,h,g,pub,coefficient_slot,Function.update,hx,r,pow_two]
    rw [hw,Fin.val_natCast,Nat.mod_eq_of_lt (fit j i).1]
  have rhs : (y 7).val = energy p b * r.num.natAbs^2 := by
    have hw : y 7 = ((energy p b * r.num.natAbs^2 : ℕ) : Word w) := by
      simp (config := {decide := true}) [y,n,m,l,h,g,z,v,u,pub,coefficient_slot,
        Function.update,← he,r,b]
    rw [hw,Fin.val_natCast,Nat.mod_eq_of_lt (fit j i).2]
  have start (last : Regs w 8) (branch : Flow.Exec pub s
      (.ifLt 7 3 clear (if 0 ≤ rows j (order i) then keep else clear)) y mem [.tick,.tick] last mem) :
      Flow.Exec pub s (compareCoordinate order rows j i) rs mem (compareEvents a x) last mem := by
    have rd : Flow.Exec pub s (.line (.read 3 2)) z mem [.read a x] g mem := by
      apply Flow.Exec.line
      simp only [Op.effect,hz,g,x]
    exact .seq (.line (rs' := u) rfl) (.seq (.line (rs' := v) rfl) (.seq (.line (rs' := z) rfl)
      (.seq rd (.seq (.line (rs' := h) rfl) (.seq (.line (rs' := l) rfl)
      (.seq (.line (rs' := m) rfl) (.seq (.line (rs' := n) rfl)
      (.seq (.line (rs' := y) rfl) branch))))))))
  have cov : coversCoordinate p b (order i) r = true ↔ 0 ≤ r ∧ ¬ y 7 < y 3 := by
    simp [coversCoordinate,Fin.lt_def,lhs,rhs,mul_pow,mul_assoc,not_lt]
  have common (dst : Fin 8) (h2 : dst ≠ 2) (h3 : dst ≠ 3) (h4 : dst ≠ 4) (h7 : dst ≠ 7) :
      y dst = rs dst := by simp [y,n,m,l,h,g,z,v,u,Function.update,h2,h3,h4,h7]
  change ∃ out, Flow.Exec pub s _ rs mem (compareEvents a x) out mem ∧
    out 0 = rs 0 ∧ out 1 = rs 1 ∧ out 6 = rs 6 ∧
    out 5 = (if coversCoordinate p b (order i) r then rs 5 else 0)
  by_cases lt : y 7 < y 3
  · refine ⟨_,start _ (.ifLtYes lt (.line (rs' := Function.update y 5 0) rfl)),?_⟩
    simp (config := {decide := true}) [Function.update,common,cov,lt]
  · by_cases sign : 0 ≤ r
    · have hb : (if 0 ≤ rows j (order i) then keep else clear) = (keep : Flow 8 (t*d*3)) := ite_eq_left sign
      refine ⟨_,start _ (.ifLtNo lt (by rw [hb]; exact .line (rs' := Function.update y 5 (y 5)) rfl)),?_⟩
      simp (config := {decide := true}) [Function.update,common,cov,lt,sign]
    · have hb : (if 0 ≤ rows j (order i) then keep else clear) = (clear : Flow 8 (t*d*3)) := ite_eq_right sign
      refine ⟨_,start _ (.ifLtNo lt (by rw [hb]; exact .line (rs' := Function.update y 5 0) rfl)),?_⟩
      simp (config := {decide := true}) [Function.update,common,cov,lt,sign]

private def coordinates (order : Fin d ≃ D) (rows : Fin t → D → ℚ) (j : Fin t) :
    List (Fin d) → Flow 8 (t*d*3)
  | [] => keep
  | i :: is => .seq (compareCoordinate order rows j i) (coordinates order rows j is)

private theorem coordinates_exec [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ)
    (s : Word w) (mem : Memory w) (rs : Regs w 8) (j : Fin t) (ids : List (Fin d))
    (he : (rs 0).val = energy p (DemandPreparation.demandAt order s mem))
    (fit : OperandsFit order p rows (DemandPreparation.demandAt order s mem) w) :
    ∃ es out, Flow.Exec (coefficients order p rows) s (coordinates order rows j ids) rs mem es out mem ∧
      choiceBits es = [] ∧ countProbes es = ids.length ∧ after mem es = mem ∧
      es.length = 11*ids.length + 1 ∧ out 0 = rs 0 ∧ out 1 = rs 1 ∧ out 6 = rs 6 ∧
      out 5 = (if ids.all fun i => coversCoordinate p (DemandPreparation.demandAt order s mem)
        (order i) (rows j (order i)) then rs 5 else 0) := by
  induction ids generalizing rs with
  | nil =>
    refine ⟨_,_,.line (rs' := Function.update rs 5 (rs 5)) rfl,rfl,rfl,rfl,rfl,?_⟩
    simp (config := {decide := true}) [Function.update]
  | cons i ids ih =>
    obtain ⟨mid,h1,e1,r1,o1,v1⟩ := compare_exec order p rows s mem rs j i he fit
    obtain ⟨es,out,h2,bits,probes,mem',len,e2,r2,o2,v2⟩ := ih mid (e1 ▸ he)
    refine ⟨_ ++ es,out,.seq h1 h2,?_,?_,?_,?_,e2.trans e1,r2.trans r1,o2.trans o1,?_⟩
    · simpa [compareEvents,choiceBits] using bits
    · simp [compareEvents,countProbes,probes,Nat.add_comm]
    · exact mem'
    · simp [compareEvents,len]; omega
    · rw [v2,v1,List.all_cons]
      cases coversCoordinate p (DemandPreparation.demandAt order s mem) (order i) (rows j (order i)) <;>
        cases ids.all (fun x => coversCoordinate p (DemandPreparation.demandAt order s mem)
          (order x) (rows j (order x))) <;> rfl

private def rowsFrom (order : Fin d ≃ D) (rows : Fin t → D → ℚ) : List (Fin t) → Flow 8 (t*d*3)
  | [] => .line (.copy 1 1)
  | j :: js =>
    .seq (.line (.constant 5 1)) <|
    .seq (coordinates order rows j (List.finRange d)) <|
    .ifEq 5 6 (.line (.copy 1 1))
      (.seq (.line (.binary .add 1 1 6)) (rowsFrom order rows js))

/-- Ordered first-cover search starting with the energy in register zero.
The first covering index, or the length sentinel, is returned in register one. -/
def grid (order : Fin d ≃ D) (rows : Fin t → D → ℚ) : Flow 8 (t*d*3) :=
  .seq (.line (.constant 6 1)) (.seq (.line (.constant 1 0)) (rowsFrom order rows (List.finRange t)))

private theorem coordinates_length (order : Fin d ≃ D) (rows : Fin t → D → ℚ)
    (j : Fin t) (is : List (Fin d)) :
    (coordinates order rows j is).length = 12 * is.length + 1 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    by_cases h : 0 ≤ rows j (order i) <;>
      simp [coordinates,compareCoordinate,Flow.length,h,keep,clear,ih] <;> omega

/-- The text size depends only on the dimensions of the fixed grid. -/
theorem grid_length (order : Fin d ≃ D) (rows : Fin t → D → ℚ) :
    (grid order rows).length = (12*d+5)*t+3 := by
  have h (ids : List (Fin t)) : (rowsFrom order rows ids).length = (12*d+5)*ids.length+1 := by
    induction ids with
    | nil => rfl
    | cons j js ih => simp [rowsFrom,Flow.length,coordinates_length,ih,Nat.mul_succ]; omega
  simp [grid,Flow.length,h]; omega

private theorem probes_append (es fs : List (Event w)) :
    countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes,ih,Nat.add_assoc]

private def coversRow [Fintype D] (p : D → ℚ) (b : D → ℕ) (r : D → ℚ) : Bool :=
  decide (∀ e, coversCoordinate p b e (r e) = true)

private theorem all_coversRow [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (b : D → ℕ)
    (r : D → ℚ) :
    (List.finRange d).all (fun i => coversCoordinate p b (order i) (r (order i))) = coversRow p b r := by
  apply Bool.eq_iff_iff.mpr
  simp [List.all_eq_true,coversRow, Equiv.forall_congr_left order]

private theorem rows_exec [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ)
    (s : Word w) (mem : Memory w) (rs : Regs w 8) (ids : List (Fin t))
    (he : (rs 0).val = energy p (DemandPreparation.demandAt order s mem))
    (ho : rs 6 = 1) (hw : 1 < 2^w)
    (fit : OperandsFit order p rows (DemandPreparation.demandAt order s mem) w) :
    ∃ es out, Flow.Exec (coefficients order p rows) s (rowsFrom order rows ids) rs mem es out mem ∧
      choiceBits es = [] ∧ countProbes es ≤ ids.length*d ∧ after mem es = mem ∧
      es.length ≤ (11*d+4)*ids.length+1 ∧ out 1 = rs 1 +
        ((ids.findIdx fun j => coversRow p (DemandPreparation.demandAt order s mem) (rows j) : ℕ) : Word w) := by
  induction ids generalizing rs with
  | nil =>
    refine ⟨_,_,.line (rs' := Function.update rs 1 (rs 1)) rfl,rfl,by simp [countProbes],rfl,by simp,?_⟩
    simp [Function.update]
  | cons j js ih =>
    let b := DemandPreparation.demandAt order s mem
    let start := Function.update rs 5 (1 : Word w)
    have reset : Flow.Exec (coefficients order p rows) s (.line (.constant 5 1)) rs mem [.tick] start mem := .line rfl
    have hs (i : Fin 8) (hi : i ≠ 5) : start i = rs i := Function.update_of_ne hi ..
    obtain ⟨es,mid,h1,bits,probes,mem',len,hE,hR,hO,hV⟩ :=
      coordinates_exec order p rows s mem start j (List.finRange d) (hs 0 (by decide) ▸ he) fit
    rw [List.length_finRange] at probes len
    rw [all_coversRow] at hV
    have ho' := hO.trans ((hs 6 (by decide)).trans ho)
    have hr' := hR.trans (hs 1 (by decide))
    change mid 5 = (if coversRow p b (rows j) then start 5 else 0) at hV
    by_cases hc : coversRow p b (rows j) = true
    · have test : mid 5 = mid 6 := by simp [hV,hc,start,ho']
      have hyes : Flow.Exec (coefficients order p rows) s (.line (.copy 1 1)) mid mem
          [.tick] (Function.update mid 1 (mid 1)) mem := .line rfl
      refine ⟨_,_,.seq reset (.seq h1 (.ifEqYes test hyes)),?_,?_,?_,?_,?_⟩
      · simp [choiceBits,Flow.choiceBits_append,bits]
      · simp [countProbes,probes_append,probes,Nat.succ_mul]
      · change after mem (es ++ [.tick,.tick]) = mem
        rw [show after mem (es ++ [.tick,.tick]) = after (after mem es) [.tick,.tick] from List.foldl_append,mem']
        rfl
      · simp [len,Nat.mul_succ]; omega
      · simp [List.findIdx_cons,hc,b,hr',Function.update] at *
    · have hn : (0 : Word w) ≠ 1 := by
        intro h
        have h' := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt hw] at h'
      have test : mid 5 ≠ mid 6 := by simp [hV,hc,ho',hn]
      let next := Function.update mid 1 (mid 1 + mid 6)
      have inc : Flow.Exec (coefficients order p rows) s (.line (.binary .add 1 1 6)) mid mem
          [.tick] next mem := .line rfl
      have en : (next 0).val = energy p b := by
        rw [show next 0 = mid 0 from Function.update_of_ne (by decide) ..,hE,hs 0 (by decide)]
        exact he
      have on : next 6 = 1 := (Function.update_of_ne (by decide) ..).trans ho'
      obtain ⟨fs,out,h2,fb,fp,fm,fl,fv⟩ := ih next en on
      refine ⟨_,_,.seq reset (.seq h1 (.ifEqNo test (.seq inc h2))),?_,?_,?_,?_,?_⟩
      · simp [choiceBits,Flow.choiceBits_append,bits,fb]
      · simp [countProbes,probes_append,probes,Nat.succ_mul]; omega
      · change after mem (es ++ (.tick :: .tick :: fs)) = mem
        rw [show after mem (es ++ (.tick :: .tick :: fs)) =
          after (after mem es) (.tick :: .tick :: fs) from List.foldl_append,mem']
        exact fm
      · simp [len,Nat.mul_succ]; omega
      · change out 1 = rs 1 + (((j :: js).findIdx fun a => coversRow p b (rows a) : ℕ) : Word w)
        rw [fv,List.findIdx_cons,ite_eq_right hc]
        simp [next,ho',hr',b,add_assoc,add_comm,add_left_comm]

/-- Row number returned by the grid instruction table. -/
def firstRow [Fintype D] (p : D → ℚ) (b : D → ℕ) (rows : Fin t → D → ℚ) : ℕ :=
  (List.ofFn rows).findIdx (coversRow p b)

theorem firstRow_getElem? [Fintype D] (p : D → ℚ) (b : D → ℕ) (rows : Fin t → D → ℚ) :
    (List.ofFn rows)[firstRow p b rows]? = selectGrid p b (List.ofFn rows) := by
  change (List.ofFn rows)[(List.ofFn rows).findIdx (coversRow p b)]? = (List.ofFn rows).find? (coversRow p b)
  generalize List.ofFn rows = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : coversRow p b a = true <;> simp [List.findIdx_cons,ha,ih]

/-- Exact row-selection semantics and worst-case work for an arbitrary finite
ordered table, including empty tables and grids with negative coordinates. -/
theorem grid_exec [Fintype D] (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ)
    (s : Word w) (mem : Memory w) (rs : Regs w 8)
    (he : (rs 0).val = energy p (DemandPreparation.demandAt order s mem))
    (hw : 1 < 2^w) (ht : t < 2^w)
    (fit : OperandsFit order p rows (DemandPreparation.demandAt order s mem) w) :
    ∃ es out, Flow.Exec (coefficients order p rows) s (grid order rows) rs mem es out mem ∧
      choiceBits es = [] ∧ countProbes es ≤ t*d ∧ after mem es = mem ∧
      es.length ≤ (11*d+4)*t+3 ∧ (out 1).val = firstRow p (DemandPreparation.demandAt order s mem) rows := by
  let a := Function.update rs 6 (1 : Word w)
  let c := Function.update a 1 (0 : Word w)
  have init1 : Flow.Exec (coefficients order p rows) s (.line (.constant 6 1)) rs mem [.tick] a mem := .line rfl
  have init2 : Flow.Exec (coefficients order p rows) s (.line (.constant 1 0)) a mem [.tick] c mem := .line rfl
  have hE : (c 0).val = energy p (DemandPreparation.demandAt order s mem) := by
    simpa (config := {decide := true}) [c,a,Function.update] using he
  have hO : c 6 = 1 := by simp (config := {decide := true}) [c,a,Function.update]
  obtain ⟨es,out,h,bits,probes,mem',len,hv⟩ := rows_exec order p rows s mem c (List.finRange t) hE hO hw fit
  rw [List.length_finRange] at len probes
  refine ⟨_,out,.seq init1 (.seq init2 h),bits,probes,mem',by simp; omega,?_⟩
  have hindex : (List.finRange t).findIdx (fun j => coversRow p (DemandPreparation.demandAt order s mem) (rows j)) =
      firstRow p (DemandPreparation.demandAt order s mem) rows := by
    have hm : (List.finRange t).map rows = List.ofFn rows := by simp [List.finRange,List.map_ofFn,Function.comp_def]
    rw [firstRow,← hm,List.findIdx_map]
    rfl
  have hi : firstRow p (DemandPreparation.demandAt order s mem) rows < 2^w :=
    (List.findIdx_le_length (xs := List.ofFn rows) (p := _)).trans_lt (by simpa using ht)
  rw [hv,hindex,show c 1 = 0 from Function.update_self ..,zero_add,Fin.val_natCast,Nat.mod_eq_of_lt hi]

end CompressorRecords.GridRAM

end VPVNP
end Computability
end OAI
