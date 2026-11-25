import OAI.Hierarchy.ProtocolRAMScan
import OAI.Hierarchy.DescentIndexedRowChoice

namespace OAI
/-! # Writing the canonical next mixing row from the physical score and span columns -/

namespace Hierarchy.DescentGL.RowRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing Classical BigOperators

noncomputable section
variable {n w : ℕ}

def cell (bank : Bank) (i : Fin n) : Expr := .lookup bank (.lit i.val)

def excluded (bank : Bank) (m : Memory w) (i : Fin n) := bank.read m (i.val:Word w) ≠ 0

def score (bank : Bank) (m : Memory w) (i : Fin n) := (bank.read m (i.val:Word w)).val

/-- Physical order of the two keys. Earlier row indices win equal scores. -/
def beats (masked scored : Bank) (m : Memory w) (j i : Fin n) : Prop :=
  ¬ excluded masked m j ∧ (score scored m j < score scored m i ∨
    score scored m j = score scored m i ∧ j < i)

def better (masked scored : Bank) (j i : Fin n) : Expr :=
  let sj := cell scored j
  let si := cell scored i
  let tie := if j < i then Expr.branch .eq sj si (.lit 1) (.lit 0) else .lit 0
  .branch .eq (cell masked j) (.lit 0) (.branch .lt sj si (.lit 1) tie) (.lit 0)

private theorem better_eval (masked scored : Bank) (m : Memory w) (r : Word w) (j i : Fin n) :
    (better masked scored j i).eval m r = if beats masked scored m j i then 1 else 0 := by
  classical
  simp only [better,Expr.eval,cell,Comparison.test,beq_iff_eq,beats,score,excluded,
    Nat.cast_zero,Nat.cast_one,not_ne_iff]
  by_cases legal : masked.read m (j.val:Word w)=0
  · by_cases less : scored.read m (j.val:Word w) < scored.read m (i.val:Word w)
    · simp [legal,less,Fin.lt_def.mp less]
    · by_cases equal : scored.read m (j.val:Word w) = scored.read m (i.val:Word w)
      · by_cases first : j < i <;> simp [legal,equal,first,Expr.eval,Comparison.test]
      · have neVal := fun h=>equal (Fin.ext h)
        have notLess : ¬(scored.read m (j.val:Word w)).val < (scored.read m (i.val:Word w)).val := less
        by_cases first : j < i <;> simp [legal,less,notLess,equal,first,Expr.eval,Comparison.test];
          exact fun bad=>False.elim (neVal bad)
  · simp [legal]

def check (masked scored : Bank) (i : Fin n) : List (Fin n) → Expr
  | [] => .lit i.val
  | j::js => .branch .eq (better masked scored j i) (.lit 0) (check masked scored i js) (.lit 0)

private theorem check_eval (masked scored : Bank) (m : Memory w) (r : Word w)
    (wide : 1<2^w) (i : Fin n) (js : List (Fin n)) :
    (check masked scored i js).eval m r =
      if ∀j∈js, ¬beats masked scored m j i then (i.val:Word w) else 0 := by
  classical
  have one : (1:Word w)≠0 := by
    intro h
    have value := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt wide] at value
  induction js with
  | nil => simp [check,Expr.eval]
  | cons j js ih =>
    simp only [check,Expr.eval,better_eval,Comparison.test,beq_iff_eq,Nat.cast_zero,List.mem_cons,
      forall_eq_or_imp,ih]
    by_cases loses : beats masked scored m j i <;> simp [loses,one]

def contribution (masked scored : Bank) (i : Fin n) :=
  Expr.branch .eq (cell masked i) (.lit 0) (check masked scored i (List.finRange n)) (.lit 0)

def total (masked scored : Bank) : List (Fin n) → Expr
  | [] => .lit 0
  | i::is => .op .add (contribution masked scored i) (total masked scored is)

def term (masked scored : Bank) (n : ℕ) := total masked scored (List.finRange n)

private theorem total_eval (masked scored : Bank) (m : Memory w) (r : Word w) (xs : List (Fin n)) :
    (total masked scored xs).eval m r =
      (xs.map fun i=>(contribution masked scored i).eval m r).sum := by
  induction xs with
  | nil => simp [total,Expr.eval]
  | cons i is ih => simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,ih]

theorem term_eval (masked scored : Bank) (m : Memory w) (r : Word w) (wide : 1<2^w) (a : Fin n)
    (legal : ¬excluded masked m a) (best : ∀j, ¬beats masked scored m j a)
    (unique : ∀ i, ¬excluded masked m i → (∀ j, ¬beats masked scored m j i) → i=a) :
    (term masked scored n).eval m r = (a.val:Word w) := by
  have part (i : Fin n) :
      (contribution masked scored i).eval m r = if i=a then (a.val:Word w) else 0 := by
    simp only [contribution,Expr.eval,cell,Comparison.test,beq_iff_eq,Nat.cast_zero,
      check_eval masked scored m r wide,List.mem_finRange,forall_const]
    by_cases hit : i=a
    · subst i
      have ok : masked.read m (a.val:Word w)=0 := not_ne_iff.mp legal
      simp [ok,best]
    · by_cases ok : masked.read m (i.val:Word w)=0
      · have lost : ¬ ∀j, ¬beats masked scored m j i := fun none=>hit (unique i (not_ne_iff.mpr ok) none)
        simp [ok,lost,hit]
      · simp [ok,hit]
  rw [term,total_eval]
  simp_rw [part]
  simp [List.finRange,List.map_ofFn,Function.comp_def,List.sum_ofFn]

private theorem better_fits (masked scored : Bank) {out : ℕ} (mb : masked.Fits w out)
    (sb : scored.Fits w out) (j i : Fin n) : (better masked scored j i).Fits w out := by
  by_cases first : j < i <;> simp [better,cell,Expr.Fits,mb,sb,first]

private theorem check_fits (masked scored : Bank) {out : ℕ} (mb : masked.Fits w out)
    (sb : scored.Fits w out) (i : Fin n) (js : List (Fin n)) : (check masked scored i js).Fits w out := by
  induction js with
  | nil => trivial
  | cons j js ih => exact ⟨better_fits masked scored mb sb j i,trivial,ih,trivial⟩

theorem total_fits (masked scored : Bank) {out : ℕ} (mb : masked.Fits w out)
    (sb : scored.Fits w out) (xs : List (Fin n)) : (total masked scored xs).Fits w out := by
  induction xs with
  | nil => trivial
  | cons i xs ih =>
    exact ⟨⟨⟨mb,trivial⟩,trivial,check_fits masked scored mb sb i _,trivial⟩,ih⟩

private theorem better_work (masked scored : Bank) (j i : Fin n) : (better masked scored j i).work ≤ 44 := by
  by_cases first : j < i <;> simp [better,Expr.work,cell,first]

private theorem check_work (masked scored : Bank) (i : Fin n) (js : List (Fin n)) :
    (check masked scored i js).work ≤ 1+47*js.length := by
  induction js with
  | nil => simp [check,Expr.work]
  | cons j js ih =>
    simp only [check,Expr.work,List.length_cons,Nat.mul_add,mul_one]
    have h := better_work masked scored j i
    omega

theorem total_work (masked scored : Bank) (xs : List (Fin n)) :
    (total masked scored xs).work ≤ 1+(12+47*n)*xs.length := by
  induction xs with
  | nil => simp [total,Expr.work]
  | cons i xs ih =>
    have h := check_work masked scored i (List.finRange n)
    rw [List.length_finRange] at h
    simp only [total,Expr.work,contribution,cell,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def procedure (w out n : ℕ) (masked scored : Bank) := scan w out 1 (term masked scored n)

theorem execute (out n : ℕ) (masked scored : Bank) (m : Memory w)
    (mb : masked.Fits w out) (sb : scored.Fits w out) (room : out+1<2^w) :
    (procedure w out n masked scored).Exec m (ProtocolRAM.image out 1 (term masked scored n) m)
      (4+1*(2*(term masked scored n).work+4)) :=
  scan_exec out 1 _ m (total_fits masked scored mb sb _) room

theorem clock_bound (masked scored : Bank) (k : ℕ) :
    4+1*(2*(term masked scored (2^k)).work+4) ≤ 10+24*2^k+94*(2^k)^2 := by
  have h := total_work masked scored (List.finRange (2^k))
  rw [List.length_finRange] at h
  unfold term
  nlinarith

theorem unchanged (masked scored : Bank) (n out : ℕ) (m : Memory w) (x : ℕ) (miss : x≠out) :
    ProtocolRAM.image out 1 (term masked scored n) m x=m x := by
  have dis : ¬(out≤x ∧ x<out+1) := by omega
  simp only [ProtocolRAM.image,fillSegment,ite_eq_right dis]

theorem physical_chosen {h k : ℕ} (hk : h<k) (base : Layout k) (objective : Row k → ℝ)
    (masked scored : Bank) (m : Memory w) (out : ℕ) (wide : 1<2^w)
    (legal : ∀ i : Fin (2^k), ¬excluded masked m i ↔ i∈legalMenu hk base)
    (compares : ∀ i j : Fin (2^k), score scored m i ≤ score scored m j ↔
      objective ((rowIndex k).symm i) ≤ objective ((rowIndex k).symm j)) :
    (ProtocolRAM.image out 1 (term masked scored (2^k)) m) out =
      ((chosenIndex hk base objective).val:Word w) := by
  let a := chosenIndex hk base objective
  have spec := DescentRowScore.nextRow_spec (legalMenu hk base) (legalMenu_nonempty hk base)
    (fun i=>objective ((rowIndex k).symm i))
  change a∈legalMenu hk base ∧ _ at spec
  have ok := (legal a).mpr spec.1
  have low (j : Fin (2^k)) (eligible : ¬excluded masked m j) :
      score scored m a ≤ score scored m j :=
    (compares a j).mpr (spec.2.1 j ((legal j).mp eligible))
  have tied (j : Fin (2^k)) (eligible : ¬excluded masked m j)
      (same : score scored m j=score scored m a) : a≤j :=
    spec.2.2 j ((legal j).mp eligible) (le_antisymm ((compares j a).mp same.le) ((compares a j).mp same.ge))
  have best (j : Fin (2^k)) : ¬beats masked scored m j a := by
    rintro ⟨eligible,less|⟨same,earlier⟩⟩
    · exact (not_lt_of_ge (low j eligible)) less
    · exact (not_lt_of_ge (tied j eligible same)) earlier
  have unique (i : Fin (2^k)) (eligible : ¬excluded masked m i)
      (none : ∀ j,¬beats masked scored m j i) : i=a := by
    have lo := low i eligible
    have rev : score scored m i ≤ score scored m a := le_of_not_gt (fun lt=>none a ⟨ok,.inl lt⟩)
    have same := le_antisymm rev lo
    exact le_antisymm (le_of_not_gt (fun lt=>none a ⟨ok,.inr ⟨same.symm,lt⟩⟩)) (tied i eligible same)
  simpa only [ProtocolRAM.image,fillSegment,le_refl,Nat.lt_add_one,true_and,ite_true] using
    term_eval masked scored m ((out:Word w)-(out:Word w)) wide a ok best unique

end
end Hierarchy.DescentGL.RowRAM

end OAI
