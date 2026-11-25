import OAI.Hierarchy.DescentSparseBinOrder
import Mathlib.Data.List.Find

namespace OAI
/-! # Canonical representatives of repeated ports and the global zero-width bin -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM
open Sparse ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
variable {C : Type*} [Fintype C] [DecidableEq C] {n w : ℕ}

def tag (v : Option C) := (v.map code).getD (Fintype.card C)

omit [DecidableEq C] in
theorem tag_injective : Function.Injective (tag (C:=C)) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some x => exact ((code_lt x).ne' h).elim
  | some x =>
    cases b with
    | none => exact ((code_lt x).ne h).elim
    | some y => exact congrArg some (code_injective h)

/-- A fixed public upper bound can mark empty slots even when the set of
occupied destinations changes. -/
def wideTag (missing : ℕ) (v : Option C) := (v.map code).getD missing

omit [DecidableEq C] in
theorem wideTag_injective (missing : ℕ) (large : Fintype.card C≤ missing) :
    Function.Injective (wideTag (C:=C) missing) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some x => exact ((code_lt x).trans_le large).ne' h |>.elim
  | some x =>
    cases b with
    | none => exact ((code_lt x).trans_le large).ne h |>.elim
    | some y => exact congrArg some (code_injective h)

omit [DecidableEq C] in
theorem wideTag_order (missing : ℕ) (large : Fintype.card C≤ missing) (a b : Option C) :
    wideTag missing a<wideTag missing b ↔ tag a<tag b := by
  cases a with
  | none =>
    cases b with
    | none => simp
    | some c => exact iff_of_false (not_lt_of_ge ((code_lt c).trans_le large).le) (not_lt_of_ge (code_lt c).le)
  | some c =>
    cases b with
    | none => exact iff_of_true ((code_lt c).trans_le large) (code_lt c)
    | some v => rfl

theorem upper_order (raw : Fin n→Option C) (missing : ℕ) (large : Fintype.card C≤ missing) :
    order (fun i=>wideTag missing (raw i))=order (fun i=>tag (raw i)) := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [order_val,order_val]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,before,wideTag_order missing large,
    (wideTag_injective missing large).eq_iff,tag_injective.eq_iff]

def rowKey (raw : Fin n→Option C) (i : ℕ) := if h : i<n then tag (raw ⟨i,h⟩) else Fintype.card C

def first (raw : Fin n→Option C) (t : ℕ) :=
  (List.range n).find? fun j=>decide (rowKey raw j=t)

def uniqueTarget (raw : Fin n→Option C) (i : Fin n) :=
  if first raw (tag (raw i))=some i.val then raw i else none

omit [DecidableEq C] in
theorem representative (raw : Fin n→Option C) (c : C) (h : ∃i,raw i=some c) :
    ∃i,uniqueTarget raw i=some c := by
  obtain ⟨u,hu⟩ := h
  cases f : first raw (code c) with
  | none =>
    have bad := List.find?_eq_none.mp f u.val (List.mem_range.mpr u.isLt)
    exact False.elim (bad (by simp [rowKey,u.isLt,hu,tag]))
  | some j =>
    have bound : j<n := List.mem_range.mp (List.mem_of_find?_eq_some f)
    let a : Fin n := ⟨j,bound⟩
    have matched : decide (rowKey raw j = code c) = true :=
      List.find?_some (p := fun i => decide (rowKey raw i = code c)) f
    have q : tag (raw a)=code c := by
      simpa [rowKey,bound,a] using of_decide_eq_true matched
    have hit : raw a=some c := tag_injective (show tag (raw a)=tag (some c) from q)
    exact ⟨a,by simp [uniqueTarget,hit,tag,f,a]⟩

def aperture (S : Finset C) (raw : Fin n→Option C) (seen : ∀v,(∃i,raw i=some v)↔v∈keep S) :
    Aperture S n where
  target := uniqueTarget raw
  unique := by
    intro i j c a b
    unfold uniqueTarget at a b
    split at a <;> try contradiction
    rename_i fi
    split at b <;> try contradiction
    rename_i fj
    rw [a] at fi
    rw [b] at fj
    exact Fin.ext (Option.some.inj (fi.symm.trans fj))
  covers := by
    intro c
    rw [←seen]
    refine ⟨?_,representative raw c⟩
    rintro ⟨i,hi⟩
    unfold uniqueTarget at hi
    split at hi <;> try contradiction
    exact ⟨i,hi⟩

def clean (n missing : ℕ) (keys : Bank) : Expr :=
  let current := Expr.lookup keys .row
  .branch .eq .row (localTarget n keys (.lit 0) current) current (.lit missing)

theorem clean_eval_missing (raw : Fin n→Option C) (keys : Bank) (m : Memory w) (i : Fin n)
    (nFit : n≤keys.size) (bankWord : keys.size<2^w) (missing : ℕ) (large : Fintype.card C≤ missing) (count : missing<2^w)
    (input : ∀i,(m (keys.base+i.val)).val=wideTag missing (raw i)) :
    (clean n missing keys).eval m (i.val:Word w)=(wideTag missing (uniqueTarget raw i):Word w) := by
  have ri : keys.read m (i.val:Word w)=m (keys.base+i.val) := by
    have sm := i.isLt.trans_le nFit
    simp [Bank.read,Fin.val_cast_of_lt (sm.trans bankWord),Nat.mod_eq_of_lt sm]
  have tap : (Expr.lookup keys .row).eval m (i.val:Word w)=m (keys.base+i.val) := ri
  have rank := localTarget_eval n keys (.lit 0) (.lookup keys .row) m (i.val:Word w) 0 (wideTag missing (raw i))
    (fun j=>if hj : j<n then wideTag missing (raw ⟨j,hj⟩) else missing) rfl ((congrArg Fin.val tap).trans (input i)) (by omega) bankWord
    (fun j hj=>by simpa [rowKey,hj] using input ⟨j,hj⟩)
  have findEq : (List.range n).find? (fun j=>decide ((if hj : j<n then wideTag missing (raw ⟨j,hj⟩) else missing)=wideTag missing (raw i)))=
      first raw (tag (raw i)) := by
    apply List.find?_congr
    intro j hj
    have hj' := List.mem_range.mp hj
    simp [rowKey,hj',(wideTag_injective missing large).eq_iff,tag_injective.eq_iff]
  rw [findEq] at rank
  have current : m (keys.base+i.val)=(wideTag missing (raw i):Word w) := by
    apply Fin.ext
    rw [Fin.val_cast_of_lt]
    · exact input i
    · cases e : raw i with
      | none => exact count
      | some c => exact (code_lt c).trans (large.trans_lt count)
  unfold clean
  simp only [Expr.eval,Comparison.test,beq_iff_eq,ri,rank,current]
  cases f : first raw (tag (raw i)) with
  | none =>
    have different : (i.val:Word w)≠(n:Word w) := by
      intro h
      have e := congrArg Fin.val h
      simp [Fin.val_cast_of_lt (nFit.trans_lt bankWord),Fin.val_cast_of_lt (i.isLt.trans (nFit.trans_lt bankWord))] at e
      exact i.isLt.ne e
    simp [f,uniqueTarget,different,wideTag]
  | some j =>
    have hj : j<n := List.mem_range.mp (List.mem_of_find?_eq_some f)
    have test : (i.val:Word w)=(j:Word w) ↔ j=i.val := by
      rw [Fin.ext_iff,Fin.val_cast_of_lt (i.isLt.trans (nFit.trans_lt bankWord)),Fin.val_cast_of_lt (hj.trans (nFit.trans_lt bankWord))]
      exact eq_comm
    by_cases yes : j=i.val <;> simp [f,uniqueTarget,test,yes,wideTag]

theorem clean_eval (raw : Fin n→Option C) (keys : Bank) (m : Memory w) (i : Fin n)
    (nFit : n≤keys.size) (bankWord : keys.size<2^w) (count : Fintype.card C<2^w)
    (input : ∀i,(m (keys.base+i.val)).val=tag (raw i)) :
    (clean n (Fintype.card C) keys).eval m (i.val:Word w)=(tag (uniqueTarget raw i):Word w) :=
  clean_eval_missing raw keys m i nFit bankWord (Fintype.card C) le_rfl count input

theorem clean_fits (n missing cut : ℕ) (keys : Bank) (f : keys.Fits w cut) :
    (clean n missing keys).Fits w cut := ⟨trivial,localTarget_fits _ _ _ _ f trivial ⟨f,trivial⟩,⟨f,trivial⟩,trivial⟩

theorem clean_work (n missing : ℕ) (keys : Bank) : (clean n missing keys).work=12+17*n := by
  simp [clean,Expr.work,localTarget_work];omega

end Hierarchy.DescentPacking.SparseBinRAM

end
end OAI
