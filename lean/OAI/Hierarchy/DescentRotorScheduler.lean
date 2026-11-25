import OAI.Hierarchy.DescentRotorReset
import OAI.Hierarchy.DescentIrreducibleSearch

namespace OAI
/-! # An executable good-base rotor controller on finite packet IDs

Each arriving packet selects the first layer missing both of its terminals.
Transposing two entries in that layer's output alphabet extends its permutation
and preserves every previously routed packet. -/

namespace Hierarchy.DescentRotor.Scheduler
open DescentBinaryField
variable {m Y L : ℕ}
abbrev Layer (L : ℕ) := Fin (2*L+1)
structure State (m Y L : ℕ) where
  assignment : Vector (Layer L) m
  image : Vector (Vector (Fin Y) Y) (2*L+1)
  work : ℕ

def color (r : State m Y L) (e : Fin m) := r.assignment.get e
def rotate (r : State m Y L) (j : Layer L) (v : Fin Y) := (r.image.get j).get v

def start (m Y L : ℕ) : State m Y L :=
  ⟨Vector.replicate m 0,Vector.replicate _ (Vector.ofFn id),0⟩

variable (src dst : Fin m → Fin Y)

def free (r : State m Y L) (e : Fin m) (j : Layer L) :=
  allWithCost (fun f=>(decide (color r f≠j ∨ (src f≠src e ∧ dst f≠dst e)),3)) (List.finRange m)

def search (r : State m Y L) (e : Fin m) :=
  findWithCost (free src dst r e) (List.finRange (2*L+1))

def chosen (r : State m Y L) (e : Fin m) : Layer L := (search src dst r e).1.getD 0

private theorem free_iff (r : State m Y L) (e : Fin m) (j : Layer L) :
    (free src dst r e j).1=true ↔ ∀ f, color r f=j → src f≠src e ∧ dst f≠dst e := by
  simp only [free,allWithCost_read,List.all_eq_true,List.mem_finRange,forall_const,decide_eq_true_eq]
  constructor
  · exact fun h f eq => (h f).resolve_left (not_not_intro eq)
  · intro h f
    by_cases eq : color r f=j
    · exact Or.inr (h f eq)
    · exact Or.inl eq

private theorem chosen_fresh
    (row : ∀ v,(Finset.univ.filter fun e=>src e=v).card≤L)
    (col : ∀ v,(Finset.univ.filter fun e=>dst e=v).card≤L)
    (r : State m Y L) (e f : Fin m) (same : color r f=chosen src dst r e) :
    src f≠src e ∧ dst f≠dst e := by
  let U := (Finset.univ.filter fun f=>src f=src e) ∪ (Finset.univ.filter fun f=>dst f=dst e)
  have card : (U.image (color r)).card≤2*L := Finset.card_image_le.trans
    ((Finset.card_union_le ..).trans <| by have h:=row (src e); have t:=col (dst e); omega)
  obtain ⟨j,absent⟩ : ∃j : Layer L,j∉U.image (color r) := by
    by_contra! h
    rw [Finset.eq_univ_of_forall h,Finset.card_univ,Fintype.card_fin] at card
    omega
  have ok : (free src dst r e j).1=true := (free_iff ..).mpr <| by
    intro t eq
    have miss : t∉U := fun h=>absent (Finset.mem_image.mpr ⟨t,h,eq⟩)
    simpa [U,not_or] using miss
  have present : (search src dst r e).1.isSome := by
    unfold search
    rw [findWithCost_read]
    exact List.find?_isSome.mpr ⟨j,List.mem_finRange _,ok⟩
  cases found : (search src dst r e).1 with
  | none => simp [found] at present
  | some c =>
    have actual := findWithCost_read (free src dst r e) (List.finRange (2*L+1))
    change (search src dst r e).1=_ at actual
    have hit := List.find?_some (actual.symm.trans found)
    exact (free_iff ..).mp hit f (by simpa [chosen,found] using same)

def install (r : State m Y L) (e : Fin m) (j : Layer L) (work : ℕ) : State m Y L :=
  let old := r.image.get j
  let oldTarget := old.get (src e)
  let image := Vector.ofFn (fun v => Equiv.swap oldTarget (dst e) (old.get v))
  ⟨r.assignment.set e.val j e.isLt,r.image.set j.val image j.isLt,r.work+work+2*Y+3⟩

private theorem get_eq_cell {α : Type*} {n : ℕ} (xs : Vector α n) (i : Fin n) :
    xs.get i = xs[i.val] := rfl

private theorem color_install (r : State m Y L) (e f : Fin m) (j : Layer L) (work : ℕ) :
    color (install src dst r e j work) f=if f=e then j else color r f := by
  by_cases eq : f=e
  · subst f;simp [color,install,get_eq_cell]
  · have ne : e.val≠f.val := fun h=>eq (Fin.ext h.symm)
    simp [color,install,get_eq_cell,ne,eq]

private theorem rotate_install (r : State m Y L) (e : Fin m) (j k : Layer L) (work : ℕ) (v : Fin Y) :
    rotate (install src dst r e j work) k v =
      if k=j then Equiv.swap (rotate r j (src e)) (dst e) (rotate r j v) else rotate r k v := by
  by_cases eq : k=j
  · subst k;simp [rotate,install,get_eq_cell]
  · have ne : j.val≠k.val := fun h=>eq (Fin.ext h.symm)
    simp [rotate,install,get_eq_cell,ne,eq]

def step (r : State m Y L) (e : Fin m) : State m Y L :=
  let q := search src dst r e
  install src dst r e (q.1.getD 0) q.2

def run : List (Fin m) → State m Y L
  | [] => start _ _ _
  | e::xs => step src dst (run xs) e

def Safe (r : State m Y L) (xs : List (Fin m)) : Prop :=
  (∀j, Function.Bijective (rotate r j)) ∧
  (∀e∈xs,rotate r (color r e) (src e)=dst e) ∧
  ∀e∈xs,∀f∈xs,color r e=color r f → src e=src f → e=f

private theorem safe_step (r : State m Y L) (e : Fin m) (xs : List (Fin m)) (he : e∉xs)
    (old : Safe src dst r xs)
    (row : ∀ v,(Finset.univ.filter fun x=>src x=v).card≤L)
    (col : ∀ v,(Finset.univ.filter fun x=>dst x=v).card≤L) :
    Safe src dst (step src dst r e) (e::xs) := by
  let j := chosen src dst r e
  let debit := (search src dst r e).2
  change Safe src dst (install src dst r e j debit) (e::xs)
  have diff (f : Fin m) (h : color r f=j) := chosen_fresh src dst row col r e f h
  refine ⟨?_,?_,?_⟩
  · intro k
    by_cases eq : k=j
    · subst k
      simpa only [funext (rotate_install src dst r e j j debit),ite_eq_left rfl,ite_true,Function.comp_def] using
        (Equiv.swap (rotate r j (src e)) (dst e)).bijective.comp (old.1 j)
    · simpa only [funext (rotate_install src dst r e j k debit),ite_eq_right eq] using old.1 k
  · intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · simp [color_install,rotate_install]
    · have fe : f≠e := fun x=>he (x ▸ hf)
      rw [color_install,ite_eq_right fe,rotate_install]
      have route := old.2.1 f hf
      by_cases eq : color r f=j
      · rw [ite_eq_left eq]
        rw [eq] at route
        rw [Equiv.swap_apply_of_ne_of_ne
          (fun h=>(diff f eq).1 ((old.1 j).1 h)) (fun h=>(diff f eq).2 (route.symm.trans h)),route]
      · simpa [eq] using route
  · intro f hf g hg same source
    rw [color_install,color_install] at same
    rcases List.mem_cons.mp hf with rfl|hf
    · by_contra ne
      have colorEq : j=color r g := by simpa [Ne.symm ne] using same
      exact (diff g colorEq.symm).1 source.symm
    · have fe : f≠e := fun h=>he (h ▸ hf)
      rcases List.mem_cons.mp hg with rfl|hg
      · have matchEq : color r f=j := by simpa [fe] using same
        exact ((diff f matchEq).1 source).elim
      · have ge : g≠e := fun h=>he (h ▸ hg)
        exact old.2.2 f hf g hg (by simpa [fe,ge] using same) source

theorem safe_run (row : ∀ v,(Finset.univ.filter fun x=>src x=v).card≤L)
    (col : ∀ v,(Finset.univ.filter fun x=>dst x=v).card≤L) (xs : List (Fin m)) (unique : xs.Nodup) :
    Safe src dst (run (L:=L) src dst xs) xs := by
  induction xs with
  | nil =>
    refine ⟨fun j => ?_, by simp, by simp⟩
    have start_id : rotate (start m Y L) j = id := by
      funext v
      simp [start, rotate, get_eq_cell]
    change Function.Bijective (rotate (start m Y L) j)
    rw [start_id]
    exact Function.bijective_id
  | cons e xs ih =>
    exact safe_step src dst _ e xs unique.notMem (ih unique.of_cons) row col

def compile (L : ℕ) := run (L:=L) src dst (List.finRange m)

/-- The two native output arrays give a legal permutation for every layer, and
route every actual packet without a shared input slot in the same layer. -/
theorem compile_correct (row : ∀ v,(Finset.univ.filter fun x=>src x=v).card≤L)
    (col : ∀ v,(Finset.univ.filter fun x=>dst x=v).card≤L) :
    let r := compile src dst L
    (∀j, Function.Bijective (rotate r j)) ∧
    (∀e,rotate r (color r e) (src e)=dst e) ∧
    ∀e f,color r e=color r f → src e=src f → e=f := by
  simpa [compile,Safe] using safe_run src dst row col (List.finRange m) (List.nodup_finRange m)

theorem search_cost (r : State m Y L) (e : Fin m) : (search src dst r e).2≤(2*L+1)*(m*3) := by
  apply (findWithCost_bound _ _ (m*3) ?_).trans_eq (by simp)
  intro j _
  exact (allWithCost_bound _ _ 3 (fun _ _=>le_rfl)).trans_eq (by simp)

theorem run_cost (xs : List (Fin m)) :
    (run (L:=L) src dst xs).work ≤ xs.length*((2*L+1)*(m*3)+2*Y+3) := by
  induction xs with
  | nil => simp [run,start]
  | cons e xs ih =>
    change (run src dst xs).work+(search src dst (run (L:=L) src dst xs) e).2+2*Y+3≤_
    have one := search_cost src dst (run (L:=L) src dst xs) e
    rw [List.length_cons, Nat.succ_mul xs.length]
    omega

/-- The counter includes the searched packet/color tests and charges the
written permutation row for at most two comparisons per output entry. -/
theorem compile_cost : (compile src dst L).work ≤ m*((2*L+1)*(m*3)+2*Y+3) := by
  simpa [compile] using run_cost (L:=L) src dst (List.finRange m)

end Hierarchy.DescentRotor.Scheduler

end OAI
