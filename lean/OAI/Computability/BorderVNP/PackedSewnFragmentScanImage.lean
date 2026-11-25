import OAI.Computability.BorderVNP.PackedSewnFragmentScan

/-! # Exact chronological image of the sparse physical coalescing circuit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open VPVNP.VerifierNetwork
open private input advance_bit from OAI.Computability.BorderVNP.PackedSewnFragmentScan

variable {w n : ℕ} (p : Frame (Bool × Column w) (Bool × Column w))

private theorem list_mem (x : Pin n w → Bool) (i : Fin n) {a : Parsed}
    (ha : a ∈ read (fun j => x (i,j))) : a ∈ list x := by
  apply List.mem_filterMap.mpr
  exact ⟨i,List.mem_finRange i,ha⟩

private theorem no_rows (x : Pin (n+1) w → Bool) (hc : Compact x) (h : active x 0 = false) : list x = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro i _
  have dead : active x i = false := by
    by_contra! live
    exact Bool.noConfusion (h.symm.trans (hc 0 i (Fin.zero_le _) (Bool.eq_true_of_not_eq_false live)))
  simp only [dead,Bool.false_eq_true,ite_false]

private theorem tail_compact (x : Pin (n+1) w → Bool) (hc : Compact x) : Compact (tail x) :=
  fun i j h => hc i.succ j.succ (Fin.succ_le_succ_iff.mpr h)

private theorem absorb_front (a b : Option Parsed) : (absorb a b).1.isSome = a.isSome := by
  cases a <;> cases b <;> simp [absorb,apply_ite Prod.fst,apply_ite Option.isSome]

private theorem absorb_list (a b : Option Parsed) (rest : List Parsed) (empty : b=none → rest=[]) :
    (absorb a b).1.toList ++ ((absorb a b).2.toList ++ rest) =
      a.elim (b.toList ++ rest) (fun r => prepend r (b.toList ++ rest)) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rw [empty rfl]; rfl
    | some b => by_cases h : a.compatible b <;> simp [absorb,prepend,h]

private theorem read_flag (x : Column w → Bool) : (read x).isSome = x (.inl false) := by
  cases h : x (.inl false) <;> simp [read,h]

private theorem identity_eval (x : Pin n w → Bool) : (Frame.initial (id : Pin n w → _)).eval x = x :=
  funext (Frame.initial_eval _ _)

/-- Every enabled output is one maximal run, in the old-lane order of the sorted
positive source, and the first source position is retained whenever it is live. -/
theorem scan_state (hp : PairSpec p) (n : ℕ) (x : Pin n w → Bool) (hc : Compact x)
    (fit : ∀ a ∈ list x, a.Fits w) :
    list ((scan p n).eval x) = coalesce (list x) ∧
      ∀ i : Fin n, i.val = 0 → active ((scan p n).eval x) i = active x i := by
  induction n with
  | zero => exact ⟨rfl,fun i => i.elim0⟩
  | succ n ih =>
    cases n with
    | zero =>
      rw [scan,identity_eval]
      refine ⟨?_,fun _ _ => rfl⟩
      rw [list_cons]
      change _ ++ [] = coalesce (_ ++ [])
      cases read (fun j => x (0,j)) <;> rfl
    | succ n =>
      let xx := tail x
      let y := (scan p (n+1)).eval xx
      let z := (scan p (n+2)).eval x
      let u := input x y
      let a := read (fun j => x (0,j))
      let b := read (fun j => y (0,j))
      have priorImage := ih xx (tail_compact x hc) (fun r hr => fit r (list_cons x ▸ List.mem_append_right _ hr))
      have raw : (∀ k : Bool, ∀ t ∈ read (fun j => u (k,j)), t.Fits w) := by
        rintro (_|_) t h
        · exact fit t (list_mem x 0 h)
        · exact coalesce_fits (fun r hr => fit r (list_cons x ▸ List.mem_append_right _ hr)) t
            (priorImage.1 ▸ list_mem y 0 h)
      have update := hp u raw
      have same := advance_bit p (scan p (n+1)) x
      have left : (fun j => z (0,j)) = (fun j => p.eval u (false,j)) :=
        funext (same 0)
      have right : (fun j => z ((0 : Fin (n+1)).succ,j)) = (fun j => p.eval u (true,j)) :=
        funext (same (0 : Fin (n+1)).succ)
      have later : tail (tail z) = tail y := by
        funext q
        exact same q.1.succ.succ q.2
      have pairEq : (read (fun j => z (0,j)),read (fun j => (tail z) (0,j))) = absorb a b := by
        change (read (fun j => z (0,j)),read (fun j => z ((0 : Fin (n+1)).succ,j))) = _
        rw [left,right]
        exact update
      have lh : read (fun j => z (0,j)) = (absorb a b).1 := congrArg Prod.fst pairEq
      have rh : read (fun j => (tail z) (0,j)) = (absorb a b).2 := congrArg Prod.snd pairEq
      have head : active z 0 = active x 0 := by
        simpa only [a,read_flag,active] using (congrArg Option.isSome (congrArg Prod.fst pairEq)).trans (absorb_front a b)
      have vacant (h : b=none) : list (tail y) = [] := by
        have first : active xx 0 = false := by
          have val := congrArg Option.isSome h
          rw [←priorImage.2 0 rfl]
          exact (read_flag (fun j => y (0,j))).symm.trans val
        have noneLeft := no_rows xx (tail_compact x hc) first
        have nil : list y = [] := priorImage.1.trans ((congrArg coalesce noneLeft).trans rfl)
        rw [list_cons] at nil
        exact (List.append_eq_nil_iff.mp nil).2
      refine ⟨?_,?_⟩
      · change list z = _
        rw [list_cons z,list_cons (tail z),later,lh,rh,
          absorb_list a b (list (tail y)) vacant]
        rw [show b.toList ++ list (tail y) = list y from (list_cons y).symm,show list y = coalesce (list xx) from priorImage.1,list_cons x]
        cases aeq : read (fun j => x (0,j)) <;> simp [a,aeq,xx,coalesce]
      · intro i hi
        have eqn : i = 0 := Fin.ext hi
        exact eqn ▸ head

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
