import OAI.Hierarchy.ProtocolRAMPurchasePathColumns

namespace OAI
/-! # Candidate scan cost independent of the number of physical CT rows -/

namespace Hierarchy.ProtocolRAM.PurchaseColumns
open PurchaseWord

private theorem substitute_bound (x j : Expr) : (x.atRow j).work ≤ x.work*(j.work+1) := by
  induction x <;> simp only [Expr.atRow,Expr.work,Nat.add_mul,Nat.one_mul] at * <;> omega

private theorem choose_bound (D key limit : ℕ) (v : Fin D → Expr) (d : Expr)
    (bound : ∀ j,(v j).work ≤ limit) :
    (chooseField D key v d).work ≤ 1+D*(d.work+limit+2) := by
  induction D generalizing key with
  | zero => simp [chooseField,Expr.work]
  | succ D ih =>
    have h := ih (key+1) (fun j=>v j.succ) (fun j=>bound j.succ)
    have z := bound 0
    simp only [chooseField,Expr.work,Nat.succ_mul]
    omega

private def nextBudget (D U : ℕ) := U+4+D*(47*(U+3)+9)

private theorem advance_bound {D : ℕ} (edge : Fin D→Expr) (state digit : Expr) (U : ℕ)
    (he : ∀ j, (edge j).work≤47) (hs : state.work≤U) (hd : digit.work≤7) :
    (advance edge state digit).work ≤ nextBudget D U := by
  have alternatives (j : Fin D) : ((edge j).atRow (.op .sub state (.lit 1))).work≤47*(U+3) :=
    (substitute_bound ..).trans (Nat.mul_le_mul (he j) (by simp [Expr.work]; omega))
  have hc := choose_bound D 0 _ _ digit alternatives
  have scale := Nat.mul_le_mul_left D (show digit.work+47*(U+3)+2 ≤ 47*(U+3)+9 by omega)
  simp only [advance,Expr.work,nextBudget]
  omega

def stateBudget (D : ℕ) : ℕ → ℕ → ℕ
  | 0,U => U
  | h+1,U => stateBudget D h (nextBudget D U)

private theorem budget_ge (D h U : ℕ) : U ≤ stateBudget D h U := by
  induction h generalizing U with
  | zero => exact le_rfl
  | succ h ih =>
    exact (by unfold nextBudget; omega : U≤nextBudget D U).trans (ih _)

private theorem states_bound {D : ℕ} (edge : Fin D→Expr) (ds : List Expr) (state : Expr)
    (he : ∀ j,(edge j).work≤47) (dsWork : ∀ d∈ds,d.work≤7) (U : ℕ) (hs : state.work≤U) :
    ∀ e∈states edge state ds, e.work ≤ stateBudget D ds.length U := by
  induction ds generalizing state U with
  | nil => simpa [states,stateBudget] using hs
  | cons d ds ih =>
    intro e member
    rcases List.mem_cons.mp member with rfl | later
    · exact hs.trans (budget_ge ..)
    · exact ih _ (fun x hx=>dsWork x (by simp [hx])) _
        (advance_bound edge state d U he hs (dsWork d (by simp))) e later

private theorem different_bound (x : Expr) (ys : List Expr) (yes no : Expr) (B : ℕ)
    (hx : x.work≤B) (hy : ∀ y∈ys,y.work≤B) :
    (distinctFrom x ys yes no).work ≤ yes.work+ys.length*(2*B+no.work+1) := by
  induction ys with
  | nil => simp [distinctFrom]
  | cons y ys ih =>
    have tail := ih (fun z hz => hy z (by simp [hz]))
    have current := hy y (by simp)
    simp only [distinctFrom,Expr.work,List.length_cons]
    rw [Nat.succ_mul ys.length]
    omega

private def guardBudget (B yes no : ℕ) : ℕ → ℕ
  | 0 => yes
  | k+1 => B+2+no+guardBudget B yes no k+k*(2*B+no+1)

private theorem check_bound (es : List Expr) (yes no : Expr) (B Y : ℕ)
    (hs : ∀e∈es,e.work≤B) (hy : yes.work≤Y) :
    (guard es yes no).work ≤ guardBudget B Y no.work es.length := by
  induction es with
  | nil => exact hy
  | cons e es ih =>
    have head := hs e (by simp)
    have tails := fun q hq => hs q (List.mem_cons_of_mem e hq)
    have a := different_bound e es (guard es yes no) no B head tails
    have b := ih tails
    simp only [PurchaseWord.guard,Expr.work,List.length_cons,guardBudget]
    omega

def fieldBudget (D h : ℕ) : ℕ :=
  let B := stateBudget D h 7
  guardBudget B (B+2) 1 (h+1)

theorem field_cost {D h : ℕ} (dir n : ℕ) (edge : Fin D→Expr) (j : Fin (h+1))
    (bounded : ∀ d, (edge d).work≤47) : (field dir n h edge j).work ≤ fieldBudget D h := by
  let es := stateExprs dir n h edge
  have hs (q : Expr) (hq : q∈es) : q.work ≤ stateBudget D h 7 := by
    have arg : ∀ e∈(List.ofFn fun d : Fin h => Expr.lookup (PurchaseDirectory.bank dir n D h (d.val+1)) .row),e.work≤7 := by
      intro e he
      obtain ⟨d,rfl⟩ := List.mem_ofFn.mp he
      exact Nat.le_refl 7
    simpa using states_bound edge _ (.lookup (PurchaseDirectory.bank dir n D h 0) .row) bounded arg 7 (Nat.le_refl 7) q hq
  have hj : j.val < es.length := by simpa [es] using j.isLt
  have he := hs _ (List.getElem_mem (l:=es) hj)
  have result := check_bound es (.op .sub es[j.val] (.lit 1)) (.lit n) (stateBudget D h 7) _ hs
    (show (Expr.op .sub es[j.val] (.lit 1)).work ≤ stateBudget D h 7+2 by simp [Expr.work];omega)
  simpa [field,PurchaseWord.tile,fieldBudget,es,Expr.work] using result

theorem clock_bound {D : ℕ} (dir out n h : ℕ) (edge : Fin D→Expr) (bound : ∀ d, (edge d).work≤47) :
    clock (passes dir out n h edge) ≤ 4+(h+1)*(4+n*D^h*(2*fieldBudget D h+4)) := by
  have c := ProbeStage.Native.columns_clock (PurchaseDFS.layout n D h).length out (fieldBudget D h)
    (List.ofFn (field dir n h edge)) (by intro e he; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he; exact field_cost dir n edge j bound)
  simpa [passes] using c

end Hierarchy.ProtocolRAM.PurchaseColumns

end OAI
