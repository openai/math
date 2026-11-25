import OAI.Hierarchy.ProtocolRAMPurchaseDirectory
import OAI.Hierarchy.ProtocolRAMPurchasePathWords
import OAI.Hierarchy.ProbeStageColumnScan
import Mathlib.Data.List.Forall2

namespace OAI
/-! # Physical tile-ID columns for the addressed purchase scanner -/

namespace Hierarchy.ProtocolRAM.PurchaseColumns
open Computability.VPVNP.BurstRAM PrivateRAM PurchaseDirectory
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {n D h w : ℕ}

private def args (dir n D h : ℕ) := List.ofFn (fun j : Fin h => Expr.lookup (bank dir n D h (j.val+1)) .row)

def stateExprs (dir n h : ℕ) (edge : Fin D → Expr) : List Expr :=
  PurchaseWord.states edge (.lookup (bank dir n D h 0) .row) (args dir n D h)

@[simp] theorem length_stateExprs (dir n h : ℕ) (edge : Fin D → Expr) :
    (stateExprs dir n h edge).length = h+1 := by simp [stateExprs,args]

def field (dir n h : ℕ) (edge : Fin D → Expr) (j : Fin (h+1)) : Expr :=
  let es := stateExprs dir n h edge
  PurchaseWord.tile n es (es[j.val]'(by simpa [es] using j.isLt))

private def vs (choice : Fin n → Fin D → Option (Fin n)) (i : Index n D h) :=
  PurchaseDFS.optionStates choice (some (item i).1) (List.ofFn (item i).2)

/-- The sentinel row is shared by all padded and nonsimple candidates. -/
def rowTile (choice : Fin n → Fin D → Option (Fin n)) (i : Index n D h) (j : Fin (h+1)) : Fin (n+1) :=
  let paths := vs choice i
  let x := paths[j.val]'(by simpa [paths,vs] using j.isLt)
  if none ∉ paths ∧ paths.Nodup then x.elim (Fin.last n) Fin.castSucc else Fin.last n

private theorem option_val (x : Option (Fin n)) :
    ((x.elim (Fin.last n) Fin.castSucc).val : ℕ) = x.elim n Fin.val := by cases x <;> rfl

theorem eval_field (dir : ℕ) (edge : Fin D → Expr) (choice : Fin n → Fin D → Option (Fin n))
    (m : Memory w) (loaded : PurchaseDirectory.Loaded dir n D h m)
    (room : n < 2^w) (degree : D ≤ 2^w)
    (correct : ∀ (r : Fin n) (j : Fin D), (edge j).eval m (r.val:Word w) = (PurchaseWord.code (choice r j):Word w))
    (i : Index n D h) (j : Fin (h+1)) :
    (field dir n h edge j).eval m (i.val:Word w) = ((rowTile choice i j).val : Word w) := by
  let es := stateExprs dir n h edge
  let vals := vs choice i
  have he : j.val < es.length := by simpa [es] using j.isLt
  have hv : j.val < vals.length := by simpa [vals,vs] using j.isLt
  have args_ok : List.Forall₂ (fun e (v : Fin D) => (Expr.eval m (i.val:Word w) e).val=v.val)
      (args dir n D h) (List.ofFn (item i).2) := by
    apply List.forall₂_of_length_eq_of_get (by simp [args])
    intro k h₁ h₂
    have hk : k<h := by simpa using h₂
    have small := (((item i).2 ⟨k,hk⟩).isLt.trans_le degree)
    simpa [args,Expr.eval,Fin.val_cast_of_lt small] using
      congrArg Fin.val (loaded.digit i ⟨k,hk⟩)
  have values : es.map (Expr.eval m (i.val:Word w)) = vals.map (fun t => (PurchaseWord.code t : Word w)) :=
    PurchaseWord.eval_states edge _ _ m _ choice (some (item i).1) _ room degree
      (loaded.start i) args_ok correct
  have evalue : (es[j.val]).eval m (i.val : Word w) = (PurchaseWord.code vals[j.val] : Word w) := by
    calc
      _ = (es.map (Expr.eval m (i.val : Word w)))[j.val]'(by simpa using he) :=
        (List.getElem_map (Expr.eval m (i.val : Word w))).symm
      _ = (vals.map (fun t => (PurchaseWord.code t : Word w)))[j.val]'(by simpa using hv) :=
        getElem_congr values rfl _
      _ = _ := List.getElem_map _
  rw [field,PurchaseWord.eval_tile _ _ _ _ vals vals[j.val] room values evalue (List.getElem_mem ..)]
  by_cases ok : none ∉ vals ∧ vals.Nodup <;> simp [rowTile,vals,ok,option_val]

def passes (dir out n h : ℕ) (edge : Fin D → Expr) :=
  ProbeStage.Native.columns (PurchaseDFS.layout n D h).length out (List.ofFn (field dir n h edge))

theorem emit (dir out : ℕ) (edge : Fin D → Expr) (choice : Fin n → Fin D → Option (Fin n))
    (m : Memory w) (loaded : PurchaseDirectory.Loaded dir n D h m)
    (room : n < 2^w) (degree : D ≤ 2^w)
    (correct : ∀ (r : Fin n) (j : Fin D), (edge j).eval m (r.val:Word w) = (PurchaseWord.code (choice r j):Word w))
    (fits : ∀ j, (field dir n h edge j).Fits w out)
    (extent : out+(h+1)*(PurchaseDFS.layout n D h).length < 2^w) :
    (program w (passes dir out n h edge)).Exec m (result (passes dir out n h edge) m) (clock (passes dir out n h edge)) ∧
    ∀ (i : Index n D h) (j : Fin (h+1)), result (passes dir out n h edge) m
      (out+j.val*(PurchaseDFS.layout n D h).length+i.val) = ((rowTile choice i j).val : Word w) := by
  let cols := List.ofFn (field dir n h edge)
  have readers : ∀ e∈cols, e.Fits w out := by
    intro e he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact fits j
  refine ⟨program_exec _ _ (ProbeStage.Native.columns_safe cols le_rfl readers (by simpa [cols] using extent)),?_⟩
  intro i j
  have read := ProbeStage.Native.columns_read cols m le_rfl readers j.val (by simpa [cols] using j.isLt) i
  exact read.trans (by simpa only [cols,List.getElem_ofFn] using eval_field dir edge choice m loaded room degree correct i j)

end Hierarchy.ProtocolRAM.PurchaseColumns

end OAI
