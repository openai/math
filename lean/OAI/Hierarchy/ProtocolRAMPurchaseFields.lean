import OAI.Hierarchy.ProtocolRAMPurchaseTape

namespace OAI
/-! # Read bounds for the fixed sampler path expressions -/

namespace Hierarchy.ProtocolRAM.PurchaseColumns
open PurchaseWord PurchaseDirectory
variable {D limit : ℕ}

private theorem substitute (x j : Expr) (hx : x.inputEnd≤limit) (hj : j.inputEnd≤limit) :
    (x.atRow j).inputEnd≤limit := by
  induction x <;> simp_all [Expr.atRow,Expr.inputEnd]

private theorem choose (D base : ℕ) (xs : Fin D→Expr) (d : Expr)
    (hx : ∀ i,(xs i).inputEnd≤limit) (hd : d.inputEnd≤limit) :
    (chooseField D base xs d).inputEnd≤limit := by
  induction D generalizing base with
  | zero => exact Nat.zero_le _
  | succ D ih =>
    have tail := ih (base+1) (fun i=>xs i.succ) (fun i => hx i.succ)
    simp [chooseField,Expr.inputEnd,hd,hx,tail]

private theorem advance_le (edges : Fin D→Expr) (x d : Expr) (he : ∀ i,(edges i).inputEnd≤limit)
    (hx : x.inputEnd≤limit) (hd : d.inputEnd≤limit) : (advance edges x d).inputEnd≤limit := by
  have step : (Expr.op .sub x (.lit 1)).inputEnd≤limit := by simp [Expr.inputEnd,hx]
  have chosen := choose D 0 (fun i => (edges i).atRow (.op .sub x (.lit 1))) d
    (fun i=>substitute _ _ (he i) step) hd
  simp [advance,Expr.inputEnd,hx,chosen]

private theorem states_le (edges : Fin D→Expr) (x : Expr) (ds : List Expr)
    (he : ∀ i,(edges i).inputEnd≤limit) (hx : x.inputEnd≤limit) (hd : ∀ d∈ds,d.inputEnd≤limit) :
    ∀ v∈states edges x ds,v.inputEnd≤limit := by
  induction ds generalizing x with
  | nil => simpa [states] using hx
  | cons d ds ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | later
    · exact hx
    · exact ih _ (advance_le _ _ _ he hx (hd _ List.mem_cons_self))
        (fun t ht => hd t (.tail _ ht)) v later

private theorem distinct_le (x : Expr) (xs : List Expr) (yes no : Expr)
    (hx : x.inputEnd≤limit) (hxs : ∀ y∈xs,y.inputEnd≤limit)
    (hy : yes.inputEnd≤limit) (hn : no.inputEnd≤limit) : (distinctFrom x xs yes no).inputEnd≤limit := by
  induction xs with
  | nil => exact hy
  | cons a xs ih =>
    have a' := hxs _ List.mem_cons_self
    have t := ih (fun v hv => hxs v (.tail _ hv))
    simp [distinctFrom,Expr.inputEnd,hx,a',hn,t]

private theorem guard_le (xs : List Expr) (yes no : Expr)
    (hxs : ∀ y∈xs,y.inputEnd≤limit) (hy : yes.inputEnd≤limit) (hn : no.inputEnd≤limit) :
    (guard xs yes no).inputEnd≤limit := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
    have x' := hxs _ List.mem_cons_self
    have lo (y : Expr) (hy : y ∈ xs) := hxs y (.tail _ hy)
    have tail := distinct_le x xs (guard xs yes no) no x' lo (ih lo) hn
    change max (max x.inputEnd 0) (max no.inputEnd _)≤limit
    exact max_le (max_le x' (Nat.zero_le _)) (max_le hn tail)

/-- Every input cell in the full validity/trajectory expression belongs to the
public start/digit directory or to a single successor lookup. -/
theorem field_below (dir n h : ℕ) (edges : Fin D→Expr)
    (he : ∀ i,(edges i).inputEnd≤limit) (hd : dir+(h+1)*span n D h≤limit) (j : Fin (h+1)) :
    (field dir n h edges j).inputEnd≤limit := by
  have lane (l : Fin (h+1)) : (Expr.lookup (bank dir n D h l.val) .row).inputEnd≤limit := by
    have bound := Nat.mul_le_mul_right (span n D h) l.isLt
    rw [Nat.succ_mul] at bound
    change max (dir+l.val*span n D h+span n D h) 0≤limit
    omega
  let digits := List.ofFn fun j : Fin h => Expr.lookup (bank dir n D h (j.val+1)) .row
  have ds : ∀ e∈digits,e.inputEnd≤limit := by
    intro e mem
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp mem
    exact lane t.succ
  have stateBound := states_le edges (.lookup (bank dir n D h 0) .row) digits he (lane 0) ds
  let es := stateExprs dir n h edges
  have all : ∀ x∈es,x.inputEnd≤limit := stateBound
  have i : j.val < es.length := by simpa [es] using j.isLt
  have x' := all es[j.val] (List.getElem_mem i)
  apply guard_le es _ _ all
  · exact max_le x' (Nat.zero_le _)
  · exact Nat.zero_le _

end Hierarchy.ProtocolRAM.PurchaseColumns

namespace Hierarchy.ProtocolRAM.PurchaseTape
variable {D : ℕ}

/-- Field bounds follow immediately from the physical bank extents. -/
theorem fields_below (s : Plan D) (n h : ℕ)
    (groups : s.columns.group.base+s.columns.group.size ≤ s.source.base)
    (stride : s.columns.stride.base+s.columns.stride.size ≤ s.source.base)
    (output : s.columns.output.base+s.columns.output.size ≤ s.source.base)
    (owners : s.columns.owner.base+s.columns.owner.size ≤ s.source.base)
    (neighbors : ∀ j,(s.neighbor j).base+(s.neighbor j).size ≤ s.source.base)
    (digits : s.directory+(h+1)*PurchaseDirectory.span n D h ≤ s.source.base) (j : Fin (h+1)) :
    (PurchaseColumns.field s.directory n h (edge s) j).inputEnd ≤ s.source.base := by
  apply PurchaseColumns.field_below _ _ _ _ _ digits
  intro i
  simp [edge,ProtocolRAMPurchaseOwners.nextWord,Expr.inputEnd,groups,stride,output,owners,neighbors]

end Hierarchy.ProtocolRAM.PurchaseTape

end OAI
