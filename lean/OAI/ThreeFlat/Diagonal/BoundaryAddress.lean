import OAI.ThreeFlat.Diagonal.BoundaryWire
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Arithmetic addresses of the shared block wires -/

namespace ThreeFlat.Diagonal.BoundaryWire

open RAM.BitLayout

variable {chunks a t n d : ℕ}

theorem chunkSite_val (half : Bool) (slot : Fin chunks) (bit : Fin a) :
    (chunkSite half slot bit).val =
      (if half then chunks*a else 0) + slot.val*a + bit.val := by
  cases half <;> simp [chunkSite, finProdFinEquiv, add_comm, add_left_comm, mul_comm]

theorem auxSite_val (bit : Fin a) :
    (auxSite chunks bit).val = (chunks*a+chunks*a)+bit.val := rfl

theorem publicSource_addr (j : Fin d) :
    sourceAddress (publicSource (chunks:=chunks) (a:=a) (t:=t) (n:=n) j) = 2+j.val := rfl

theorem oldSource_addr (i : Fin (t+1)) (j : Fin (stateWidth chunks a)) :
    sourceAddress (oldSource (n:=n) (d:=d) i j) =
      if i.val = 0 then 2+d+j.val else
        hiddenBase (pinWidth chunks a d) + (i.val-1)*stateWidth chunks a + j.val := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [oldSource, sourceAddress, add_assoc]
    rfl
  · simp only [oldSource, Fin.cons_succ, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
      Nat.add_sub_cancel]
    change hiddenBase _ + (j.val + stateWidth chunks a * k.val) = _
    ac_rfl

theorem newSource_addr (i : Fin (t+1)) (j : Fin (stateWidth chunks a)) :
    sourceAddress (newSource (n:=n) (d:=d) i j) =
      if i.val = t then 2+d+stateWidth chunks a+j.val else
        hiddenBase (pinWidth chunks a d) + i.val*stateWidth chunks a+j.val := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [newSource, sourceAddress, add_assoc]
    rfl
  · have hk : k.val ≠ t := Nat.ne_of_lt k.isLt
    simp only [newSource, Fin.snoc_castSucc, Fin.val_castSucc, hk, ite_false]
    change hiddenBase _ + (j.val + stateWidth chunks a * k.val) = _
    ac_rfl

theorem interiorSource_addr (i : Fin (t+1)) (k : Fin n) (j : Fin a) :
    sourceAddress (interiorSource (chunks:=chunks) (d:=d) i k j) =
      hiddenBase (pinWidth chunks a d) + t*stateWidth chunks a + i.val*(n*a) + k.val*a + j.val := by
  change hiddenBase _ + (t*stateWidth chunks a + (j.val+a*k.val + (n*a)*i.val)) = _
  ac_rfl

end ThreeFlat.Diagonal.BoundaryWire

end OAI
