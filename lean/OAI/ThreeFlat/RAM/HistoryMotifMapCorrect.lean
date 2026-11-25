import OAI.ThreeFlat.RAM.HistoryMotifMaps
import OAI.ThreeFlat.Diagonal.MotifSelectorChecks
import OAI.ThreeFlat.Diagonal.MotifOrderedCells

namespace OAI
/-! # Physical addresses of the four actual histogram component maps -/

namespace ThreeFlat.RAM.HistoryMotifMaps

open Diagonal Diagonal.MotifOrderedCells BitLayout Diagonal.MotifOuterTerms Diagonal.MotifSelectorChecks
open scoped Classical

variable {r b d e h : ℕ}

private theorem index_val {n m : ℕ} (a : Fin n) (i : Fin m) : (finProdFinEquiv (a,i)).val = i.val+m*a.val := rfl

private theorem divIndex {n m : ℕ} (x : Fin n) (y : Fin m) : (finProdFinEquiv (x,y)).val / m = x.val ∧
    (finProdFinEquiv (x,y)).val % m = y.val := by
  have hp : 0 < m := Nat.zero_lt_of_lt y.isLt
  simp [Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt y.isLt,Nat.mod_eq_of_lt y.isLt]

theorem tile_source (i : Fin r) (x : Fin (b+(e*d+e*d))) (letters quota : ℕ) :
    word .tile x.val i.val r b e d letters quota = sourceAddress (tileWire (e:=e) (b:=b) (d:=d) i x) := by
  refine Fin.addCases (fun j => ?_) (fun z => ?_) x
  · simp [word,tileWire,headAddr,sourceAddress,j.isLt,Nat.add_comm]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) z <;>
      obtain ⟨⟨a,l⟩,rfl⟩ := finProdFinEquiv.surjective j
    · have hd := divIndex a l
      have bound := (finProdFinEquiv (a,l)).isLt
      simp only [tileWire,Fin.append_left,Fin.append_right,Equiv.symm_apply_apply]
      simp (disch := omega) only [word,Fin.val_castAdd,Fin.val_natAdd,Nat.add_sub_cancel_left,
        ite_eq_left,ite_eq_right,hd.1,hd.2]
      simp [maskAddr,gAddr,sourceAddress,hiddenBase,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · have hd := divIndex a l
      simp only [tileWire,Fin.append_right,Equiv.symm_apply_apply]
      simp (disch := omega) only [word,Fin.val_natAdd,Nat.add_sub_cancel_left,
        ite_eq_right,hd.1,hd.2]
      simp [dataAddr,gAddr,sourceAddress,hiddenBase,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem stream_source (a : Fin e) (x : Fin ((r*d)+(r*d+r*d))) (letters quota : ℕ) :
    word .stream x.val a.val r b e d letters quota = sourceAddress (streamWire (r:=r) (b:=b) (d:=d) a x) := by
  refine Fin.addCases (fun j => ?_) (fun z => ?_) x
  · obtain ⟨⟨i,l⟩,rfl⟩ := finProdFinEquiv.surjective j
    have bound := (finProdFinEquiv (i,l)).isLt
    simp only [streamWire,Fin.append_left,Equiv.symm_apply_apply]
    simp (disch := omega) only [word,Fin.val_castAdd,ite_eq_left]
    simp [maskAddr,gAddr,sourceAddress,hiddenBase,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) z
    · obtain ⟨⟨i,l⟩,rfl⟩ := finProdFinEquiv.surjective j
      have bound := (finProdFinEquiv (i,l)).isLt
      simp only [streamWire,Fin.append_left,Fin.append_right,Equiv.symm_apply_apply]
      simp (disch := omega) only [word,Fin.val_castAdd,Fin.val_natAdd,Nat.add_sub_cancel_left,ite_eq_left,ite_eq_right]
      simp [dataAddr,gAddr,sourceAddress,hiddenBase,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp only [streamWire,Fin.append_right]
      simp (disch := omega) only [word,Fin.val_natAdd,Nat.add_sub_cancel_left,ite_eq_right]
      simp [outAddr,sourceAddress,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem localTest_source (i : Fin r) (x : Fin (b+h)) (ports width quota : ℕ) :
    word .localTest x.val i.val r b ports width h quota = sourceAddress (localWire (b:=b) (h:=h) i x) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) x <;> simp [word,localWire,sourceAddress,hiddenBase,j.isLt,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem counter_source (z : Histogram (Fin h) r) (a : Fin h) (x : Fin (r+(r+r))) (ports width : ℕ) :
    word .counter x.val a.val r b ports width h (z.val a).val = sourceAddress (countWire (p:=r*b) z a x) := by
  refine Fin.addCases (fun i => ?_) (fun t => ?_) x
  · simp [word,countWire,sourceAddress,hiddenBase,i.isLt,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) t
    · simp [word,countWire,sourceAddress,i.isLt]
    · simp only [countWire,Fin.append_right]
      by_cases q : i.val < (z.val a).val <;> simp [word,sourceAddress,unary,q]

end ThreeFlat.RAM.HistoryMotifMaps

end OAI
