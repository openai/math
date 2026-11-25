import OAI.ThreeFlat.Routing.StableCompactPredicates
import OAI.ThreeFlat.Routing.StableCompactStages
import OAI.ThreeFlat.Routing.StableCompactRows
import Mathlib.Data.Fin.Init

namespace OAI
/-! # Compaction-stage histories read from native physical source addresses -/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.StableCompactNative

open StableCompactRows StableCompactSite StableCompactStages
open StableCompaction (record masked compact)

abbrev stages (m : ℕ) := (steps m).length
abbrev shared (m : ℕ) := (stages m+1)*width m
abbrev Sites (m : ℕ) := Fin (2^m)
abbrev Bits (m : ℕ) := Sites m → Bool
abbrev Regs (m : ℕ) := Fin (shared m) → Bits m
private abbrev Src (m : ℕ) := Source m (shared m)

private def layer {m : ℕ} (r : Fin (stages m)) := (steps m).get r

private def register {m : ℕ} (t : Fin (stages m+1)) (j : Fin (width m)) : Fin (shared m) :=
  finProdFinEquiv (t,j)

def history (m : ℕ) : Regs m ≃ Values m (width m) where
  toFun h t v j := h (register t j) v
  invFun H a v := H (finProdFinEquiv.symm a).1 v (finProdFinEquiv.symm a).2
  left_inv h := by
    funext a v
    change h (finProdFinEquiv (finProdFinEquiv.symm a)) v = h a v
    rw [Equiv.apply_symm_apply]
  right_inv H := by
    funext t v j
    change H (finProdFinEquiv.symm (finProdFinEquiv (t,j))).1 v
      (finProdFinEquiv.symm (finProdFinEquiv (t,j))).2 = H t v j
    rw [Equiv.symm_apply_apply]

private def dataSrc (m : ℕ) : Fin (width m) → Src m :=
  Fin.append (Fin.append (fun _ : Fin 1 => .pin 1) (fun j : Fin m => .siteBit j.val))
    (fun _ : Fin 1 => .pin 0)

private def regSrc {m : ℕ} (t : Fin (stages m+1)) (j : Fin (width m)) (mask : Sites m) : Src m :=
  .hidden (register t j) mask

private def source (m : ℕ) : (g : Gate m (stages m)) → Port g → Src m
  | .inl j => ![dataSrc m j,regSrc 0 j 0,.constant false]
  | .inr (.inr _) => ![regSrc (Fin.last _) (Fin.last (1+m)) 0,regSrc (Fin.last _) 0 0,.pin 2]
  | .inr (.inl r) => fun p => match p with
    | .inl d => ![.siteBit (layer r).stride,.siteBit (layer r).phase] d
    | .inr (d,j) => ![regSrc r.castSucc j 0,regSrc r.castSucc j (strideMask (layer r)),regSrc r.succ j 0] d

def wires (m : ℕ) (j : Fin (Fintype.card (Label m (stages m)))) : Src m :=
  let q := (Fintype.equivFin (Label m (stages m))).symm j
  source m q.1 q.2

private theorem xor_zero_site {m : ℕ} (v : Sites m) : v ^^^ (0 : Sites m) = v := Fin.xor_zero v

private theorem reg_read {m} (t : Fin (stages m+1)) (j : Fin (width m)) (M X Y : Bits m)
    (h : Regs m) (v : Sites m) :
    (regSrc t j 0).read M X Y h v = history m h t v j := by
  change h _ (v ^^^ 0) = h _ v
  rw [xor_zero_site]

private theorem input_at {m : ℕ} (M X Y : Bits m) (h : Regs m) (v : Sites m) (j : Fin (width m)) :
    (if inverted j then !((dataSrc m j).read M X Y h v) else (dataSrc m j).read M X Y h v) =
      record M X v j := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [inverted,dataSrc,record,Fin.append_left,Source.read,Bool.false_eq_true,ite_false]; rfl
    · simp only [inverted,dataSrc,record,Fin.append_left,Fin.append_right,Source.read,Bool.false_eq_true,ite_false]; rfl
  · simp only [inverted,dataSrc,record,Fin.append_right,Source.read,ite_true]; rfl

def labelBits {m : ℕ} (M X Y : Bits m) (h : Regs m) (v : Sites m)
    (p : Label m (stages m)) : Bool := (source m p.1 p.2).read M X Y h v

private theorem pass_init {m : ℕ} (M X Y : Bits m) (h : Regs m) (v : Sites m) (j : Fin (width m)) :
    pass (k := stages m) (.inl j) (fun i => labelBits M X Y h v ⟨.inl j,i⟩) ↔
      history m h 0 v j = record M X v j := by
  change (regSrc 0 j 0).read M X Y h v =
    (if inverted j then !((dataSrc m j).read M X Y h v) else (dataSrc m j).read M X Y h v) ↔ _
  rw [reg_read,input_at]

private theorem pass_last {m : ℕ} (M X Y : Bits m) (h : Regs m) (v : Sites m) :
    pass (m := m) (k := stages m) (.inr (.inr ())) (fun i => labelBits M X Y h v ⟨.inr (.inr ()),i⟩) ↔
      Y v = masked (history m h (Fin.last _) v) := by
  change Y v = (!((regSrc (Fin.last _) (Fin.last (1+m)) 0).read M X Y h v) &&
    (regSrc (Fin.last _) 0 0).read M X Y h v) ↔ _
  rw [reg_read,reg_read]; rfl

private theorem pass_step {m : ℕ} (M X Y : Bits m) (h : Regs m) (v : Sites m) (r : Fin (stages m)) :
    pass (m := m) (k := stages m) (.inr (.inl r)) (fun i => labelBits M X Y h v ⟨.inr (.inl r),i⟩) ↔
      history m h r.succ v = next (layer r) v (history m h r.castSucc v)
        (history m h r.castSucc (mate (layer r) v)) := by
  change ((fun j => (regSrc r.succ j 0).read M X Y h v) =
    StableCompactStep.selected (v.val.testBit (layer r).stride) (v.val.testBit (layer r).phase)
    (fun j => (regSrc r.castSucc j 0).read M X Y h v)
    (fun j => (regSrc r.castSucc j (strideMask (layer r))).read M X Y h v)) ↔ _
  simp only [reg_read,mate_eq_xor]; rfl

theorem accepted {m : ℕ} (M X Y : Bits m) (h : Regs m) :
    (∀ (v : Sites m) (g : Gate m (stages m)), pass (m:=m) (k:=stages m) g
      (fun j => labelBits M X Y h v ⟨g,j⟩)) ↔ Accepts M X Y (history m h) := by
  constructor
  · intro a
    exact ⟨fun v => funext fun j => (pass_init M X Y h v j).mp (a v (.inl j)),
      fun r v => (pass_step M X Y h v r).mp (a v (.inr (.inl r))),
      fun v => (pass_last M X Y h v).mp (a v (.inr (.inr ())))⟩
  · rintro ⟨hi,hs,ho⟩ v (j | (r | z))
    · exact (pass_init M X Y h v j).mpr (congrFun (hi v) j)
    · exact (pass_step M X Y h v r).mpr (hs r v)
    · cases z
      exact (pass_last M X Y h v).mpr (ho v)

end ThreeFlat.Routing.StableCompactNative

end
end OAI
