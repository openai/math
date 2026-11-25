import OAI.ThreeFlat.Diagonal.LaneCursorReverse
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Numeric owner and canonical-mask tests recover precisely the emitted variable -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout
open RAM.BitLayout
variable {F : Type*} {p k low o c : ℕ} {N : BitNetwork F p}
    (P : RowLayout N k low o c)

def Rectangular.canonicalized (R : P.Rectangular) : P.canonical.Rectangular where
  cell := R.cell
  at_cell := R.at_cell

theorem reverse_source (R : P.Rectangular) (L : Lane k) (t : Fin o × PayloadAddress low c) :
    let own := (splitRow k low).symm (L,t.2.1)
    let row := partner own (P.offset t.1)
    let cell := R.cell row t.2.2.1
    let s := N.source cell t.2.2.2
    let home := sourceRow P.hiddenRow P.pinRow row s
    (P.canonical.reverseProbe (Rectangular.canonicalized P R) L t).map (fun a => N.source a.val.1 a.val.2) =
      if 2 ≤ sourceAddress s ∧ home.val=own.val ∧ firstMask P.offset t.1=true then some s else none := by
  intro own row cell s home
  have site : P.cellAddress cell=(row,t.2.2.1) := R.at_cell _ _
  have lookup : P.canonical.reverseProbe (Rectangular.canonicalized P R) L t =
      if h : wired s then
        let entry : Occurrence N := ⟨(cell,t.2.2.2),h⟩
        if P.canonical.key entry=(L,t) then some entry else none
      else none := rfl
  by_cases live : wired s
  · let a : Occurrence N := ⟨(cell,t.2.2.2),live⟩
    have he : P.owner a=home := by change sourceRow _ _ (P.cellAddress cell).1 s = _; rw [site]
    have good := P.candidate_key_iff R L t live
    change P.canonical.key a=(L,t) ↔ P.owner a=own ∧ firstMask P.offset t.1=true at good
    have large : 2 ≤ sourceAddress s := by
      cases h : s with
      | constant b => simp [h,wired] at live
      | pin i => simp [sourceAddress]
      | hidden i => change 2≤2+p+i.val; omega
    by_cases ok : P.owner a=own ∧ firstMask P.offset t.1=true
    · have done := (P.canonical.reverseProbe_iff (Rectangular.canonicalized P R) L t a).2 (good.mpr ok)
      have hov : home.val=own.val := congrArg Fin.val (he.symm.trans ok.1)
      simp [done,large,hov,ok.2,a,s]
    · have none : P.canonical.reverseProbe (Rectangular.canonicalized P R) L t=none := by
        rw [lookup,dite_eq_left live]
        exact ite_eq_right (fun h=>ok (good.mp h))
      have fail : ¬(2 ≤ sourceAddress s ∧ home.val=own.val ∧ firstMask P.offset t.1=true) :=
        fun h => ok ⟨he.trans (Fin.ext h.2.1),h.2.2⟩
      simp [none,fail]
  · have small : ¬2 ≤ sourceAddress s := by
      cases h : s with
      | constant b => cases b <;> simp [sourceAddress]
      | hidden i => simp [h,wired] at live
      | pin i => simp [h,wired] at live
    have none : P.canonical.reverseProbe (Rectangular.canonicalized P R) L t=none := by
      rw [lookup,dite_eq_right live]
    simp [none,small]

end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
