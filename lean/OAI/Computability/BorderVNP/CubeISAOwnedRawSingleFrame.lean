import OAI.Computability.BorderVNP.CubeScatterRawSingletonFrame
import OAI.Computability.BorderVNP.CubeISAOwnedStrictScatter
import OAI.Computability.BorderVNP.CubeISAOwnedStageInverse
import OAI.Computability.BorderVNP.RoutingISALoops

/-! # Protected words through a singleton row on arbitrary routed input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open Cube Cube.Physical.Owned Cube.Scatter VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM Owned CellDispatch

/-- In a returning singleton row, only accepted families can write and each writes in its
real ordered-pair interval. All protected source words and low loop controls survive, even
if a crossing word read by the scatter is an arbitrary machine word. -/
theorem singleLoop_raw_frame {w n d len : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (D : SingleRowData n d len) (src : Set ℕ) (orig : Bank w) (old : Memory w)
    (ready : singleReady D.axis D.left D.right 0 (.ofWords orig old)) (width : readings orig 21 = len)
    (frameZ : (pub 0).val+56 ∈ src) (frameBank : (pub 0).val+88 ∈ src)
    (zAt : readings old ((pub 0).val+56) = d^(n+1)) (bankAt : readings old ((pub 0).val+88) = D.bank)
    (room : SingleRoom w n d len (pub 0).val D.bank)
    (protect : ∀ k : Fin (singlePairTrials n d), D.selected k → ∀ x ∈ src, x < D.address k ∨ D.address k+len ≤ x)
    {es t mt} (path : Runs pub mac (rowLoop (singleCandidate n) scatterSingle) orig old es t mt) :
    (∀ j : Reg, j.val < 24 → j ≠ 18 → t j = orig j) ∧ (∀ x ∈ src, mt x = old x) ∧ t 36 = orig 36 := by
  let I (r : Bank w) (m : Memory w) := (∀ j : Reg, j.val < 24 → j ≠ 18 → r j = orig j) ∧
    ∀ x ∈ src, m x = old x
  let body := Code.seq (singleCandidate n) (.seq (.ifEq 40 1 scatterSingle .nop) (.binary .add 18 18 1))
  have step {r : Bank w} {m : Memory w} {gs u mu} (inv : I r m) (lt : r 18 < r 19)
      (run : Runs pub mac body r m gs u mu) : I u mu := by
    obtain ⟨r0,r1,r10,r11,r12,r14,r15,_,r19⟩ := ready
    have low (j : Reg) (hj : j.val < 24) (hn : j ≠ 18) := congrArg Fin.val (inv.1 j hj hn)
    let k : Fin (singlePairTrials n d) := ⟨readings r 18, by
      have h19 : readings r 19 = singlePairTrials n d := (low _ (by decide) (by decide)).trans r19
      exact h19 ▸ lt⟩
    obtain ⟨_,v,mv,_,_,candidate,tail⟩ := seq_split run
    obtain ⟨_,y,my,_,_,branch,inc⟩ := seq_split tail
    obtain ⟨fu,fv,key,dst⟩ := D.fits k room.keys room.allocation
    have prepared := (singleCandidate_run pub mac r m D.axis D.left D.right k
      ((low 0 (by decide) (by decide)).trans r0) ((low 1 (by decide) (by decide)).trans r1)
      ((low 10 (by decide) (by decide)).trans r10) ((low 11 (by decide) (by decide)).trans r11)
      ((low 12 (by decide) (by decide)).trans r12) ((low 14 (by decide) (by decide)).trans r14)
      ((low 15 (by decide) (by decide)).trans r15) rfl fu fv).asTest (singleCandidate_deterministic n)
    obtain ⟨lcode,rcode,flag,preserve,sameMem⟩ := (prepared.sound candidate).2
    have v1 : readings v 1 = 1 := (preserve _ (by decide)).trans ((low _ (by decide) (by decide)).trans r1)
    have v21 : readings v 21 = len := (preserve _ (by decide)).trans ((low _ (by decide) (by decide)).trans width)
    have mb (x : ℕ) (hx : x ∈ src) : mv x = old x :=
      (Fin.ext (congrFun sameMem x)).trans (inv.2 x hx)
    have lowY (j : Reg) (hj : j.val < 24) : y j = v j :=
      branch.keepsReg ((by decide : ∀ j : Reg, j.val < 24 → (Code.ifEq 40 1 scatterSingle .nop).keeps j = true) j hj)
    have lowU (j : Reg) (hj : j.val < 24) (hn : j ≠ 18) : u j = orig j :=
      (inc.keepsReg (by simp [Code.keeps,hn])).trans ((lowY j hj).trans ((Fin.ext (preserve j hj)).trans (inv.1 j hj hn)))
    have im : mu = my := by
      have bump : Runs pub mac (.binary .add 18 18 1) y my [tick w] (Function.update y 18 (y 18+y 1)) my :=
        Runs.localStep _ rfl rfl
      exact (inc.unique_of_deterministic (by decide) bump).2.2
    obtain ⟨_,_,chosen⟩ := eq_split branch
    refine ⟨lowU,fun x hx => im ▸ ?_⟩
    by_cases passed : v 40 = v 1
    · rw [ite_eq_left passed] at chosen
      have ok : D.selected k := by
        by_contra wrong
        have wrong' : ¬ singleTrialValid D.axis D.left D.right k := wrong
        have h40 : readings v 40 = 0 := by simpa only [NatState.ofWords,ite_eq_right wrong'] using flag
        have eqn : readings v 40 = readings v 1 := congrArg Fin.val passed
        omega
      have oldZ := (congrArg Fin.val (mb _ frameZ)).trans zAt
      have oldB := (congrArg Fin.val (mb _ frameBank)).trans bankAt
      exact (scatterSingle_raw_outside D.bank (d^(n+1)) len (D.codes k).1 (D.codes k).2
        lcode rcode v21 oldZ oldB room.frameFit key dst chosen x (protect k ok x hx)).trans (mb x hx)
    · rw [ite_eq_right passed] at chosen
      have nop : Runs pub mac .nop v mv [tick w] v mv := Runs.localStep _ rfl rfl
      exact (congrFun (chosen.unique_of_deterministic (by decide) nop).2.2 x).trans (mb x hx)
  have result := (path.while_invariant 18 19 body I step rfl ⟨fun _ _ _ => rfl,fun _ _ => rfl⟩).1
  have k36 := (singleCandidate_frame n).2.1
  have kept : (rowLoop (singleCandidate n) scatterSingle).keeps 36 = true := by
    change ((singleCandidate n).keeps 36 && true) = true
    simpa only [Bool.and_true] using k36
  exact ⟨result.1,result.2,path.keepsReg kept⟩

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
