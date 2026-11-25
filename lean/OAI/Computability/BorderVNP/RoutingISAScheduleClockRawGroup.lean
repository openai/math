import OAI.Computability.BorderVNP.RoutingISAScheduleClockRawRows
import OAI.Computability.BorderVNP.RoutingISAScheduleClockRowFold
import OAI.Computability.BorderVNP.CubeTeamOwnedReplaySetup

/-! # The native owned-group clock on one processor's actual receiving intervals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open BorderVNP.Cube BorderVNP.Cube.Tally Physical Physical.Owned Scatter Padding.Banks
open TeamRows TeamRowSources TeamRowClock RoutingISA.CubeArena RoutingISA.OwnedStages VPVNP.BurstRAM
open private diagonalRoleReturn from OAI.Computability.BorderVNP.CubeTeamRawArenaRoles

variable {a : CubeArena.Layout} {w frame team : ℕ} {decl : LengthDeclaration a.n a.header.d} {copies : 1 ≤ a.K}
variable {owner : Fin a.header.d → ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {original m mt : Memory w} {r t : Bank w} {es : List (TeamRAM.Event w)}

set_option maxHeartbeats 1600000

/-- Measure the callback selected by the genuine quotient and remainder,
including its stores and the three cursor values required by the row induction. -/
theorem rawVisit_measured (P : a.RawInputs frame team decl copies owner pub original)
    (views : LocalReceived a frame team decl owner original) (q : Fin (a.header.d*a.header.d)) :
    let l := a.scanner frame team decl.1.val a.rowSelectorBits
    let src := source l a.powerBase a.n
    wordOwner owner (q.val/l.d) = team → (∀ x ∈ src, m x = original x) →
    readings r 7 = a.vertexBase+3*vertexPrefix l (wordOwner owner) a.n a.header.blocks q.val →
    TeamRowPrepare.ReadyRow l (readings m) q.val (.ofWords r m) →
    Runs pub mac (if q.val/l.d = q.val%l.d then diagonalRole a.n a.b a.h a.K a.s else strictRole a.n a.b a.h a.K a.s) r m es t mt →
    traceCost es ≤ physicalCostAt l a.header.blocks a.b a.h a.K a.s decl.1 q.val ∧
      (∀ x ∈ src, mt x = m x) ∧ readings t 7 = readings r 7+(if q.val/l.d = q.val%l.d then 0 else 3*strictVertices a.n l.d a.header.blocks) ∧
      readings t 22 = q.val ∧ readings t 23 = l.d*l.d := by
  intro l src owned same cursor prep run
  let v := pairAt a.header.d q
  have keyAt : key v = q.val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply q)
  have digits := key_digits v
  rw [keyAt] at digits
  change wordOwner owner (q.val/a.header.d) = team at owned
  have owns : owner v.1 = team := by simpa only [digits.1,wordOwner,dite_eq_left v.1.isLt] using owned
  have equal : q.val/l.d = q.val%l.d ↔ v.1 = v.2 := by
    change q.val/a.header.d = q.val%a.header.d ↔ _
    rw [digits.1,digits.2]
    exact ⟨Fin.ext,congrArg Fin.val⟩
  rw [physicalCostAt_pair l a.header.blocks a.b a.h a.K a.s decl.1 q]
  change traceCost es ≤ physicalRoleTicks a.header.blocks a.b a.h a.K a.s decl.1 v.1 v.2 ∧ _
  have strict (p : Symbols a.header.d) (high : Bool) (order : oriented p high = v) (different : v.1 ≠ v.2) :
      traceCost es ≤ physicalRoleTicks a.header.blocks a.b a.h a.K a.s decl.1 v.1 v.2 ∧
        (∀ x ∈ src, mt x = m x) ∧ readings t 7 = readings r 7+3*strictVertices a.n l.d a.header.blocks ∧
        readings t 22 = q.val ∧ readings t 23 = l.d*l.d := by
    have ho := order.symm ▸ owns
    have k : key (oriented p high) = q.val := (congrArg key order).trans keyAt
    have path := (ite_eq_right (different ∘ equal.mp)) ▸ run
    obtain ⟨cost,keep,endAt,next,limit⟩ := rawStrictRole_measured P views p high ho same (k.symm ▸ cursor) (k.symm ▸ prep) path
    rw [order] at cost
    exact ⟨cost,keep,endAt,next.trans k,limit⟩
  rcases lt_trichotomy v.1 v.2 with lo | eq | hi
  · rw [ite_eq_right (lo.ne ∘ equal.mp)]
    exact strict ⟨v,lo⟩ false rfl lo.ne
  · simp only [ite_eq_left (equal.mpr eq),Nat.add_zero]
    have k : key (v.1,v.1) = q.val := by rw [eq,show (v.2,v.2) = v from Prod.ext eq.symm rfl]; exact keyAt
    have path := (ite_eq_left (equal.mpr eq)) ▸ run
    have cost := rawDiagonalRole_cost P v.1 same (k.symm ▸ prep) path
    obtain ⟨keep,endAt,next,limit⟩ := diagonalRoleReturn P v.1 same (k.symm ▸ prep) path
    exact ⟨by rwa [← eq],keep,endAt,next.trans k,limit⟩
  · rw [ite_eq_right (hi.ne' ∘ equal.mp)]
    exact strict ⟨v.swap,hi⟩ true rfl hi.ne'

/-- Every returning native traversal at this team fits its schedule's allowance,
even when other teams' packet selectors, row claims, or histories are invalid. -/
theorem rawOwnedGroups_traceCost (P : a.RawInputs frame team decl copies owner pub original)
    (views : LocalReceived a frame team decl owner original)
    (run : Runs pub mac (ownedGroups a.n a.b a.h a.K a.s) r original es t mt) :
    let l := a.scanner frame team decl.1.val a.rowSelectorBits
    traceCost es ≤ 4+(TeamRows.ticks l (wordOwner owner) (physicalCostAt l a.header.blocks a.b a.h a.K a.s decl.1)+11) := by
  intro l
  let old (m : Memory w) := ∀ x ∈ source l a.powerBase a.n, m x = original x
  let I (q : ℕ) (v : Word w) (m : Memory w) :=
    old m ∧ v.val = a.vertexBase+3*vertexPrefix l (wordOwner owner) a.n a.header.blocks q
  have inv (m : Memory w) (same : old m) :=
    source_inventory (l := l) P.fields P.directory P.owners same
  have visit (q : ℕ) (hq : q < l.d*l.d)
      (owned : wordOwner owner (q/l.d) = l.teamID) (u : Bank w) (mu : Memory w) (same : old mu)
      (cursor : readings u 7 = a.vertexBase+3*vertexPrefix l (wordOwner owner) a.n a.header.blocks q)
      (prep : TeamRowPrepare.ReadyRow l (readings mu) q (.ofWords u mu)) (ys v mv)
      (path : Runs pub mac (if q/l.d=q%l.d then diagonalRole a.n a.b a.h a.K a.s else strictRole a.n a.b a.h a.K a.s) u mu ys v mv) :=
    rawVisit_measured P views ⟨q,hq⟩ owned same cursor prep path
  obtain ⟨H,zero,_⟩ := ownedGroups_return_induction a.n a.header.blocks a.b a.h a.K a.s l (wordOwner owner)
    (fun _ => old) a.vertexBase P.fits P.seed.frame (fun _ _ => rfl) (fun _ => inv) (fun _ _ _ _ same => same)
    (fun q hq owned u mu same cursor prep ys v mv path => by
      obtain ⟨_,keep,ret⟩ := visit q hq owned u mu same cursor prep ys v mv path
      exact ⟨fun x hx => (keep x hx).trans (same x hx),ret⟩) run
  apply ownedHistory_traceCost (wordOwner owner) (physicalCostAt l a.header.blocks a.b a.h a.K a.s decl.1) H I
  · exact ⟨fun _ _ => rfl,by simpa only [vertexPrefix,Finset.range_zero,Finset.sum_empty,Nat.mul_zero,Nat.add_zero,readings] using zero⟩
  · intro j _ k mem h miss
    exact ⟨h.1,by simpa only [vertexPrefix,Finset.sum_range_succ,miss,false_and,ite_false,Nat.add_zero] using h.2⟩
  · intro j hj k mem h
    exact (inv mem h.1).2.2 _ (pairAt l.d ⟨j,hj⟩).1.isLt
  · intro j hj u mu ys v mv h owned prep path
    obtain ⟨cost,keep,out,_⟩ := visit j hj owned u mu h.1 h.2 prep ys v mv path
    refine ⟨cost,fun x hx => (keep x hx).trans (h.1 x hx),?_⟩
    change readings v 7 = _
    have cur : readings u 7 = _ := h.2
    change readings v 7 = readings u 7+(if j/l.d=j%l.d then 0 else 3*strictVertices a.n l.d a.header.blocks) at out
    rw [out,cur]
    by_cases eqn : j/l.d=j%l.d <;> simp [vertexPrefix,Finset.sum_range_succ,owned,eqn,Nat.mul_add,Nat.add_assoc]

/-- Raw words on the incident sides and an installed finite arena suffice for
the measured physical row clock. The lengths are needed only at owned sides. -/
theorem rawOwnedGroups_of_words (a : CubeArena.Layout) (frame team : ℕ) (decl : LengthDeclaration a.n a.header.d)
    (copies : 1 ≤ a.K) (owner : Fin a.header.d → ℕ) (room : a.ReplayRoom w frame)
    (words : a.ScannerWords frame team decl.1.val owner (readings pub) (readings original) decl.2)
    (views : LocalReceived a frame team decl owner original)
    (run : Runs pub mac (ownedGroups a.n a.b a.h a.K a.s) r original es t mt) :
    let l := a.scanner frame team decl.1.val a.rowSelectorBits
    traceCost es ≤ 4+(TeamRows.ticks l (wordOwner owner) (physicalCostAt l a.header.blocks a.b a.h a.K a.s decl.1)+11) :=
  rawOwnedGroups_traceCost (a.rawInputs_of_words frame team decl copies owner pub original
    room.axes room.alphabet room.payload room.positive room.primary room.stopFit room.fixedFit room.capFit words) views run

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
