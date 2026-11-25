import OAI.Computability.BorderVNP.RoutingISATypedTaskGather
import OAI.Computability.BorderVNP.RoutingISATypedTaskMemory

/-! # Native memory stores and the ownership branch of one cell task -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

open VPVNP.BurstRAM Packing.Directory.ISA

private theorem pushEval (rs : List Reg) (pub : Arg → ℕ) (z : NatState) (a : ℕ)
    (one : z.reg 1=1) (ptr : z.reg 20=a) (apart : ∀ r ∈ rs, r ≠ 20) :
    (pushWords rs).fixedEval pub z =
      ⟨Function.update z.reg 20 (a+rs.length),putNat z.mem a (rs.map z.reg)⟩ := by
  induction rs generalizing a z with
  | nil =>
    simp only [pushWords,Code.fixedEval,Code.evalNat,List.length_nil,Nat.add_zero,List.map_nil,putNat,← ptr,
      Function.update_eq_self]
  | cons r rs ih =>
    let z' : NatState := ⟨Function.update z.reg 20 (a+1),Function.update z.mem a (z.reg r)⟩
    have hmap : rs.map z'.reg = rs.map z.reg := by
      apply List.map_congr_left
      intro v hv
      exact Function.update_of_ne (apart v (List.mem_cons_of_mem r hv)) ..
    have h := ih z' (a+1) (by simp [z',one]) (by simp [z'])
      (fun v hv => apart v (List.mem_cons_of_mem _ hv))
    rw [hmap] at h
    simp only [pushWords,Code.fixedEval,Code.evalNat,addressOp,one,ptr,List.length_cons,List.map_cons,putNat]
    simpa only [z',Function.update_idem,Nat.add_right_comm a 1 rs.length,Nat.add_assoc] using h

private theorem pushSafe (rs : List Reg) (pub : Arg → ℕ) (z : NatState) (w : ℕ)
    (one : z.reg 1=1) (room : z.reg 20+rs.length < 2^w) : (pushWords rs).fixedSafe w pub z := by
  induction rs generalizing z with
  | nil => trivial
  | cons r rs ih =>
    let z' : NatState := ⟨Function.update z.reg 20 (z.reg 20+1),Function.update z.mem (z.reg 20) (z.reg r)⟩
    have h := ih z' (by simp [z',one]) (by simpa [z',Nat.add_assoc,Nat.add_comm 1] using room)
    simp only [pushWords,Code.fixedSafe,Code.safeReadOnly,Code.fixedEval,Code.evalNat,addressOp,addressOpFits,one,true_and]
    exact ⟨by simp only [List.length_cons] at room; omega,h⟩

private theorem ready_update (l : Layout) (i j k : ℕ) (z : NatState) (hr : l.Ready i j z)
    (out : NatState) (ht : ∀ r : Reg, r.val < 20 → r ≠ 18 → r ≠ 19 → out.reg r=z.reg r)
    (hi : out.reg 18=i+1) (hj : out.reg 19=k) : l.Ready (i+1) k out := by
  intro r hh
  by_cases a : r=18
  · subst r
    exact hi
  by_cases b : r=19
  · subst r
    exact hj
  rw [ht r hh a b,hr r hh]
  rcases r with ⟨r,rr⟩
  change r < 20 at hh
  interval_cases r <;> first | rfl | contradiction

private abbrev seven : List Reg := [24,25,26,27,28,29,30]

private def writeOwner (l : Layout) (original : ℕ → ℕ) (i : ℕ) (z : NatState) : NatState :=
  ⟨z.reg,Function.update z.mem (l.call i) (l.owner original i)⟩

private def afterEmit (l : Layout) (original : ℕ → ℕ) (i j : ℕ) (z : NatState) : NatState :=
  let a := l.tasks+7*j
  ⟨Function.update (Function.update z.reg 20 (a+7)) 19 (j+1),putNat z.mem a (l.row original i)⟩

private theorem emit_eval (l : Layout) (original : ℕ → ℕ) (pub : Arg → ℕ)
    (i j : ℕ) (z : NatState) (h : l.Gathered original i j z) (own : l.owner original i=l.team) :
    emit.fixedEval pub z = afterEmit l original i j z := by
  have one : z.reg 1=1 := h.ready 1 (by decide)
  have cursor : z.reg 19=j := h.ready 19 (by decide)
  have push := pushEval seven pub z (l.tasks+7*j) one h.next (by decide)
  rw [show seven.map z.reg = l.row original i from h.fields own] at push
  change (Code.binary .add 19 19 1).fixedEval pub ((pushWords seven).fixedEval pub z) = _
  rw [push]
  simp (config := {decide:=true}) [Code.fixedEval,Code.evalNat,addressOp,afterEmit,seven,one,cursor]

private theorem emit_safe {w : ℕ} (l : Layout) (original : ℕ → ℕ) (pub : Arg → ℕ)
    (i j : ℕ) (z : NatState) (h : l.Gathered original i j z) (fit : l.tasks+7*j+7 < 2^w) :
    emit.fixedSafe w pub z := by
  have one : z.reg 1=1 := h.ready 1 (by decide)
  have cursor : z.reg 19=j := h.ready 19 (by decide)
  have push := pushEval seven pub z (l.tasks+7*j) one h.next (by decide)
  change (pushWords seven).fixedSafe w pub z ∧
    (Code.binary .add 19 19 1).fixedSafe w pub ((pushWords seven).fixedEval pub z)
  refine ⟨pushSafe seven pub z w one (by change z.reg 20+7 < _; rwa [h.next]),?_⟩
  rw [push]
  simp (config := {decide:=true}) [Code.fixedSafe,Code.safeReadOnly,addressOpFits,one,cursor]
  omega

private theorem commit_effect {w : ℕ} (l : Layout) (original : ℕ → ℕ) (room : l.Room original w)
    (pub : Arg → ℕ) (i : ℕ) (hi : i < l.cells) (z : NatState)
    (hg : l.Gathered original i (l.before original i) z) (hm : z.mem=l.image original i) :
    commitRow.fixedSafe w pub z ∧
    l.Ready (i+1) (l.before original (i+1)) (commitRow.fixedEval pub z) ∧
    (commitRow.fixedEval pub z).mem=l.image original (i+1) := by
  let j := l.before original i
  let u := writeOwner l original i z
  have hu : (Code.store 30 21).fixedEval pub z = u := by simp only [Code.fixedEval,hg.call,hg.owner,u,writeOwner]
  have gu : l.Gathered original i j u := ⟨hg.ready,hg.next,hg.owner,hg.fields,hg.call⟩
  let branch : Code := .ifEq 21 4 emit .nop
  let v := branch.fixedEval pub u
  have own : u.reg 21=l.owner original i := hg.owner
  have team : u.reg 4=l.team := hg.ready 4 (by decide)
  have idx : u.reg 18=i := hg.ready 18 (by decide)
  have cur : u.reg 19=j := hg.ready 19 (by decide)
  have one : u.reg 1=1 := hg.ready 1 (by decide)
  have ev : v = if l.owner original i=l.team then afterEmit l original i j u else u := by
    change (if u.reg 21=u.reg 4 then emit.fixedEval pub u else (Code.nop.fixedEval pub u)) = _
    rw [own,team]
    split
    · exact emit_eval l original pub i j u gu (by assumption)
    · rfl
  have hj := l.before_le original i
  have fits : l.tasks+7*j+7 < 2^w := by change l.tasks+7*l.before original i+7 < _; have := room.tasks; omega
  have sb : branch.fixedSafe w pub u := by
    change (if u.reg 21=u.reg 4 then emit.fixedSafe w pub u else Code.nop.fixedSafe w pub u)
    rw [own,team]; split
    · exact emit_safe l original pub i j u gu fits
    · trivial
  have keep (r : Reg) (h19 : r ≠ 19) (h20 : r ≠ 20) : v.reg r=u.reg r := by
    rw [ev]
    split <;> simp [afterEmit,h19,h20]
  have idx' := (keep 18 (by decide) (by decide)).trans idx
  have one' := (keep 1 (by decide) (by decide)).trans one
  have last : v.reg 19=l.before original (i+1) := by
    rw [ev,Layout.before]
    split <;> simp [afterEmit,cur,j]
  have mv : v.mem=l.image original (i+1) := by
    rw [ev,Layout.image]
    split <;> simp [afterEmit,u,writeOwner,hm,j]
  have fin : commitRow.fixedEval pub z = ⟨Function.update v.reg 18 (i+1),v.mem⟩ := by
    change (Code.binary .add 18 18 1).fixedEval pub
      (branch.fixedEval pub ((Code.store 30 21).fixedEval pub z)) = _
    rw [hu]
    change (Code.binary .add 18 18 1).fixedEval pub v = _
    simp only [Code.fixedEval,Code.evalNat,addressOp,idx',one']
  have safe : commitRow.fixedSafe w pub z := by
    change True ∧ branch.fixedSafe w pub ((Code.store 30 21).fixedEval pub z) ∧
      (Code.binary .add 18 18 1).fixedSafe w pub (branch.fixedEval pub ((Code.store 30 21).fixedEval pub z))
    rw [hu]
    refine ⟨trivial,sb,?_⟩
    change v.reg 18 + v.reg 1 < 2^w
    rw [idx',one']; have := room.calls; omega
  rw [fin]
  refine ⟨safe,ready_update l i j _ u gu.ready _ ?_ ?_ ?_,mv⟩
  · intro r rr h18 h19
    have h20 : r ≠ 20 := fun e => by subst r; exact (by decide : ¬ (20 : Reg).val < 20) rr
    exact (Function.update_of_ne h18 ..).trans (keep r h19 h20)
  · change Function.update v.reg (18 : Reg) (i+1) 18 = i+1
    simp
  · change Function.update v.reg (18 : Reg) (i+1) 19 = l.before original (i+1)
    rw [Function.update_of_ne (by decide : (19 : Reg) ≠ 18)]
    exact last

/-- One actual iteration writes the public owner and conditionally adds one typed task.
Only source addresses of the current cell need to agree with the original memory. -/
theorem body_step {w : ℕ} (l : Layout) (original : ℕ → ℕ) (room : l.Room original w)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (i : ℕ) (hi : i < l.cells) (s : Bank w) (m : Memory w)
    (hr : l.Ready i (l.before original i) (.ofWords s m)) (hm : readings m = l.image original i) :
    BoundedRun pub mac body s m body.slots (fun z =>
      l.Ready (i+1) (l.before original (i+1)) z ∧ z.mem=l.image original (i+1)) := by
  let j := l.before original i
  let z := NatState.ofWords s m
  have hs : l.Reads original z.mem i := by
    intro a ha; change readings m a=original a
    rw [hm]; exact l.image_input original room hi.le hi ha
  have safe := gather_safe l original room (readings pub) i j z hi (l.before_le original i) hr hs
  have first := (gather.runFixed pub mac s m safe).mono le_rfl (fun out eqn => eqn ▸
    gather_eval l original (readings pub) i j z hr hs)
  apply first.seq
  rintro t mt ⟨hg,hmem⟩
  have h := commit_effect l original room (readings pub) i hi (.ofWords t mt) hg (hmem.trans hm)
  exact (commitRow.runFixed pub mac t mt h.1).mono le_rfl (fun out eqn => eqn ▸ h.2)

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
