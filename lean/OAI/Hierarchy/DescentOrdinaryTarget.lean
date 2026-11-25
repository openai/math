import OAI.Hierarchy.DescentOrdinaryDestRAM
import OAI.Hierarchy.DescentGadgetNetwork

namespace OAI
/-! # The destination of every surviving old cable is computed from the actual chosen demand -/

namespace Hierarchy.DescentOrdinaryDestRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentSixParty GadgetNetwork Computability.BorderVNP.Crossing
open scoped Fin.CommRing Classical
noncomputable section
variable {D w n : ℕ} {P : Type} {bits : P→ℕ} (N : Network D P bits) (S : Banks)
variable (pick : Fin n×Fin 2↪N.Edge) (edge : N.Edge↪Fin S.dest.size)
variable (oldSite : N.Site→ℕ) (role : Fin n×Fin 6→ℕ)
local notation "id" => fun (s : Fin 2) (i : Fin n)=>edge (pick (i,s))
local notation "birth" => fun (s : Fin 2) (i : Fin n)=>role (i,demandSrc s)

/-- Parent records are initialized from the old destination directory before each of the two
sparse native overwrites. Input and destination arrays occupy separate native intervals. -/
structure Input (m : Memory w) : Prop where
  fields : ∀s,S.Records s (id s) (birth s) m
  old : ∀e,m (S.dest.base+(edge e).val)=oldSite (N.dst e)
  pairBefore : S.pairs.base+S.pairs.size≤S.dest.base
  birthBefore : S.births.base+S.births.size≤S.dest.base

def endMem (m : Memory w) :=
  S.after (1:Fin 2) (id 1) (birth 1) (S.after (0:Fin 2) (id 0) (birth 0) m)

theorem authentic_target {m : Memory w} (room : S.Room w n) (data : Input N S pick edge oldSite role m) :
    ((S.pass w n 0).seq (S.pass w n 1)).Exec m (endMem N S pick edge role m)
      (ProtocolRAMGeneratedWrite.work n (S.pointer 0) (S.value 0)+
       ProtocolRAMGeneratedWrite.work n (S.pointer 1) (S.value 1)) ∧
    ∀e : N.Edge,endMem N S pick edge role m (S.dest.base+(edge e).val)=
      (Sum.elim oldSite role (target N pick (.inl e)):ℕ) := by
  have inj (s : Fin 2) : Function.Injective (id s) := fun i j h=>congrArg Prod.fst (pick.injective (edge.injective h))
  let mid:=S.after (0:Fin 2) (id 0) (birth 0) m
  have oldMem (u : ℕ) (lo : u<S.dest.base) : mid u=m u := by
    apply frame
    · intro i; omega
    · have :=room.dest.2.2; omega
    · exact room
  have next : S.Records (1:Fin 2) (id 1) (birth 1) mid := by
    constructor
    · intro i
      rw [oldMem _ (by have := i.isLt; have :=room.np; have :=data.pairBefore; change _+(9*_+2)<_; omega)]
      exact (data.fields 1).edgeField i
    · intro i
      rw [oldMem _ (by have := i.isLt; have :=room.nb; have :=data.birthBefore; change _+(6*_+2)<_; omega)]
      exact (data.fields 1).siteField i
  constructor
  · exact Procedure.Exec.then (intermediate S 0 room _ _ m (data.fields 0))
      (intermediate S 1 room _ _ mid next)
  · intro e
    have low : S.dest.base+(edge e).val<S.outAddress := by have := (edge e).isLt; have :=room.dest.2.2; omega
    cases h : selected N pick e with
    | none =>
      have away (s : Fin 2) (i : Fin n) : S.dest.base+(edge e).val≠S.dest.base+(id s i).val := by
        intro eqn
        have eqE:=edge.injective (Fin.ext (Nat.add_left_cancel eqn))
        rw [eqE,selected_pick] at h
        contradiction
      change S.after _ _ _ mid _=_
      rw [frame _ _ _ _ _ _ (away 1) low room,show mid _=m _ from frame _ _ _ _ _ _ (away 0) low room,
        data.old]
      simp [target,h]
    | some t =>
      have eqE:=selected_spec N pick h
      subst e
      rcases t with ⟨i,s⟩
      have dest : target N pick (.inl (pick (i,s))) = .inr (i,demandSrc s) := by
        simp [target]
      rw [dest]
      fin_cases s
      · have skip (j : Fin n) : S.dest.base+(id 0 i).val≠S.dest.base+(id 1 j).val := by
          intro eqn
          have pairEq:=pick.injective (edge.injective (Fin.ext (Nat.add_left_cancel eqn)))
          exact (by decide : (0:Fin 2)≠1) (congrArg Prod.snd pairEq)
        exact (frame S 1 (id 1) (birth 1) mid (S.dest.base+(id 0 i).val) skip low room).trans
          (read S 0 (id 0) (inj 0) (birth 0) m i)
      · exact read S 1 (id 1) (inj 1) (birth 1) mid i

end
end Hierarchy.DescentOrdinaryDestRAM

end OAI
