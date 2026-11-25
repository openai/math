import OAI.Hierarchy.DescentDatedNamedBlock
import OAI.Hierarchy.DescentOrdinarySignedEmission

namespace OAI
/-! The actual named operand and the observed signed emitter select precisely
the same next-stage grain. Its within-cable ordinal distinguishes an uncut cable. -/
namespace Hierarchy.DescentOrdinarySiblingSerial
open DescentPackedOperand DescentSIMDLookup
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
open private physicalBase physicalKey from OAI.Hierarchy.DescentOrdinarySiblingSerial

variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪DescentHostDirectory.Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {age i : ℕ} {price ε : ℝ}
variable (A : GroupStage (PhysicalRename.rankedWorld
  (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
  (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site)) G price ε J V age)
local notation "baseWorld" => physicalBase W G pick z hz fit pack p key flag k g q old picked affected
local notation "edgeKey" => physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site
local notation "rep" => repetitions W G pick z hz fit pack p key flag k g q

local notation "coarse" => coalesced (W.selected G pick z hz fit pack p) key flag k g
local notation "ls" => rename site
local notation "le'" => rename edgeKey
local notation "nextWorld" => PhysicalRename.rankedWorld baseWorld site edgeKey
open DescentKernelHistory DescentBundleHistory DescentOperandStateBanks
local notation "cut₀" => repetition_width W G pick z hz fit pack p key flag k g q old picked affected
variable {R unit : ℕ} {recipe : BitDescription (coalesced (W.selected G pick z hz fit pack p) key flag k g)}
variable (hp : 0<unit) (sh : WorldShape unit R recipe) (hq : 0<q) (dvd : unit∣q)
local notation "pre" => sh.pieces rep q cut₀ hp hq dvd
local notation "mapped" => SiteBooks.trans hp (SiteBooks.rename hp pre ls le')
  (SiteBooks.split hp sh rep q cut₀ hq dvd)

open DescentOrdinaryParentBlocks DescentOrdinaryWindowFields
local notation "B₀" => blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A hq
local notation "wt₀" => weight W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
local notation "issue" => signedEmission W G edge pair pick z hz fit pack p key flag k g q old picked affected site A hq

open private Mount.naming Mount.single from OAI.Hierarchy.DescentOrdinaryParentBlocks

private theorem markedEmissionEdge {E Z : Type} (marked : E → Prop) [DecidablePred marked] (copies : E → ℕ)
    (name : Fibers.Raw marked copies ≃ Z) (count : Z → ℕ)
    (one : ∀ (u : {u : E // marked u}) (j : Fin (copies u.val)), count (name (.inr ⟨u,j⟩)) = 1)
    (u : E) (mark : marked u) (j : Fin (Fibers.weight marked copies name count u)) (m : Fin (copies u))
    (index : j.val = m.val) :
    (Fibers.emit marked copies name count one ⟨u,j⟩).1 = name (.inr ⟨⟨u,mark⟩,m⟩) := by
  let i := Fibers.copyIndex marked copies name count u mark j
  have same : i = m := Fin.ext index
  exact (congrArg Sigma.fst (Fibers.emit_marked marked copies name count one u mark j)).trans
    (congrArg (fun t => name (.inr ⟨⟨u,mark⟩,t⟩)) same)

private theorem freeEmissionEdge {E Z : Type} (marked : E → Prop) [DecidablePred marked] (copies : E → ℕ)
    (name : Fibers.Raw marked copies ≃ Z) (count : Z → ℕ)
    (one : ∀ (u : {u : E // marked u}) (j : Fin (copies u.val)), count (name (.inr ⟨u,j⟩)) = 1)
    (u : E) (outer : ¬marked u) (j : Fin (Fibers.weight marked copies name count u)) :
    (Fibers.emit marked copies name count one ⟨u,j⟩).1 = name (.inl ⟨u,outer⟩) :=
  congrArg Sigma.fst (Fibers.emit_free marked copies name count one u outer j)

/-- The emitted edge and lane read from a surviving public block. -/
def emittedOperandNumber {Q : Type} (root : (coarse).graph.Edge) (chunk : ℕ)
    (observed : Q → Prop) (number : Q → Option ((nextWorld).graph.Edge × ℕ)) : Prop :=
  ∃ word : Q, ∃ child : Fin ((B₀).count root),
    observed word ∧ child.val = chunk / (q/unit) ∧
      let sent := (issue).units ⟨root,child⟩
      number word = some (sent.1,if root ∈ (coarse).core then chunk % (q/unit) else chunk) ∧
      sent.2.val = (if root ∈ (coarse).core then 0 else child.val)

include hp dvd in
theorem emittedNumber_of_publicBlock {Q : Type} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (tickSize : A.z*G.b=q) (root : (coarse).graph.Edge) (chunk : ℕ) (fits : (chunk+1)*unit ≤ (coarse).graph.width root)
    (observed : Q → Prop) (number : Q → Option ((nextWorld).graph.Edge × ℕ))
    (recorded : ∃ word : Q, observed word ∧ (if core : root ∈ (coarse).core then
      ∃ m : Fin (rep root), m.val = chunk/(q/unit) ∧ number word = some ((le') (.inr ⟨⟨root,core⟩,m⟩),chunk%(q/unit))
      else number word = some ((le') (.inl ⟨root,core⟩),chunk))) :
    emittedOperandNumber W G edge pair pick z hz fit pack p key flag k g q old picked affected site A hq (unit:=unit)
      root chunk observed number := by
  obtain ⟨word,hit,address⟩ := recorded
  have size:=weight_width W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
    S ready tickSize root
  have scale : (q/unit)*unit=q := Nat.div_mul_cancel dvd
  have positive : 0 < q/unit := Nat.div_pos (Nat.le_of_dvd hq dvd) hp
  have bound : chunk+1≤wt₀ root*(q/unit) := by
    apply Nat.le_of_mul_le_mul_right ?_ hp
    rw [Nat.mul_assoc,scale,size]
    exact fits
  let j : Fin ((B₀).count root):=⟨chunk/(q/unit),(Nat.div_lt_iff_lt_mul positive).2 bound⟩
  refine ⟨word,j,hit,rfl,?_,?_⟩
  · change number word=some
      ((emit W G edge pair pick z hz fit pack p key flag k g q old picked affected site A ⟨root,j⟩).1,
          if root∈(coarse).core then chunk%(q/unit) else chunk)
    by_cases core : root∈(coarse).core
    · rw [dite_eq_left core] at address
      obtain ⟨m,idx,whereAt⟩ := address
      rw [ite_eq_left core]
      have same := markedEmissionEdge (fun u : (coarse).graph.Edge => u ∈ (coarse).core) rep
        (Mount.naming coarse q rep cut₀ site edgeKey) A.grainCount (Mount.single coarse q rep cut₀ site edgeKey A)
        root core j m idx.symm
      exact whereAt.trans (congrArg (fun edge => some (edge,chunk%(q/unit))) same.symm)
    · rw [dite_eq_right core] at address
      rw [ite_eq_right core]
      have same := freeEmissionEdge (fun u : (coarse).graph.Edge => u ∈ (coarse).core) rep
        (Mount.naming coarse q rep cut₀ site edgeKey) A.grainCount (Mount.single coarse q rep cut₀ site edgeKey A)
        root core j
      exact address.trans (congrArg (fun edge => some (edge,chunk)) same.symm)
  · exact within_at W G edge pair pick z hz fit pack p key flag k g q old picked affected site A root j


theorem emitted_public_block (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (tickSize : A.z*G.b=q) (v : (coarse).graph.Site) (e : Incident (coarse).graph ((ls).symm v))
    (chunk : ℕ) (fits : (chunk+1)*unit≤(coarse).graph.width e.val) :
    let word:=((mapped).atSite v).publicWord ⟨.inl e,chunk,fits⟩
    ∃j : Fin ((B₀).count e.val), j.val=chunk/(q/unit) ∧
      let sent:=(issue).units ⟨e.val,j⟩
      word.cableNumber (nextWorld).graph v=some (sent.1,if e.val∈(coarse).core then chunk%(q/unit) else chunk) ∧
      sent.2.val=(if e.val∈(coarse).core then 0 else j.val) := by
  intro word
  let number : Unit → Option ((nextWorld).graph.Edge × ℕ) := fun _ => word.cableNumber (nextWorld).graph v
  have recorded : ∃ w : Unit, True ∧ (if core : e.val ∈ (coarse).core then
      ∃ m : Fin (rep e.val), m.val = chunk/(q/unit) ∧ number w = some ((le') (.inr ⟨⟨e.val,core⟩,m⟩),chunk%(q/unit))
      else number w = some ((le') (.inl ⟨e.val,core⟩),chunk)) := by
    refine ⟨(),True.intro,?_⟩
    split
    · rename_i core
      exact named_split_block (W:=coarse) hp sh rep q cut₀ hq dvd ls le' v e chunk fits core
    · rename_i outer
      exact named_unsplit_block (W:=coarse) hp sh rep q cut₀ hq dvd ls le' v e chunk fits outer
  obtain ⟨_,j,_,index,shown⟩ := emittedNumber_of_publicBlock W G edge pair pick z hz fit pack p key flag k g q
    old picked affected site A hp hq dvd S ready tickSize e.val chunk fits (fun _ : Unit => True) number recorded
  exact ⟨j,index,shown⟩

end
end Hierarchy.DescentOrdinarySiblingSerial

end OAI
