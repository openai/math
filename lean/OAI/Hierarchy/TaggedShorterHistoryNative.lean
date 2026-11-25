import OAI.Hierarchy.TaggedShorterHistoryAdvance
import OAI.ThreeFlat.Diagonal.TraceMass

namespace OAI
/-! # Native descriptor writes read back from the combined physical memory -/

noncomputable section
namespace Hierarchy.TaggedShorterHistory
open ThreeFlat Diagonal TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
variable {w p r k : ℕ}

theorem advance_exposed (M : Machine w p r k) {t : ℕ} {c done : Config w p r} {ext out : Memory w}
    {bank : Memory (w+1)} (hm : Matches bank ext c.privateMem)
    (ran : RAM.advance M.program t c ext=some (done,out)) :
    ∃ image, RAM.advance (exposed M) t (snapshot c) bank=some (snapshot done,image) ∧
      Matches image out done.privateMem := by
  induction t generalizing c ext bank with
  | zero =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ran)
    exact ⟨_,rfl,hm⟩
  | succ t ih =>
    simp only [RAM.advance,Machine.program] at ran
    rw [RAM.advance]
    simp only [exposed,snapshot]
    cases hop : M.code c.pc with
    | constant dst v next =>
      rw [hop] at ran
      exact ih (c := c.put next dst v) hm ran
    | publicWord dst j next =>
      rw [hop] at ran
      exact ih (c := c.put next dst (M.publicData j)) hm ran
    | stateWord dst next =>
      rw [hop] at ran
      exact ih (c := c.put next dst c.persistent) hm ran
    | copy dst src next =>
      rw [hop] at ran
      exact ih (c := c.put next dst (c.reg src)) hm ran
    | binary op dst x y next =>
      rw [hop] at ran
      exact ih (c := c.put next dst (op.eval (c.reg x) (c.reg y))) hm ran
    | loadPrivate dst addr next =>
      rw [hop] at ran
      simp only [step,hm.privateWord,narrow_wide]
      exact ih (c := c.put next dst (c.privateMem (c.reg addr))) hm ran
    | storePrivate addr src next =>
      rw [hop] at ran
      exact ih (c := c.store next (c.reg addr) (c.reg src)) (hm.write_private ..) ran
    | jumpEq x y yes no =>
      rw [hop] at ran
      exact ih (c := {c with pc := if c.reg x = c.reg y then yes else no}) hm ran
    | jumpLt x y yes no =>
      rw [hop] at ran
      exact ih (c := {c with pc := if c.reg x < c.reg y then yes else no}) hm ran
    | readExternal dst addr next =>
      rw [hop] at ran
      have hr : bank (wide (c.reg addr)).val = wide (ext (c.reg addr).val) := hm.external _
      simp only [step,hr,narrow_wide]
      exact ih (c := c.put next dst (ext (c.reg addr).val)) hm ran
    | writeExternal addr src next =>
      rw [hop] at ran
      exact ih (c := {c with pc := next}) (hm.write_external ..) ran
    | choose _ _ | accept | reject | returnState _ => simp [hop,Instr.run] at ran

/-- The terminal opcode observed at native exit is the same one checked
by the encoded physical CPU; the extra address bit is zero on its result. -/
theorem finish_exposed (M : Machine w p r k) (c : Config w p r) (result : Option (Word w))
    (h : M.program.step c=.finish result) :
    (exposed M).step (snapshot c)=.finish (result.map wide) := by
  change (M.code c.pc).run M.publicData c=.finish result at h
  change step M.publicData (snapshot c) (M.code c.pc)=_
  cases hop : M.code c.pc <;> simp [Instr.run,hop] at h <;> subst result <;> rfl

/-- Every immutable advice word and emitted descriptor address is read
from the physical combined bank witnessed by that very CPU history. -/
theorem native_history (M : Machine w p r k) {S t fuel d : ℕ} {c done : Config w p r}
    (header : ℕ → Word w) (out : Memory w) (result : Option (Word w))
    (room : S+fuel≤2^d) (headerFits : S≤2^w) (inside : t<fuel)
    (empty : c.privateMem=fun _ => 0)
    (ran : RAM.advance M.program t c (initialMemory S header)=some (done,out))
    (halt : M.program.step done=.finish result) :
    ∃ es : List (Event (w+1)), es.length=t ∧
      (∀ a : Word w, replay (initialMemory S (wide ∘ header)) es a.val=wide (out a.val)) ∧
      ∃! rows : List (TraceRows.Row (w+1) (Snapshot w p r)), rows.length=fuel ∧
        verifies (exposed M) (snapshot c) S d (wide ∘ header) rows ∧
        TraceRows.report rows=⟨es,result.map wide⟩ := by
  have initial : Matches (initialMemory S (wide ∘ header)) (initialMemory S header) c.privateMem := by
    have image : inputBank (initialMemory S header) = initialMemory S (wide ∘ header) :=
      TraceRows.inputBank_initialMemory S header headerFits
    rw [empty, ← image]
    exact matches_inputBank _
  obtain ⟨image,executed,imageAgrees⟩ := advance_exposed M initial ran
  obtain ⟨es,len,replayed,unique⟩ :=
    advance_history (exposed M) (wide ∘ header) image (result.map wide) inside room executed
      (finish_exposed M done result halt)
  exact ⟨es,len,fun a=>congrFun replayed a.val |>.trans (imageAgrees.external a),unique⟩

end Hierarchy.TaggedShorterHistory

end
end OAI
