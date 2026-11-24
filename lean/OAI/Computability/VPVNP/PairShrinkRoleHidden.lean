import OAI.Computability.VPVNP.PairShrinkRoleStages
import OAI.Computability.VPVNP.PairNodeChildStage
import OAI.Computability.VPVNP.PairShrinkHiddenDecode
import OAI.Computability.VPVNP.PairShrinkHiddenCost

/-!
# The hidden-field stage of a shrinking vertex

The native directory gives an ID and width for each absorbed field at the
vertex. A full prefix supplies exactly those fields and updates their scratch
cells. A stream ending in any one of the fields rejects.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess
open scoped Fin.CommRing

variable {w endAddr p r k : ℕ} {M : Machine w p r k} {pc : Stage → Fin p}
  {reg : Fin 22 ↪ Fin r} {done : Fin p}

private def packets (es : List Row) : List Packet := es.map fun e => ⟨e.1,e.2⟩

private theorem stored (g : Args w) (es : List Row) (priv : Word w → Word w) :
    storeRows g.scratchBase g.slotStride es priv =
      storePackets ⟨g.scratchBase,g.slotStride⟩ (packets es) priv := by
  simp only [storeRows, storePackets, packets, List.foldl_map, Arena.base]

/-- The parsed rows use the dense hidden ID as the slot number in scratch. -/
def hiddenReader (g : Args w) (m : Memory w) (seed : List Row) :
    Reader w endAddr (List Row) := fun _ saved bs =>
  if (stream seed).length ≤ bs.length then
    let (es,tail) := decode seed bs
    some (⟨es, events g m es,
      writePackets ⟨g.scratchBase,g.slotStride⟩ (packets es) saved⟩,tail)
  else none

private theorem decoded_split (seed : List Row) (bs : List Bool) :
    stream (decode seed bs).1 ++ (decode seed bs).2 = bs := by
  induction seed generalizing bs with
  | nil => rfl
  | cons e seed ih =>
    simp only [decode, stream, List.flatMap_cons, List.append_assoc]
    rw [← stream, ih, List.take_append_drop]

theorem hiddenReader_split (g : Args w) (m : Memory w) (seed : List Row)
    (node : Word w) (saved : DFS.Scratch w endAddr) (bs out tail)
    (read : hiddenReader g m seed node saved bs = some (out, tail)) :
    bs = choiceBits out.trace ++ tail := by
  unfold hiddenReader at read
  split at read
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj read)
    rw [(cost g m _).2.2]
    exact (decoded_split seed bs).symm
  · contradiction

/-- Registers outside the hidden-field loop's writes retain their values. -/
def HiddenPreserved (reg : Fin 22 ↪ Fin r) (q : Fin r) : Prop :=
  q ≠ reg 3 ∧ q ≠ reg 21 ∧ ∀ j ∈ ShrinkHiddenGuess.scratch, q ≠ reg j

/-- Run the actual instruction table on the decoded fields. The scratch
update is computed from the entry scratch, even if other cells in the full
private memory differ. -/
theorem hidden_realizes (link : ShrinkHiddenGuess.Linked M pc reg done)
    (g : Args w) (m : Memory w) (seed : List Row) (dfs : Fin 9 ↪ Fin r)
    (pre : Word w → Config w p r → Prop) (post : List Row → Word w → Config w p r → Prop)
    (entry : ∀ node c, pre node c → c.pc = pc (.inl .one) ∧ Inputs g reg c)
    (fit : g.countBase + g.owner < 2 ^ w) (count : (m (g.countBase + g.owner)).val = seed.length)
    (valid : ValidRows g m seed) (above : endAddr ≤ g.scratchBase)
    (apart : ∀ i, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → HiddenPreserved reg (dfs i))
    (resume : ∀ node c es d, pre node c → ValidRows g m es → d.pc = done →
      d.privateMem = storeRows g.scratchBase g.slotStride es c.privateMem →
      d.persistent = c.persistent → (∀ q, HiddenPreserved reg q → d.reg q = c.reg q) →
      post es node d) :
    Realizes (hiddenReader (endAddr := endAddr) g m seed) M m dfs pre post := by
  constructor
  · intro node c bs out tail hc read
    have splitBits := hiddenReader_split g m seed node _ bs out tail read
    unfold hiddenReader at read
    split at read
    · rename_i enough
      let es := (decode seed bs).1
      obtain ⟨len,_,rows⟩ := decode_valid g m seed valid bs enough
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj read)
      obtain ⟨ep,inputs⟩ := entry _ _ hc
      obtain ⟨d,path,donePC,keep,mem,pers⟩ :=
        ShrinkHiddenGuess.native link g m es c ep inputs fit (count.trans len.symm) rows
      have frameReg (q) (h : HiddenPreserved reg q) := keep q h.1 h.2.1 h.2.2
      refine ⟨splitBits,d,resume node c es d hc rows donePC mem pers frameReg,?_,?_,?_⟩
      · refine ⟨fun i hi => frameReg _ (apart i hi), ?_, pers⟩
        intro a ha
        rw [mem]
        have low {xs : List Row}
            (ends : ∀ e ∈ xs, g.slot e.1 + e.2.length ≤ 2 ^ w) (priv : Word w → Word w) :
            storeRows g.scratchBase g.slotStride xs priv a = priv a := by
          induction xs generalizing priv with
          | nil => rfl
          | cons e xs ih =>
            apply (ih (fun e he => ends e (List.mem_cons_of_mem _ he)) _).trans
            exact PrivateFields.storeBits_outside _ _ _ a (ends e List.mem_cons_self)
              (Or.inl (ha.trans_le (above.trans (Nat.le_add_right ..))))
        apply low
        intro e he
        obtain ⟨i,hi,eqn⟩ := List.mem_iff_getElem.mp he
        exact eqn ▸ (rows ⟨i,hi⟩).2.2.le
      · rw [mem, stored, scratch_storePackets]
      · change Prefix M m c d (choiceBits (events g m es)) (events g m es)
        rwa [(cost g m es).2.2]
    · contradiction
  · intro node c bs hc reject
    by_cases enough : (stream seed).length ≤ bs.length
    · simp [hiddenReader, enough] at reject
    · obtain ⟨ep,inputs⟩ := entry _ _ hc
      exact native_short link g m seed c ep inputs fit count valid bs (Nat.lt_of_not_ge enough)

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
