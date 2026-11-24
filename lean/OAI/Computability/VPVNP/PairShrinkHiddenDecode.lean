import OAI.Computability.VPVNP.PairShrinkHiddenGuess

/-!
# Decoding an arbitrary complete native hidden-field stream

The same field widths that the native loop reads determine a partition of
any sufficiently long bit list. This includes empty fields and preserves
the remaining bits for the next node operation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess

open BurstRAM PrivateRAM NodeArguments.ChildScan

variable {W p r k : ℕ}

/-- Replace each field's bits, retaining its ID and consuming its recorded width. -/
def decode : List Row → List Bool → List Row × List Bool
  | [], bs => ([],bs)
  | e::es, bs =>
    let next := decode es (bs.drop e.2.length)
    ((e.1,bs.take e.2.length)::next.1,next.2)

private theorem decode_at (g : Args W) (m : Memory W) (es : List Row) (ptr : ℕ)
    (ok : ∀ i : Fin es.length, ValidAt g m (ptr+i.val) es[i.val]) (bs : List Bool)
    (enough : (stream es).length ≤ bs.length) :
    let d := decode es bs
    d.1.length = es.length ∧ stream d.1 ++ d.2 = bs ∧
      ∀ i : Fin d.1.length, ValidAt g m (ptr+i.val) d.1[i.val] := by
  induction es generalizing ptr bs with
  | nil => exact ⟨rfl,rfl,fun i => Fin.elim0 i⟩
  | cons e es ih =>
    have len : e.2.length + (stream es).length ≤ bs.length := by simpa only [stream,List.flatMap_cons,List.length_append] using enough
    have eqLen : (bs.take e.2.length).length = e.2.length := by simp [Nat.min_eq_left (by omega : e.2.length ≤ bs.length)]
    have vs (i : Fin es.length) : ValidAt g m (ptr+1+i.val) es[i.val] := by
      simpa only [Fin.val_succ,List.getElem_cons_succ,← Nat.add_assoc,Nat.add_right_comm] using ok i.succ
    have ve : ValidAt g m ptr e := by simpa using ok 0
    obtain ⟨size, part, tail⟩ := ih (ptr+1) vs (bs.drop e.2.length) (by simp; omega)
    refine ⟨congrArg Nat.succ size,?_,?_⟩
    · change bs.take e.2.length ++ stream (decode es (bs.drop e.2.length)).1 ++ (decode es (bs.drop e.2.length)).2 = bs
      rw [List.append_assoc,part,List.take_append_drop]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.val_zero,Nat.add_zero,List.getElem_cons_zero,decode,ValidAt,eqLen] using ve
      · simpa only [Fin.val_succ,List.getElem_cons_succ,decode,← Nat.add_assoc,Nat.add_right_comm] using tail j

/-- The decoder drops exactly the total number of requested field bits. -/
theorem decode_tail (es : List Row) (bs : List Bool) :
    (decode es bs).2 = bs.drop (stream es).length := by
  induction es generalizing bs with
  | nil => rfl
  | cons e es ih =>
    change (decode es (bs.drop e.2.length)).2 = _
    rw [ih,List.drop_drop]
    simp only [stream,List.flatMap_cons,List.length_append]

/-- Sufficient input determines both the actual accepted prefix and its tail. -/
theorem decode_valid (g : Args W) (m : Memory W) (es : List Row) (ok : ValidRows g m es)
    (bs : List Bool) (enough : (stream es).length ≤ bs.length) :
    let d := decode es bs
    d.1.length = es.length ∧ stream d.1 ++ d.2 = bs ∧ ValidRows g m d.1 :=
  decode_at g m es g.row ok bs enough

/-- The actual native run from a raw stream writes the decoded fields and
passes the exact remaining suffix to its continuation. -/
theorem native_decode {M : Machine W p r k} {pc : Stage → Fin p} {reg : Fin 22 ↪ Fin r} {done : Fin p}
    (link : Linked M pc reg done) (g : Args W) (m : Memory W) (es : List Row)
    (c : Config W p r) (entry : c.pc = pc (.inl .one)) (inputs : Inputs g reg c)
    (fit : g.countBase+g.owner < 2^W) (count : (m (g.countBase+g.owner)).val = es.length)
    (ok : ValidRows g m es) (bs : List Bool) (enough : (stream es).length ≤ bs.length) :
    let parsed := decode es bs
    ∃ d, d.pc = done ∧ d.privateMem = storeRows g.scratchBase g.slotStride parsed.1 c.privateMem ∧
      d.persistent = c.persistent ∧ ∀ fuel, execute M.program (fuel+(events g m parsed.1).length) c m bs =
        (execute M.program fuel d m parsed.2).map (fun q => ⟨events g m parsed.1 ++ q.events,q.result⟩) := by
  obtain ⟨len,part,valid⟩ := decode_valid g m es ok bs enough
  obtain ⟨d,pref,endPC,_,priv,pers⟩ := native link g m (decode es bs).1 c entry inputs fit (count.trans len.symm) valid
  refine ⟨d,endPC,priv,pers,fun fuel => ?_⟩
  have path := pref fuel (decode es bs).2
  rwa [part] at path

end PairSimulation.ShrinkHiddenGuess

end VPVNP
end Computability
end OAI
