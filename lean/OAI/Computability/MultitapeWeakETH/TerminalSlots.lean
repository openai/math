import OAI.Computability.MultitapeWeakETH.TerminalFields

/-! # Addressing the actual endpoint slots of a terminal vertex -/

namespace OAI.Computability.MultitapeWeakETH.TerminalWords

open IntegerMultiplication Code VPVNP Compression CompressorRecords PairSimulation
open TerminalGatherGeometry LocalHistory
noncomputable section

abbrev SlotQuery := (Tally × Tally) × List Tally

/-- The first ordinal and the degree give all outgoing ports in order.
Looking up those same ordinals in the inverse column gives the sources
of the incoming ports, including both incidences of any loop. -/
def slots (q : SlotQuery) : List Tally :=
  let out := (Iter.lineup q.1.2).map (fun i => q.1.1 ++ i)
  out ++ out.map (fun i => Iter.pick [] (q.2,i))

theorem slots_poly : Poly slots := by
  have start : Poly (fun q : SlotQuery => q.1.1) := (Easy.fst.compose Easy.fst).poly
  have degree : Poly (fun q : SlotQuery => q.1.2) := (Easy.fst.compose Easy.snd).poly
  have add : Poly (fun p : Tally × Tally => p.1 ++ p.2) := Easy.fst.poly.app Easy.snd.poly
  have out := (start.pair (degree.compose Iter.poly_line)).compose (Poly.push [] [] add)
  exact out.app ((Easy.snd.poly.pair out).compose (Poly.push [] [] (Iter.facile []).poly))

def inverse {a g : ℕ} (X : State a g) := List.ofFn fun i : Fin (TerminalPrefix.arcCount X) =>
  tally (number X (X.slots.actualGraph.target.symm ((edgeOrder X).entries i))).val

def firstSlot {a g : ℕ} (X : State a g) (v : X.network.Site) := ((siteOrder X).entries.symm v).val * 2^a

theorem slots_eq {a g : ℕ} (X : State a g) (v : X.network.Site) :
    slots ((tally (firstSlot X v),tally (2^a)),inverse X) = edges X v false ++ edges X v true := by
  have pos (j : Fin (2^a)) : firstSlot X v + j.val = (number X (v,j)).val := by
    change _ * _ + _ = j.val + 2^a * ((siteOrder X).entries.symm v).val
    ring
  have out : ((Iter.lineup (tally (2^a))).map fun j => tally (firstSlot X v) ++ j) = edges X v false := by
    simp [Iter.lined,List.map_ofFn,Function.comp_def,Strip.Dims.mergeTally,pos,edges,arc]
  simp only [slots,out]
  congr 1
  simp [edges,List.map_ofFn,Function.comp_def,arc,inverse,Iter.entry,number]
  funext j
  exact congrArg (fun e : X.network.Edge => tally (number X (X.slots.actualGraph.target.symm e)).val)
    ((edgeOrder X).entries.apply_symm_apply (v,j))

/-- Scanning the inverse column followed by the shared bits produces the
typed terminal argument in the order consumed by the selected site parser. -/
theorem packet_program :
    ∃ eval : Fields × SlotQuery → Bits.Word, Poly eval ∧
      ∀ {a g : ℕ} (X : State a g) (v : X.network.Site) (f : Fin (∑ i,TerminalPrefix.width X i) → Bool),
        eval ((widths X,List.ofFn f),(tally (firstSlot X v),tally (2^a)),inverse X) =
          NodeArguments.packed X v (half X f v) := by
  refine ⟨fun q => gather (q.1,slots q.2),(Easy.fst.poly.pair (Easy.snd.poly.compose slots_poly)).compose gather_poly,?_⟩
  intro a g X v f
  simp only [slots_eq,gather_eq]

end
end OAI.Computability.MultitapeWeakETH.TerminalWords
