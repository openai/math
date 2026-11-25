import OAI.Computability.BorderVNP.TeamTapeInputRouteVerify

/-! # One closed sorter from the physical owner streams and emitted record array -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputRoute.Verify

open VPVNP BurstRAM RAMTape RAMLayout RAMSerialization TeamTapeSorting

attribute [local instance] TeamTapeSorting.portDecidableEq

/-- Stage all of the owner's virtual banks, then use the actual saved flag to run the
correct number of complete physical sorters. -/
def processor : FiniteRoutine Port := (loader.onPorts Sum.inr).followedBy terminal

/-- The processor's two canonicality guard workspaces start empty, alongside the real
parser and closed record-buffer stacks. -/
def initial (s : Stacks TeamTapeInputRoute.Port) : Stacks Port := Sum.elim (fun _ => []) s

variable {d e w : ℕ}

private theorem bank_eq (hw : 2 ≤ w) (lane : Bool) (a : Fields d e w) (v : Word d)
    (rows : Word d → List (WordRecord w)) (out : Stacks TeamTapeInputRoute.Port)
    (h : out ∘ TeamTapeInputRoute.Port.post lane = SitePost.prestate v (incoming a v) (outgoing a v)
      (SortReplay.emittedBlock hw e (rows v),[]) (comparisonBits a v)) :
    initial out ∘ lanePort lane = siteInput hw a v (rowInput e rows) := by
  rw [siteInput,rawBlock_eq_emitted]
  funext p; cases p with
  | inl => rfl
  | inr => exact congrFun h _

/-- Starting from the raw metadata, incident link bits, and closed physical record array,
the owner checker counts exactly the joint local memory/format decision on its assigned
virtual blocks. It halts on all paths, including inconsistent or malformed link messages. -/
theorem processor_spec (n : ℕ) (hw₂ : 2 ≤ w) (cap : 2^d*2^e < 2^w)
    (a : Fields d e w) (v : Word d) (other : Option (Word d))
    (rows : Word d → List (WordRecord w)) (empty : ∀ u, other = some u → rows u = [])
    (s : Stacks TeamTapeInputRoute.Port) (tail rest : List Bool) (hd : d ≤ n) (hw : w ≤ n)
    (hH : 2^e ≤ n) (hL : comparisonSize d e w ≤ n)
    (hi : s metadata = metadataBits n e w v other ++ tail) (hs : s source = ownerBits a v other ++ rest)
    (ww : (s widthSource).length = w) (bc : (s bucket).length = 2^e) (hc : s .suffixSize = [])
    (hb : s (.entry (.inl .bits)) = []) (hh : s (.entry (.inl .high)) = [])
    (htmp : s (.entry (.inl .scratch)) = []) (hm : s (.work .count) = [])
    (ht : s (.work .tmp) = []) (hz : ∀ b i, s (.post b i) = [])
    (hblock : s closedBlock = List.ofFn ((blockFormat (2^e) hw₂).encode (RecordBuffer.slots (2^e) (rows v))))
    (fuel : ℕ) (hbudget : 600*(n+1)^2 + 2*siteBudget d e w+1 ≤ fuel) :
    (∀ c, processor.body.count c fuel (initial s) =
      @ite ℕ (ownerValid hw₂ cap a (rowInput e rows) v other) (Classical.propDecidable _) 1 0) ∧
      ∀ c, processor.body.AllStops c fuel (initial s) := by
  obtain ⟨t,bound,out,run,_,_,hflag,hfirst,hsecond,_,_⟩ :=
    loader_spec n hw₂ a v other s tail rest (rows v) hd hw hH hL hi hs ww bc hc hb hh htmp hm ht hz hblock
  have frame : (loader.onPorts Sum.inr).Runs t (initial s) (initial out) := by
    apply loader.runs_onPorts_framed Sum.inr_injective run (fun _ => rfl) (fun _ => rfl)
    rintro (k|k) h
    · rfl
    · exact (h k rfl).elim
  have hreal := bank_eq hw₂ false a v rows out hfirst
  have hvirtual (u : Word d) (hu : other = some u) := bank_eq hw₂ true a u rows out
    (by simpa only [empty u hu] using hsecond u hu)
  have hx := terminal_spec hw₂ cap a (rowInput e rows) v other (initial out) _ hflag hreal hvirtual
    (fuel-t) (by omega)
  have he : fuel = (fuel-t)+t := by omega
  constructor
  · intro c
    change ((loader.onPorts Sum.inr).body.followedBy terminal.body).count c fuel (initial s) = _
    rw [Routine.count_followedBy, he, frame.count_eq]
    exact hx.1 _
  · intro c
    change ((loader.onPorts Sum.inr).body.followedBy terminal.body).AllStops c fuel (initial s)
    rw [Routine.allStops_followedBy, he, frame.allStops_iff]
    exact hx.2 _

end TeamTapeInputRoute.Verify

end BorderVNP
end Computability
end OAI
