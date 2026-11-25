import OAI.Computability.MultitapeWeakETH.HistoryVisitCases
import OAI.Computability.MultitapeWeakETH.WitnessPushCodes
import OAI.Computability.VPVNP.PairSelectedKernelReaders
import OAI.Computability.VPVNP.PairSelectedPacketOrders

/-! # Child jobs and private prefixes in the selected term parser's order -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP BurstRAM Compression CompressorRecords NetworkKernel PairSimulation
open LocalHistory NodeArguments TraversalRows TreeDecode WitnessWalk
open scoped Classical
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
    {f : B.Entry → R} {hf : B.IsSolution f}

def inputJob {a g : ℕ} (X : State a g) (level : ℕ) (u : X.network.Site) (old : X.network.Half u) : Job :=
  ((tally level,tally ((siteOrder X).entries.symm u).val),packed X u old)

def outputJob (V : SelectedLevel B f hf) (level : ℕ) (v : (V.pass.step.term V.term).output.Site)
    (new : (V.pass.step.term V.term).output.Half v) : Job :=
  ((tally (level+1),tally ((outputOrder V).entries.symm v).val),
    pullBits (V.pass.output_eq V.term) (packed (V.pass.next V.term)) v new)

local notation "rdr(" V ")" => originReader B f hf (SelectedLevel.origin V) (SelectedLevel.term V)

private theorem selected_order (V : SelectedLevel B f hf) :
    (∀ u, (rdr(V)).order.children u = (siteOrder V.input).restrict
      (fun p => u = (V.pass.step.term V.term).place p)) ∧
    (∀ u, (rdr(V)).order.outgoing u = outgoingOrder V.input u) ∧
    (∀ u, (rdr(V)).order.incoming u = incomingOrder V.input u) ∧
    (rdr(V)).payload = statePayload V.input := by
  rcases V with ⟨a,g,b,n,X,pass,origin,term,tape⟩
  cases origin with
  | shrink i h X => subst g; exact ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,rfl⟩
  | refresh X => exact ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,rfl⟩

variable (V : SelectedLevel B f hf) (j : Fin (levelLayer B f hf V).count) (w level : ℕ)
local notation "v" => outputSite V j
local notation "o" => childOrder V j
local notation "t" => V.pass.step.term V.term


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 6000 in
theorem visit_child_jobs (old : Placed (V.pass.step.term V.term).place V.input.network.Half (outputSite V j)) :
    let ids := ((levelLayer B f hf V).ids j).map tally
    let bank := NamedPackets.placedBank V.input _ (v) (o) old w
    childJobs (tally level,ids,bank.2) =
      WitnessWalk.children (rdr(V)) (inputJob V.input level) (v) old := by
  intro ids bank
  have order := (selected_order V).1 (v)
  let ordered (os : Order ((t).Preimage (v))) :=
    List.ofFn fun i => let u := os.entries i; inputJob V.input level u.val (old u.val u.prop)
  apply Eq.trans _ (congrArg ordered order.symm)
  let name (i : Fin (o).length) := tally ((siteOrder V.input).entries.symm ((o).entries i).val).val
  let packet (i : Fin (o).length) := packed V.input ((o).entries i).val (old _ ((o).entries i).prop)
  have num : ids = (List.finRange (o).length).map name := by
    change (List.ofFn (fun i => ((siteOrder V.input).entries.symm ((o).entries i).val).val)).map tally = _
    rw [List.map_ofFn,List.ofFn_eq_map]; rfl
  have bs : bank.2 = (List.finRange (o).length).map packet := List.ofFn_eq_map ..
  rw [num,bs,childJobs_ordered]
  exact List.ofFn_eq_map.symm

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 6000 in
theorem visit_node_bits (old : Placed (V.pass.step.term V.term).place V.input.network.Half (outputSite V j)) (new : (t).output.Half (v)) (x : ((rdr(V)).witness (v) old new).Choice) :
    let bank := NamedPackets.placedBank V.input _ (v) (o) old w
    (rdr(V)).nodeBits (v) old new x = bank.2.flatten ++ ((rdr(V)).read (v) old new).encode x := by
  intro bank
  obtain ⟨order,out,inc,payload⟩ := selected_order V
  apply (TermParsers.nodeBits_eq_childPackets (rdr(V)) (fun _ => 0) (v) old new x).trans
  apply congrArg (· ++ _)
  rw [TermParsers.childPackets_state V.input (rdr(V)) payload out inc,order (v),List.flatMap_def,List.map_ofFn]
  rfl

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
