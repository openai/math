import OAI.Computability.VPVNP.CompressorShrinkTermLaunch
import OAI.Computability.VPVNP.CompressorSourceGroups

/-!
# The certified term interval of the complete shrinking script

The raw reports of the actual gather and term verifier are retained as
two chronological packets. Both satisfy the online replay and clock
conditions. The selector's recipe reads the same published level header
after the gather writes its dense demand pairs.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkTermOnline

open BurstRAM BlockPlanner Compression DescriptorSpace Schedule ShrinkBlockInputs ShrinkInput ShrinkTermPackets
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
variable (s : X.ShrinkSelection B.shrink) (fuel : ℕ)
local notation "A" => BlockProgram.script B
local notation "O" => BlockProgram.arena B i.val 0
local notation "H" => ShrinkTermSelection.bundles X
local notation "Q" => ShrinkTermSelection.ranks (a i)
local notation "N" => ShrinkTermInputs.motifCount X
local notation "D" => Online.N (BlockPlanner.Script.size (BlockProgram.script B)) (BlockPlanner.Script.size (BlockProgram.script B))

/-- Combine a globally indexed term visit with its actual entry memory and the reports emitted
by its source run. -/
def packet (j : Stage) (raw : Memory w) (rs : List (Report w)) :
    SourceWalk.Packet (SourceOnline.Visit A w) w := ⟨globalVisit B i X T start s fuel j,raw,rs⟩

/-- The gather packet followed by the selector packet, starting the selector in the memory
produced by the gather reports. -/
def packetList (raw : Memory w) (gs ts : List (Report w)) :=
  [packet B i X T start s fuel .gather raw gs,packet B i X T start s fuel .select (after raw (eventLog gs)) ts]


private theorem pair_group {U : Script} {L : DescriptorSpace.Layout} {base : Word w} {cap ordinal total : ℕ}
    (m : Memory w) (p q : SourceOnline.Packet U w)
    (first : p.input = m) (next : q.input = p.output)
    (rp : p.stage.Runs p.input p.reports) (rq : q.stage.Runs q.input q.reports)
    (hp : SourceOnline.Checked U L cap p) (hq : SourceOnline.Checked U L cap q)
    (ep : SourceOnline.Prepared U L base ordinal total p) (eq : SourceOnline.Prepared U L base (ordinal+1) total q) :
    SourceOnline.Group U L base cap ordinal total m [p,q] := by
  refine ⟨⟨first,rp,next,rq,trivial⟩,fun x h => ?_,fun n => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> assumption
  · change Fin 2 at n
    fin_cases n <;> assumption

set_option maxHeartbeats 1200000 in
theorem certify (L : DescriptorSpace.Layout) (base : Word w) (iteration total cap : ℕ)
    (before : Memory w) (gs ts : List (Report w))
    (hg : ShrinkDemandGather.Gathered H Q (pairBank X T start) fuel before gs)
    (ht : ShrinkTermSelection.Written B.shrink X (demandHead X start) (termHead X start)
      10 fuel s (after before (eventLog gs)) ts)
    (hcap : ShrinkDemandGather.cost < fuel) (space : ShrinkInput.termEnd X start 10 < 2^w)
    (header : ShrinkHeaderReads.Header i X T start L ((S.steps+1)*iteration) before)
    (headerBefore : levelStart L ((S.steps+1)*iteration+i.val) + 60 < start)
    (arityFit : arity (A).catalog = L.shape.arity) (baseFit : base.val = L.base)
    (totalRows : total = directoryRows L) (live : ordinal B i iteration .select < total)
    (recipeClock : ∀ j, ((A).plan.recipes (index B i j)).2.code.length+1+2*D+5 ≤ cap)
    (dataClock : ∀ j, fuel+3+4*(((A).catalog (index B i j)).params+1)+2*D+5 ≤ cap) :
    SourceOnline.Group A L base cap (ordinal B i iteration .gather) total before
      (packetList B i X T start s fuel before gs ts) := by
  let mid := after before (eventLog gs)
  have ga := gathered_packet B i O X T start s fuel hcap space before gs hg
  have te := selected_packet B i O X T start s fuel space mid ts ht
  have first : levelStart L 0 ≤ levelStart L ((S.steps+1)*iteration+i.val) := levelStart_mono L (Nat.zero_le _)
  have startData : levelStart L 0 ≤ start := by omega
  have fits : levelStart L 0 < 2^w := first.trans_lt ((Nat.le_add_right ..).trans_lt header.room)
  have hd : (demandHead (w := w) X start).val = ShrinkInput.stop X start :=
    Nat.mod_eq_of_lt (by unfold termEnd at space; omega)
  obtain ⟨h₁,h₂,h₃,h₄⟩ := range_bounds X start
  have keep (x : ℕ) (hx : x < start) : mid x = before x :=
    hg.frame x (.inl (show x < (demandHead (w := w) X start).val by rw [hd]; omega))
  have header' := header.keep_below headerBefore keep
  have succ : ordinal B i iteration .gather + 1 = ordinal B i iteration .select := by
    unfold ordinal
    rw [show (localIndex B i .gather).val = 0 from rfl,show (localIndex B i .select).val = 1 from rfl,Nat.add_zero]
  have hp : 0 < fuel := (Nat.zero_le _).trans_lt hcap
  have gp := prepared B i X T start s fuel L base iteration total .gather before gs header space arityFit baseFit fits
    totalRows (by omega)
  have tp := prepared B i X T start s fuel L base iteration total .select mid ts header' space arityFit baseFit fits
    totalRows live
  let gPacket := packet B i X T start s fuel .gather before gs
  let tPacket := packet B i X T start s fuel .select mid ts
  have tp' : SourceOnline.Prepared A L base (ordinal B i iteration .gather+1) total tPacket :=
    Eq.mp (congrArg (fun n => SourceOnline.Prepared A L base n total tPacket) succ.symm) tp
  exact pair_group before gPacket tPacket rfl rfl
    (runs B i X T start s fuel .gather _ _ ga) (runs B i X T start s fuel .select _ _ te)
    (checked B i X T start s fuel L cap .gather before gs ga hp space startData (recipeClock _) (dataClock _))
    (checked B i X T start s fuel L cap .select mid ts te hp space startData (recipeClock _) (dataClock _))
    gp tp'

end CompressorRecords.ShrinkTermOnline

end

end VPVNP
end Computability
end OAI
