import OAI.Hierarchy.DescentPackedMatchOrdinary
import OAI.Hierarchy.DescentPackedSixBirthTables

namespace OAI
/-! # Six actual party records directly on the normalized ordinary matcher run -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentStageEdgeReceipt DescentSIMDLookup DescentPackedProfileWindow ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentTerminalEpochDecoder DescentKernelHistory.BitDescription DescentSixParty.StarKeys Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
attribute [local irreducible] Gather.ROM.after Gather.ROM.machine Gather.ROM.ticks
  SixBirths.mounted SixBirths.after SixBirths.program SixBirths.mount
  topologyWords Gather.flat Gather.descriptorInputs
  slabPacking pairNumber scannedRows laneCounts

variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (groupKey : J↪ℕ) (vertex : V↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
    (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "rankOf" => groupRank groupKey vertex
local notation "names" => cableNames k rankOf
local notation "peers" => rotor A rankOf
local notation "r" => 2^k
local notation "K" => 2^(k+1)
local notation "p" => 2*A.cap
local notation "panel" => terrain (short:=short) A native S ready names win peers
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "real" => spread groups hosts panel
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed (groupRank groupKey vertex))
    (fit : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (profile : ℕ)
local notation "s" => shape r A.degree p profile
local notation "R" => M*(s).pairs
local notation "slotOf" => slot he A groups hosts hm

local notation "N" => (K*H)*chunks G M

include coord named fit winner df in
theorem ordinary_births (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (pins : ∀i,(stream i).val=profileAt (inputNumber he A groups hosts) ((scannedRows he A.stage).profile choice) i)
    (wins : Fin r→Bank) (marked : Fin r→Fin p→Bank) (P : DescentPackedColony.Ports A.degree)
    (unit base seats : ℕ) (m : Memory w)
    (large : Gather.matchUnit s short r A.degree p≤unit) (shortWord : unit*M≤w/2)
    (roster : DescentPackedColony.Mounted P (hostRotor hosts (DescentGroupPeerOrder.hostRoster A vertex)) m G M)
    (access : ∀x,DescentPackedColony.Accessible P (wins x) H G M w base)
    (mf : ∀x i,(marked x i).Fits w base) (mr : ∀x i,H*chunks G M≤(marked x i).size)
    (own : ∀x,DescentPackedColony.Reads (wins x) (fun h g=>(real h g).winner x) M m)
    (old : ∀x i,DescentPackedColony.Reads (marked x i) (fun h g=>(real h g).neighbor x i) M m)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (raw : let b:=(Gather.ROM.place s short r A.degree p K H G M unit base seats).raw
      ∀i<b.size,m (b.base+i)=((DescentPackedProfileWindow.word (s).digit R stream i).val:Word w))
    (extra : SixBirths.unit s≤unit)
    (space : let l:=(Gather.ROM.place s short r A.degree p K H G M unit base seats).layout
      SixBirths.outputBase s M l.topology (SixBirths.tapeBank l.out N)+N<2^w) :
    let l:=(Gather.ROM.place s short r A.degree p K H G M unit base seats).layout
    let tape:=SixBirths.tapeBank l.out N
    let rom:=SixBirths.tableStart l.topology tape
    let dest:=SixBirths.outputBase s M l.topology tape
    let banks:=SixBirths.mountedBanks s M rom l.topology tape
    let field:=Gather.expr wins marked P H
    let E:=Gather.ROM.machine s short r A.degree p A.cap K H G M unit base seats w field
    let o:=Gather.ROM.after s short r A.degree p A.cap K H G M unit base seats field m
    let issue:=(SixBirths.mount s M rom w).seq (SixBirths.program banks N dest w)
    let done:=SixBirths.after banks N dest (SixBirths.mounted s M rom o)
    (E.seq issue).Exec m done (Gather.ROM.ticks s short r A.degree p K H G M unit base seats field+
      ((4+10*SixBirths.entries s M)+(4+54*N))) ∧
      (∀c : ScanColonies he A.stage,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
        let j:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
        ∃u : Fin (s).pairs,u.val=j ∧ ∀q : Fin 6,
          let pos:=SixBirths.slot (slotOf c).2 u q
          SixBirths.atom A.stage.z (digit ((s).digit+1) pos.val (done (dest+(slotOf c).1.val)).val) pos.val=
            some (A.stage.z,DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩),q.val)) ∧
      CheapCode (E.seq issue) := by
  let L:=Gather.ROM.place s short r A.degree p K H G M unit base seats
  let l:=L.layout
  let tape:=SixBirths.tapeBank l.out N
  let rom:=SixBirths.tableStart l.topology tape
  let dest:=SixBirths.outputBase s M l.topology tape
  let banks:=SixBirths.mountedBanks s M rom l.topology tape
  let keys:=topologyWords (M:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real))
  have ca : N≤l.topology.size:=Gather.ROM.column_size _ _
  have cb : N≤tape.size:=Nat.le_pow_clog (by decide) _
  have limit : SixBirths.width s M≤w := by
    have small : ((s).digit+1)*((s).pairs*6)≤unit:=(le_max_right ..).trans extra
    have bound:= (Nat.mul_le_mul_right M small).trans shortWord
    calc
      SixBirths.width s M=(((s).digit+1)*((s).pairs*6))*M:=by unfold SixBirths.width;ring
      _≤w:=bound.trans (Nat.div_le_self ..)
  obtain ⟨fitNew,before⟩:=SixBirths.placed s M N w l.topology tape ca cb limit space
  have priorSpace : L.endAddr<2^w:=by
    change l.out+N<2^w
    have side : l.out+N≤rom:=before.2
    have tail : rom≤dest:=Nat.le_add_right ..
    exact (side.trans (tail.trans (Nat.le_add_right ..))).trans_lt space
  obtain ⟨matchRun,top,received,_,lowCost⟩:=ordinary_run A native S ready groupKey vertex win he groups hosts hm coord named fit winner df profile
    choice stream pins wins marked P unit base seats m large shortWord priorSpace roster access mf mr own old cap raw
  let matcherMemory := Gather.ROM.after s short r A.degree p A.cap K H G M unit base seats
    (Gather.expr wins marked P H) m
  obtain ⟨write,records,writeCost⟩ := SixBirths.fresh s M N rom dest w l.topology tape fitNew before
    matcherMemory keys top
  refine ⟨?_,?_,cheap_seq lowCost writeCost⟩
  · intro P₁ R₁ K₁ machine
    exact Procedure.Exec.then matchRun write machine
  intro c e
  obtain ⟨u,number,selected⟩ := received c e
  have counts:=measured A native S ready rankOf win he groups hosts hm coord named fit winner df profile
  let j:=pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e
  have active : j.val<(laneCounts s M (keys (slotOf c).1) (slotOf c).2).val := (counts.live c).symm ▸ j.isLt
  have occurs : u.val<(laneCounts s M (keys (slotOf c).1) (slotOf c).2).val:=by simpa only [number] using active
  refine ⟨u,number,?_⟩
  intro q
  dsimp only
  rw [records _ _ _ q,ite_eq_left occurs]
  change SixBirths.atom _ (digit _ _ (matcherMemory (l.out+(slotOf c).1.val)).val+1) _=_
  rw [selected]
  simp [SixBirths.atom,SixBirths.role]

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
