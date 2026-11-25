import OAI.Hierarchy.DescentPackedMatchPrepareROM

namespace OAI
/-! # From true previous-stage words to a single installed native matcher input -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare.ROM
open DescentSixParty DescentStageEdgeReceipt DescentSIMDLookup DescentPackedColony DescentGroupPeerOrder
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F T V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i a s M H G w : ℕ} {bs : T→ℕ} {W : MarkedWorld F d T bs} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J↪Fin G) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
local notation "rank" => groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "physical" => spread groups hosts (terrain (short:=s) A native S ready (cableNames k rank) win (rotor A rank))
local notation "rows" => H*chunks G M
local notation "r" => 2^k
local notation "p" => 2*A.cap

/-- Both sides of the entire native workspace are untouched, including a future raw profile shelf. -/
theorem high {kk D cap : ℕ} (C : Chart kk cap) (R : DescentSortedRoster.Chart) (base H G M : ℕ) (m : Memory w) (j : ℕ)
    (above : stop kk H G M D cap base≤j) : ProtocolRAM.result (passes C R base H G M D) m j=m j := by
  let es:=List.ofFn (expr C);let after:=ProtocolRAM.image base (H*D) (DescentSortedRoster.code R D H) m
  have hi : fieldBase base H D+es.length*(H*chunks G M)≤j := by simpa only [stop,es,List.length_ofFn] using above
  have late : base+H*D≤j := (Nat.le_add_right ..).trans hi
  exact (ProbeStage.Native.columns_frame es after (.inr hi)).trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr late))

variable (P : Ports A.degree) (out : Bank) (romBase rowBits shapeBits outputBits : ℕ) (act : Bank) (vals : Fin (2^k)→Bank) (wire : Fin (2^k)→Fin (2*A.cap)→Bank)
local notation "C" => chart romBase A.degree a M rowBits act vals wire
local notation "R" => roster romBase k A.degree A.cap a M H G shapeBits P.roster
local notation "len" => staticWords k A.degree A.cap a M H G
local notation "rom" => ROM.program w romBase k A.degree A.cap a s M H G
local notation "ps" => passes C R out.base H G M A.degree

theorem from_published (published : Fin H→Fin G→Fin (2^k)→Cell a)
    (liveWin : ∀u,published (hosts (A.pos u).2) (groups (A.pos u).1) (A.block u)=win (A.pos u) (A.block u)) (m : Memory w) (rs : Fin H→Fin A.degree→Option (Fin H))
    (geometry : ∀h j,j∈(List.ofFn (rs h)).filterMap id ↔ ∃v u : V,h=hosts v ∧ j=hosts u ∧ v∈A.near u)
    (fit : Room C A.degree a s M H G w out.base) (rf : DescentSortedRoster.Room R A.degree H w out.base)
    (sep : romBase+len≤out.base) (actTop : act.base+rows≤romBase) (winTop : ∀x,(vals x).base+rows≤romBase)
    (wireTop : ∀x j,(wire x j).base+rows≤romBase) (ids : ∀j,(P.ids j).base+rows≤romBase)
    (rankTop : P.roster.base+H*A.degree≤romBase) (off : P.offsets.base+H≤romBase) (ch : P.chunks.base+rows≤romBase)
    (aRead : Reads act (actors A groups hosts) M m) (wRead : ∀x,Reads (vals x) (fun h g=>published h g x) M m)
    (sRead : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (signed A native S ready groups hosts x j h g)) M m)
    (old : Mounted P rs m G M) :
    let ready:=ROM.after romBase k A.degree A.cap a s M H G m;let final:=ProtocolRAM.result ps ready
    ((rom).seq (ProtocolRAM.program w ps)).Exec m final ((4+10*len)+clock ps) ∧
      (∀x : Fin (2^k),Reads (gatedBank (k:=k) out.base H G M A.degree outputBits x) (fun h g=>(physical h g).winner x) M final) ∧
      (∀(x : Fin (2^k)) (j : Fin (2*A.cap)),Reads (markedBank (k:=k) (cap:=A.cap) out.base H G M A.degree outputBits x j) (fun h g=>(physical h g).neighbor x j) M final) ∧
      Mounted {P with roster:=out} (hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding))) final G M ∧
      (∀z,z<romBase ∨ stop k H G M A.degree A.cap out.base≤z→final z=m z) ∧ CheapCode ((rom).seq (ProtocolRAM.program w ps)) := by
  let first:=ROM.after romBase k A.degree A.cap a s M H G m
  have room : romBase+len<2^w := sep.trans_lt ((Nat.le_add_right ..).trans_lt rf.endFit)
  obtain ⟨inputs,raw⟩:=ROM.mounted (d:=s) romBase rowBits shapeBits m act vals wire P.roster (actors A groups hosts) (fun x h g=>published h g x)
    (signed A native S ready groups hosts) rs actTop winTop wireTop rankTop aRead wRead sRead old.roster
  have before (z : ℕ) (hz : z<romBase) : first z=m z := ROM.frame _ _ _ _ _ _ _ _ _ _ _ (.inl hz)
  have left : romBase≤out.base := (Nat.le_add_right ..).trans sep
  have carry : Mounted P rs first G M := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t j;rw [before _ ((Nat.add_lt_add_left (row H G M t).isLt _).trans_le (ids j))];exact old.ids t j
    · intro v j;have small : v.val*A.degree+j.val<H*A.degree := (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
      rw [before _ ((Nat.add_lt_add_left small _).trans_le rankTop)];exact old.roster v j
    · intro v;rw [before _ ((Nat.add_lt_add_left v.isLt _).trans_le off)];exact old.offsets v
    · intro t;rw [before _ ((Nat.add_lt_add_left (row H G M t).isLt _).trans_le ch)];exact old.chunks t
  obtain ⟨right,gate,chip,sorted,past,op⟩:=native_published A native S ready groups hosts win published liveWin C R P out outputBits first rs geometry fit inputs rf raw carry
    (fun j=>(ids j).trans left) (off.trans left) (ch.trans left)
  refine ⟨Procedure.Exec.then (ROM.run romBase k A.degree A.cap a s M H G m room) right,gate,chip,sorted,?_,cheap_seq (by apply ROM.cheap) op⟩
  intro z outside;rcases outside with low|upper
  · exact (past z (low.trans_le left)).trans (before z low)
  · have top : out.base≤ stop k H G M A.degree A.cap out.base := (Nat.le_add_right _ (H*A.degree)).trans (Nat.le_add_right ..)
    exact (high C R out.base H G M first z upper).trans (ROM.frame _ _ _ _ _ _ _ _ _ _ _ (.inr (sep.trans (top.trans upper))))

theorem from_old (m : Memory w) (rs : Fin H→Fin A.degree→Option (Fin H))
    (geometry : ∀h j,j∈(List.ofFn (rs h)).filterMap id ↔ ∃v u : V,h=hosts v ∧ j=hosts u ∧ v∈A.near u)
    (fit : Room C A.degree a s M H G w out.base) (rf : DescentSortedRoster.Room R A.degree H w out.base)
    (sep : romBase+len≤out.base) (actTop : act.base+rows≤romBase) (winTop : ∀x,(vals x).base+rows≤romBase)
    (wireTop : ∀x j,(wire x j).base+rows≤romBase) (ids : ∀j,(P.ids j).base+rows≤romBase)
    (rankTop : P.roster.base+H*A.degree≤romBase) (off : P.offsets.base+H≤romBase) (ch : P.chunks.base+rows≤romBase)
    (aRead : Reads act (actors A groups hosts) M m) (wRead : ∀x,Reads (vals x) (winners groups hosts win x) M m)
    (sRead : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (signed A native S ready groups hosts x j h g)) M m)
    (old : Mounted P rs m G M) :
    let ready:=ROM.after romBase k A.degree A.cap a s M H G m;let final:=ProtocolRAM.result ps ready
    ((rom).seq (ProtocolRAM.program w ps)).Exec m final ((4+10*len)+clock ps) ∧
      (∀x : Fin (2^k),Reads (gatedBank (k:=k) out.base H G M A.degree outputBits x) (fun h g=>(physical h g).winner x) M final) ∧
      (∀(x : Fin (2^k)) (j : Fin (2*A.cap)),Reads (markedBank (k:=k) (cap:=A.cap) out.base H G M A.degree outputBits x j) (fun h g=>(physical h g).neighbor x j) M final) ∧
      Mounted {P with roster:=out} (hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding))) final G M ∧
      (∀z,z<romBase ∨ stop k H G M A.degree A.cap out.base≤z→final z=m z) ∧ CheapCode ((rom).seq (ProtocolRAM.program w ps)) :=
  from_published A native S ready groups hosts win P out romBase rowBits shapeBits outputBits act vals wire
    (fun h g x=>winners groups hosts win x h g) (true_win A groups hosts win) m rs geometry fit rf sep actTop winTop wireTop ids rankTop off ch aRead wRead sRead old

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare.ROM

end OAI
