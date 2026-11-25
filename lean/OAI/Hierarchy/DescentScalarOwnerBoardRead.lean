import OAI.Hierarchy.DescentScalarOwnerEvidence
import OAI.Hierarchy.DescentScalarActorPublisherROM
import OAI.Hierarchy.DescentGroupPeerOrder
import OAI.Hierarchy.DescentIssuedOwnerBoard

namespace OAI
/-! # The actor publisher consumes the old owner board and its issued six headed rows -/
namespace Hierarchy.DescentScalarVenueMask.Stage
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage DescentSixParty DescentStageEdgeReceipt
open DescentGroupPeerOrder DescentSharedCableNames DescentPackedColony DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (groups : J↪Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a) (profile : ℕ) (lay : Bool)
local notation "R"=>2^k
local notation "D"=>A.degree
local notation "signedWidth"=>2*A.cap
local notation "rank"=>groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "next"=>rotor A rank
local notation "panel"=>terrain (short:=short) A native S ready (cableNames k rank) win next
local notation "near"=>hostRoster A (hosts.trans Fin.valEmbedding)
local notation "adj"=>hostRotor hosts near
local notation "original"=>spread groups hosts panel
local notation "act"=>Prepare.actors A groups hosts
local notation "key"=>tokens (short:=short) A native S ready rank win profile lay groups hosts

def board (h : Fin H) (g : Fin Z) :=Owners.render R D signedWidth short A.cap profile (Owners.register lay (original h g))
local notation "old"=>board (short:=short) A native S ready groups hosts win profile lay

def sixHeads (h : Fin H) (g : Fin Z) :=Owners.report R D signedWidth short A.cap profile (Owners.register lay (original h g))
  (encode _ (D+1) (Owners.registers old adj h g))
local notation "six"=>sixHeads (short:=short) A native S ready groups hosts win profile lay

theorem rows_at (z : J×V) : Owners.registers old adj (hosts z.2) (groups z.1)=registerRows (short:=short) A native S ready rank win profile lay z:=by
  funext j;induction j using Fin.cases with
  | zero=>simp [Owners.registers,registerRows,board,spread_hit]
  | succ t=>
    rcases z with ⟨g,v⟩;simp only [Owners.registers,registerRows,Fin.cases_succ]
    have good : ∃u,hosts u=hosts v:=⟨v,rfl⟩
    rw [hostRotor,dite_eq_left good,hosts.injective good.choose_spec,rotor_group]
    cases q:near v t with
    | none=>rfl
    | some y=>
      simp only [Option.map_some,Option.elim_some,board]
      rw [spread_hit groups hosts panel (g,y)]

private theorem all_zero {r : ℕ} (x : Fin r) : (encode 1 r).symm 0 x=0:=by
  rw [show (encode 1 r).symm 0=fun _=>0 from (encode 1 r).symm_apply_eq.mpr (by
    apply Fin.ext;change 0=(finFunctionFinEquiv (fun _ : Fin r=>(0:Cell 1))).val;simp)]

theorem published_eq (slots : ℕ) (x : Fin R) (s : Fin (1+A.cap*6)) (h : Fin H) (g : Fin Z) :
    Publisher.ticket («D»:=D) (d:=short) (slots:=slots) (raw:=2^(k+1)*slots) (x,s) (act h g) (old h g) (six h g)=key slots x s h g:=by
  by_cases occupied : ∃z:J×V,groups z.1=g ∧ hosts z.2=h
  · obtain ⟨z,rfl,rfl⟩:=occupied
    have here : ∃t:J×V,groups t.1=groups z.1 ∧ hosts t.2=hosts z.2:=⟨z,rfl,rfl⟩
    have uniq:(here).choose=z:=Prod.ext (groups.injective (here).choose_spec.1) (hosts.injective (here).choose_spec.2)
    simp only [tokens,Prepare.spreadField,dite_eq_left here,uniq,sixHeads,board,rows_at,reports,spread_hit]
  · have miss : act h g=0:=by simp [Prepare.actors,Prepare.spreadField,occupied]
    simp only [tokens,miss,Publisher.ticket,Prepare.spreadField,dite_eq_right occupied]
    cases tag:finSumFinEquiv.symm s with
    | inl u=>simp [oldTicket,all_zero]
    | inr j=>simp [newTicket,all_zero]

/-- Both operand arrays are exactly the outputs of `Owners.Board.run` and
`Owners.run`. The ghost board may contain a layout flag; the actor mask
clears it before the short path and the low key reach the recipient. -/
theorem publish (mask current heads : Bank) (slots romBase out rowBits : ℕ) (m : Memory w)
    (mfit : mask.Fits w romBase) (ofit : current.Fits w romBase) (bfit : heads.Fits w romBase)
    (mroom : H*chunks Z M≤ mask.size) (oroom : H*chunks Z M≤current.size) (broom : H*chunks Z M≤heads.size)
    (occupied : Reads mask act M m) (oldSite : Reads current old M m) (parties : Reads heads six M m)
    (gap : romBase+Publisher.ROM.size R D A.cap short M≤out) (space : out+2*(R*(1+A.cap*6))*(H*chunks Z M)<2^w) :
    let raw:=2^(k+1)*slots;let f:=Publisher.ROM.entries R D A.cap short slots raw;let unit:=Publisher.ROM.unit R D A.cap short
    let C : Publisher.Chart R A.cap :=Publisher.ROM.chart D short slots raw M romBase mask current heads;let ps:=Publisher.passes C H Z M out
    let mid:=DescentPackedZip.Book.image f unit M romBase m;let final:=result ps mid
    ((DescentPackedZip.Book.install f unit M w romBase).seq (program w ps)).Exec m final ((4+10*Publisher.ROM.size R D A.cap short M)+clock ps) ∧
    (∀x s,Reads (Publisher.bank H Z M out rowBits ((0:Fin 2),x,s)) (fun h g=>pathCode (key slots x s h g)) M final) ∧
    (∀x s,Reads (Publisher.bank H Z M out rowBits ((1:Fin 2),x,s)) (fun h g=>localCode (key slots x s h g)) M final) ∧
    (∀a,a<romBase ∨ out+2*(R*(1+A.cap*6))*(H*chunks Z M)≤a→final a=m a) ∧ CheapCode ((DescentPackedZip.Book.install f unit M w romBase).seq (program w ps)):=by
  intro raw f unit C ps mid final
  obtain ⟨setup,fixed,oldMem,cheap⟩:=Publisher.ROM.mounted (r:=R) (cap:=A.cap) («D»:=D) (d:=short) (slots:=slots) (raw:=raw) romBase out mask current heads m act old six gap ((Nat.le_add_right ..).trans_lt space) mfit ofit bfit mroom oroom broom occupied oldSite parties
  obtain ⟨run,read,frame,cheapP⟩:=Publisher.publish C act old six out rowBits mid fixed space
  refine ⟨setup.then run,?_,?_,?_,cheap_seq cheap cheapP⟩
  · intro x s;simpa [published_eq,Publisher.projection] using read ((0:Fin 2),x,s)
  · intro x s;simpa [published_eq,Publisher.projection] using read ((1:Fin 2),x,s)
  · intro j away;rcases away with low|high
    · exact (frame _ (.inl (low.trans_le ((Nat.le_add_right ..).trans gap)))).trans (oldMem _ (.inl low))
    · exact (frame _ (.inr high)).trans (oldMem _ (.inr (gap.trans ((Nat.le_add_right ..).trans high))))

end
end Hierarchy.DescentScalarVenueMask.Stage

end OAI
