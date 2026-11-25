import OAI.Hierarchy.DescentDatedVenueSources
import OAI.Hierarchy.DescentPackedMatchPrepare
import OAI.Hierarchy.DescentSortedRosterTariff
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Simultaneous native mounting of the true ranked stage's complete matching inputs -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare
open DescentSixParty DescentStageEdgeReceipt DescentGroupPeerOrder DescentSIMDLookup DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i a s M H G w : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {T : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W T price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J↪Fin G) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
local notation "rank" => groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "physical" => spread groups hosts (terrain (short:=s) A native S ready (cableNames k rank) win (rotor A rank))
local notation "rows" => H*chunks G M

local notation "cables" => signed A native S ready groups hosts
local notation "actor" => actors A groups hosts
local notation "values" => winners groups hosts win

theorem native_published (published : Fin H→Fin G→Fin (2^k)→Cell a)
    (liveWin : ∀u,published (hosts (A.pos u).2) (groups (A.pos u).1) (A.block u)=win (A.pos u) (A.block u)) (C : Chart k A.cap) (R : DescentSortedRoster.Chart) (P : Ports A.degree) (out : Bank) (bits : ℕ) (m : Memory w)
    (rs : Fin H→Fin A.degree→Option (Fin H))
    (mem : ∀h j,j∈(List.ofFn (rs h)).filterMap id ↔ ∃v u : V,h=hosts v ∧ j=hosts u ∧ v∈A.near u)
    (fit : Room C A.degree a s M H G w out.base) (source : Frame C actor (fun x h g=>published h g x) cables s M m)
    (rf : DescentSortedRoster.Room R A.degree H w out.base) (raw : DescentSortedRoster.Raw R rs m)
    (old : Mounted P rs m G M) (left : ∀j,(P.ids j).base+rows≤out.base) (off : P.offsets.base+H≤out.base) (ch : P.chunks.base+rows≤out.base) :
    let ps:=passes C R out.base H G M A.degree;let final:=ProtocolRAM.result ps m
    (ProtocolRAM.program w ps).Exec m final (ProtocolRAM.clock ps) ∧
      (∀x : Fin (2^k),Reads (gatedBank (k:=k) out.base H G M A.degree bits x) (fun h g=>(physical h g).winner x) M final) ∧
      (∀(x : Fin (2^k)) (j : Fin (2*A.cap)),Reads (markedBank (k:=k) (cap:=A.cap) out.base H G M A.degree bits x j) (fun h g=>(physical h g).neighbor x j) M final) ∧
      Mounted {P with roster:=out} (hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding))) final G M ∧
      (∀z<out.base,final z=m z) ∧ CheapCode (ProtocolRAM.program w ps) := by
  obtain ⟨run_,gate,chip,p,old,cheap⟩:=run C R P out bits m actor (fun x h g=>published h g x) cables rs fit source rf raw old left off ch
  have gateEq (x : Fin (2^k)) : (fun h g=>Stage.gated (s:=s) (actor h g) x (published h g x))=(fun h g=>(physical h g).winner x) := by
    funext h g
    by_cases live : ∃z : J×V,groups z.1=g ∧ hosts z.2=h
    · simp only [actors,spreadField,spread,dite_eq_left live,terrain]
      by_cases active : ∃u,A.pos u=live.choose ∧ A.block u=x
      · obtain ⟨u,hu,hx⟩:=active
        have eqn:=liveWin u
        rw [hu,hx,live.choose_spec.1,live.choose_spec.2] at eqn
        rw [eqn]
      · simp only [Stage.gated,DescentActorRaster.actor_read,ite_eq_right active,Nat.zero_ne_one,ite_false]
    · simp [actors,spreadField,spread,live,blank,Stage.gated,digit]
  have chipEq (x : Fin (2^k)) (j : Fin (2*A.cap)) : (fun h g=>Stage.marked s (cables x j h g))=(fun h g=>(physical h g).neighbor x j) := by
    funext h g
    by_cases live : ∃z : J×V,groups z.1=g ∧ hosts z.2=h <;> simp [signed,spreadField,spread,live,terrain,blank,Stage.marked]
  exact ⟨run_,fun x=>gateEq x ▸ gate x,fun x j=>chipEq x j ▸ chip x j,issued_roster A hosts rs mem ▸ p,old,cheap⟩

theorem true_win (u : W.graph.Site) : values (A.block u) (hosts (A.pos u).2) (groups (A.pos u).1)=win (A.pos u) (A.block u) := by
  have live : ∃ z : J×V, groups z.1 = groups (A.pos u).1 ∧ hosts z.2 = hosts (A.pos u).2 :=
    ⟨A.pos u, rfl, rfl⟩
  rw [winners, spreadField, dite_eq_left live]
  exact congrArg (fun z => win z (A.block u))
    (Prod.ext (groups.injective live.choose_spec.1) (hosts.injective live.choose_spec.2))

theorem native_inputs (C : Chart k A.cap) (R : DescentSortedRoster.Chart) (P : Ports A.degree) (out : Bank) (bits : ℕ) (m : Memory w)
    (rs : Fin H→Fin A.degree→Option (Fin H))
    (mem : ∀h j,j∈(List.ofFn (rs h)).filterMap id ↔ ∃v u : V,h=hosts v ∧ j=hosts u ∧ v∈A.near u)
    (fit : Room C A.degree a s M H G w out.base) (source : Frame C actor values cables s M m)
    (rf : DescentSortedRoster.Room R A.degree H w out.base) (raw : DescentSortedRoster.Raw R rs m)
    (old : Mounted P rs m G M) (left : ∀j,(P.ids j).base+rows≤out.base) (off : P.offsets.base+H≤out.base) (ch : P.chunks.base+rows≤out.base) :
    let ps:=passes C R out.base H G M A.degree;let final:=ProtocolRAM.result ps m
    (ProtocolRAM.program w ps).Exec m final (ProtocolRAM.clock ps) ∧
      (∀x : Fin (2^k),Reads (gatedBank (k:=k) out.base H G M A.degree bits x) (fun h g=>(physical h g).winner x) M final) ∧
      (∀(x : Fin (2^k)) (j : Fin (2*A.cap)),Reads (markedBank (k:=k) (cap:=A.cap) out.base H G M A.degree bits x j) (fun h g=>(physical h g).neighbor x j) M final) ∧
      Mounted {P with roster:=out} (hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding))) final G M ∧
      (∀z<out.base,final z=m z) ∧ CheapCode (ProtocolRAM.program w ps) :=
  native_published A native S ready groups hosts win (fun h g x=>values x h g) (true_win A groups hosts win)
    C R P out bits m rs mem fit source rf raw old left off ch

theorem clock_bound {D cap : ℕ} (C : Chart k cap) (R : DescentSortedRoster.Chart) (base H G M : ℕ) :
    clock (passes C R base H G M D)≤4+(H*D)*(2*(100*(D+1)^3)+4)+4+(2^k+2^k*(2*cap))*(4+54*(H*chunks G M)) := by
  apply (ticks C R base H G M D).trans
  rw [Nat.mul_comm 54]
  gcongr
  exact DescentSortedRoster.code_work R D H

private theorem column_names (w n base : ℕ) (es : List Expr) (bound : ∀e∈es,e.work≤25) :
    DescentStaticWordColumn.names (ProtocolRAM.program w (ProbeStage.Native.columns n base es))≤15+es.length*111 := by
  induction es generalizing base with
  | nil=>change DescentStaticWordColumn.names (scan w 0 0 (.lit 0))≤15;rw [DescentStaticWordColumn.names_scan];rfl
  | cons e es ih=>
    have old:=ih (base+n) (fun t ht=>bound t (List.mem_cons_of_mem _ ht))
    have head:=bound e (List.mem_cons_self ..)
    simp only [ProbeStage.Native.columns,ProtocolRAM.program,Pass.procedure,DescentStaticWordColumn.names_seq,
      DescentStaticWordColumn.names_scan,List.length_cons,Nat.succ_mul es.length]
    omega

theorem code_names {D cap : ℕ} (C : Chart k cap) (R : DescentSortedRoster.Chart) (base H G M w : ℕ) :
    DescentStaticWordColumn.names (ProtocolRAM.program w (passes C R base H G M D))≤26+400*(D+1)^3+(2^k+2^k*(2*cap))*111 := by
  have cs:=column_names w (H*chunks G M) (fieldBase base H D) (List.ofFn (expr C)) (fun e member=>by obtain ⟨j,rfl⟩:=List.mem_ofFn.mp member;exact work_expr C j)
  rw [List.length_ofFn] at cs
  simp only [passes,ProtocolRAM.program,Pass.procedure,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan]
  have fee:=DescentSortedRoster.code_work R D H
  omega

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare

end OAI
