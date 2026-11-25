import OAI.Hierarchy.DescentDatedTicketWords
import OAI.Hierarchy.DescentDatedGrainBank
import OAI.Hierarchy.DescentOrdinarySideProjection
import OAI.Hierarchy.DescentChronologicalGrains
import OAI.Hierarchy.DescentPackedOperandPublic

namespace OAI
/-! # The sixth registered operand field of an actual ordinary descent date -/
namespace Hierarchy.DescentDatedPublicGrain
open DescentSIMDLookup DescentDatedPriorOperand DescentCompiler ProtocolRAM
open DescentPriorOperandColumns DescentPackedOperand DescentPackedColony DescentOperandStateBanks
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

def dateCell (S : AtomSchedule) (b date : ℕ) (l : DescentDatedPriorOperand.Layout)
    (bound : amount S b date<2^(l.size+2)) : Cell (l.size+2) := ⟨amount S b date,bound⟩

def sideBanks (l : DescentDatedPriorOperand.Layout) (base : ℕ) (other : Fin l.jobs→Fin 5→Bank)
    (j : Fin l.jobs) (f : Fin 6) :=
  if h : f.val<5 then other j ⟨_,h⟩ else bank l base

@[simp] theorem bank_sixth (l : DescentDatedPriorOperand.Layout) (base : ℕ) (other : Fin l.jobs→Fin 5→Bank) (j : Fin l.jobs) :
    sideBanks l base other j 5=bank l base := rfl

theorem registered_sixth (l : DescentDatedPriorOperand.Layout) (base : ℕ) (other : Fin l.jobs→Fin 5→Bank) (grain : Cell (l.size+2))
    (s : Fin l.jobs→Fin l.hosts→Fin l.groups→Side l.size) (j : Fin l.jobs) {w : ℕ} (m : Memory w) :
    DescentPackedColony.Reads (sideBanks l base other j 5) (fun h g=>(withGrain grain (s j h g)).digits 5)
      l.lanes (image l base grain m) :=
  row_read l base grain m

/-- The complete six-column read on the output of the one shared literal
program, preserving all five earlier columns at their actual row addresses. -/
theorem registered_sides (l : DescentDatedPriorOperand.Layout) (base : ℕ) (other : Fin l.jobs→Fin 5→Bank)
    (grain : Cell (l.size+2)) (s : Fin l.jobs→Fin l.hosts→Fin l.groups→Side l.size)
    {w : ℕ} (m : Memory w)
    (before : ∀j f,(other j f).base+l.rows≤base)
    (previous : ∀j f,DescentPackedColony.Reads (other j f) (fun h g=>(s j h g).digits f.castSucc) l.lanes m) :
    ∀j f,DescentPackedColony.Reads (sideBanks l base other j f) (fun h g=>(withGrain grain (s j h g)).digits f)
      l.lanes (image l base grain m) := by
  intro j f
  refine Fin.lastCases (registered_sixth l base other grain s j m) (fun i=>?_) f
  intro p
  have early : (other j i).base+(row l.hosts l.groups l.lanes p).val<base :=
    (Nat.add_lt_add_left (row l.hosts l.groups l.lanes p).isLt _).trans_le (before j i)
  have hold:=frame l base grain m _ (Or.inl early)
  have eqn : sideBanks l base other j i.castSucc=other j i := by
    simp only [sideBanks,Fin.val_castSucc,dite_eq_left i.isLt]
  have preserve (a : Side l.size) : (withGrain grain a).digits i.castSucc=a.digits i.castSucc := by
    fin_cases i <;> rfl
  simp only [eqn,preserve]
  exact hold.trans (previous j i p)

section Chronological
open DescentSixParty DescentSixParty.Chronology
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {S : AtomSchedule}
  {price ε u : ℝ} {k wire hist i₀ i i₂ z₀ z z' z₂ D₀ D D' D₂ : ℕ}
  {W₀ W W₂ : MarkedWorld F d P bits}
  {first : Reached W₀ G price ε S k i₀ z₀ D₀ wire hist}
  {current : Reached W G price ε S k i z D wire hist}
  {last : Reached W₂ G price ε S k i₂ z₂ D₂ wire hist}
  {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
  {n : Normalize ((T.result he).state c)}
  {target : Reached n.result G price ε S k (i+1) z' D' wire hist}

/-- A genuine selected successor records both the width of every split edge
and the reduction of its stage multiplier. These yield the same p-word count. -/
theorem on_cut (ticket : OrdinaryLink current he T c n target)
    (before : Path first current) (after : Path target last) {path : Path first last}
    (cut : (before.ordinary ticket).append after=path) {p : ℕ} (hp : 0<p) (dates : path.GrainDates p) :
    T.z=amount S G.b i*p ∧ z'*G.b=T.z ∧ Normalize.CutsEqual T.z n ∧
      T.z/p=amount S G.b i ∧ (z'*G.b)/p=amount S G.b i := by
  have measured : T.z=amount S G.b i*p :=
    (ticket.grain_on_cut before after cut dates).trans
      ((bits_per_bundle S G.b p i).trans (Nat.mul_comm ..))
  have next : z'*G.b=T.z := ticket.grainStep.symm.trans (ticket.quantum.trans current.grain).symm
  have norm : Normalize.CutsEqual T.z n := by rw [ticket.quantum];exact ticket.cuts
  have quot : T.z/p=amount S G.b i := by rw [measured,Nat.mul_div_cancel _ hp]
  exact ⟨measured,next,norm,quot,by rw [next,quot]⟩

/-- In a parent with `reps` normalized child edges the original p-chunk
bound is precisely the bound consumed by the marked operand resolver. -/
theorem cut_chunks (q grain p reps : ℕ) (hp : 0<p) (scaled : q=grain*p) :
    (reps*q)/p=reps*grain := by rw [scaled,←Nat.mul_assoc,Nat.mul_div_cancel _ hp]

end Chronological

/-- Reading the shared digit yields a quotient and a remainder on a marked
edge, and leaves the old chunk untouched on an unsplit edge. -/
theorem resolve_public {k : ℕ} (chunk peer start grain : Cell (k+2)) :
    resolve (Public.fragment true peer start chunk grain)=
      .cable peer.val (start.val+chunk.val/grain.val) (chunk.val%grain.val) ∧
    resolve (Public.fragment false peer start chunk grain)=.cable peer.val start.val chunk.val :=
  ⟨rfl,rfl⟩

end
end Hierarchy.DescentDatedPublicGrain

namespace Hierarchy.DescentPackedOperand.Public
open DescentColonies DescentSixParty DescentSharedCableNames DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Stage.Host J V k↪ℕ)

omit [Fintype P] in
theorem unsplit_dated {b : ℕ} (e : W.graph.Edge) (j : Fin (A.grainCount e)) (target : Bool)
    (slotRoom : A.degree≤2^(b+2)) (wireRoom : A.cap≤2^(b+2)) (chunk : Cell (b+2))
    (bound : DescentDatedPublicGrain.amount S G.b i<2^(b+2)) :
    let grain : Cell (b+2):=⟨DescentDatedPublicGrain.amount S G.b i,bound⟩
    let first:=endpoint A native S ready names target ⟨e,⟨0,Nat.zero_lt_of_lt j.isLt⟩⟩
    let observed:=endpoint A native S ready names target ⟨e,j⟩
    resolve (fragment false (short first.neighbor slotRoom) (short first.wire wireRoom) chunk grain)=
      .cable first.neighbor.val first.wire.val chunk.val ∧
        first.wire.val+j.val=observed.wire.val := by
  intro grain
  exact unsplit A native S ready names e j target slotRoom wireRoom chunk grain

end
end Hierarchy.DescentPackedOperand.Public

namespace Hierarchy.DescentOrdinarySiblingSerial
open DescentPackedOperand DescentSIMDLookup
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
open private physicalBase physicalKey from OAI.Hierarchy.DescentOrdinarySiblingSerial
open private firstGrain from OAI.Hierarchy.DescentPackedOperandPublic

variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪DescentHostDirectory.Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {age i : ℕ} {price ε : ℝ}
variable (A : GroupStage (PhysicalRename.rankedWorld
  (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
  (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site)) G price ε J V age)
local notation "baseWorld" => physicalBase W G pick z hz fit pack p key flag k g q old picked affected
local notation "edgeKey" => physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site
local notation "rep" => repetitions W G pick z hz fit pack p key flag k g q
local notation "atPiece" => piece W G pick z hz fit pack p key flag k g q old picked affected
local notation "paid" => core_piece W G edge pair pick z hz fit pack p key flag k g q old picked affected site
local notation "ord" => @originalId (baseWorld).graph.Edge (baseWorld).graph.finiteEdge

set_option maxHeartbeats 4000000 in
/-- The measured parent bundle and the compiled observation use the same marked sibling index. -/
theorem operand_piece_dated [Fintype P] {b : ℕ} (qpos : 0<q) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : Stage.Host J V age↪ℕ) (target : Bool) (u : {a : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Edge // a ∈ (coalesced (W.selected G pick z hz fit pack p) key flag k g).core})
    (chunk : Cell (b+2)) (wordWidth : ℕ) (hp : 0<wordWidth)
    (field : DescentDatedPublicGrain.amount S G.b i<2^(b+2))
    (cut : q=DescentDatedPublicGrain.amount S G.b i*wordWidth)
    (occurs : chunk.val<(rep u.val*q)/wordWidth)
    (slotRoom : A.degree≤2^(b+2)) (wireRoom : A.cap≤2^(b+2)) :
    let grain : Cell (b+2):=⟨DescentDatedPublicGrain.amount S G.b i,field⟩
    let positive : 0<grain.val:=DescentDatedPublicGrain.amount_pos S G.base_pos i
    let within : chunk.val<rep u.val*grain.val:=by
      rw [DescentDatedPublicGrain.cut_chunks q grain.val wordWidth (rep u.val) hp cut] at occurs
      exact occurs
    let j : Fin (rep u.val):=⟨chunk.val/grain.val,(Nat.div_lt_iff_lt_mul positive).2 within⟩
    let zero : Fin (rep u.val):=⟨0,Nat.zero_lt_of_lt j.isLt⟩
    let fine (t : Fin (rep u.val)) : Stage.Grain A:=firstGrain baseWorld site edgeKey A (atPiece u t) (paid u t)
    let first:=Public.endpoint A ord S ready names target (fine zero)
    let actual:=Public.endpoint A ord S ready names target (fine j)
    resolve (Public.fragment true (Public.short actual.neighbor slotRoom) (Public.short first.wire wireRoom) chunk grain)=
      .cable actual.neighbor.val actual.wire.val (chunk.val%grain.val) := by
  intro grain positive within
  exact operand_piece W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qpos
    S ready names target u chunk grain positive within slotRoom wireRoom

end
end Hierarchy.DescentOrdinarySiblingSerial

end OAI
