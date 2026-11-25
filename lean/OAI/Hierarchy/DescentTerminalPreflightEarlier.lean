import OAI.Hierarchy.DescentTerminalPreflightMaskRoom
import OAI.Hierarchy.DescentTerminalPublicSortBook
import OAI.Hierarchy.DescentTerminalPublicIdentity
import OAI.Hierarchy.DescentTerminalSiteControlBanks

namespace OAI
/-! # The complete earlier-address certificate for the genuinely paid terminal placement -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalCompiledPrefix DescentTerminalRowArena
open DescentTerminalEmitter.Compact DescentTerminalPrimitiveArena DescentTerminalVertexFields
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (x : Spec) (begin_ rom q piece W K codes front : ℕ) (peer : Bank)
    (priorCables : Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (total modulo homes : Bank) (boundary : ℕ)
variable (cfg : DescentTerminalCompiledPrefix.Shape) (V : Home.Format)
    (other : AddressPlan.Input) (T : AddressPlan.RouteSources.Tables) (vertices B : ℕ)
local notation "mask_" => x.maskBase begin_
local notation "R_" => x.channels begin_
local notation "C_" => AddressPlan.meter V R_ mask_
local notation "base_" => AddressPlan.afterMeter V cfg R_ mask_
local notation "grain" => W*piece
local notation "raw" => cfg.terminal.plane.rawRows
local notation "candidate_" => DescentTerminalPaidBoot.candidate K W q piece codes raw front
local notation "id_" => front+DescentTerminalPaidBoot.total K W q piece codes raw
local notation "J_" => x.chipInput begin_ rom q grain peer priorCables total modulo homes boundary cfg other
local notation "row_" => AddressPlan.rowArena cfg J_ base_
local notation "cols_" => ScalarLiterals.columns q V.roles V.privateWords V.nodes V.addresses grain
                          vertices W B cfg.terminal.pool (T.columns row_ (J_).sources)

/-- Before installing the scalar lookup values, the route stage already points
to the real incoming public-sort and candidate banks. -/
def reachedRoutes : AddressPlan.Input :=
  { J_ with
    publicTapes := DescentTerminalPublicIdentity.controls (row_).order.sorted id_ cfg.packets
    candidate := candidate_
    sources := T.columns row_ (J_).sources }

local notation "routes_" => x.reachedRoutes begin_ rom q piece W K codes front peer priorCables total modulo homes
                               boundary cfg V other T

/-- Only the archived private-counter layout is inherited from `other`. Both
scatter sources, the public and candidate banks, and all literals have concrete addresses. -/
def reachedInput : AddressPlan.Input :=
  {routes_ with sources:=cols_}

local notation "I_" => x.reachedInput begin_ rom q piece W K codes front peer priorCables total modulo homes
                         boundary cfg V other T vertices B

/-- The paid-branch interpreter applies these very scalar and route programs to the
43-column layout. Every incoming header reference is attained, hence has no ROM index. -/
def reachedLiterals (hq : 0<q) : Literals (I_).sources :=
  ScalarLiterals.data q V.roles V.privateWords V.nodes V.addresses grain vertices W B
    cfg.terminal.pool hq (routes_).sources (T.value (fun _ _=>0))

theorem reached_placed :
    { routes_ with sources := cols_ } = I_ := rfl

open DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open DescentTerminalHeaderDraft DescentTerminalDenseHeader DescentTerminalDenseHeaderBoot
open DescentTerminalDenseWindow
local notation "arena₀" => x.draft begin_ total modulo homes boundary
local notation "fixed₀" => literals (x.literalBase begin_) x.paidRows
local notation "tab₀" => DescentTerminalHeaderDraft.output arena₀

/-- The exact two pass lengths, idle symbol, and both original five-word input
layouts of the same later terminal program. -/
theorem reached_headers (rem whole idx ctl : Bank) :
    Uses fixed₀ tab₀ (I_).sources ∧ (I_).indexEvents=cfg.terminal.rows ∧
      (I_).formatEvents=cfg.terminal.rows ∧
      (I_).blank=(formatIndex q grain (DescentTerminalScalarPadded.blank q grain)).val ∧
      inputBanks (DescentTerminalDenseHeaderBoot.layout q grain rom
        (x.cables begin_ peer priorCables).printer.output rem whole idx ctl)=(I_).cable ∧
      inputBanks (DescentTerminalDenseHeaderBoot.layout q grain rom
        (x.publicWidths begin_).widthLayout.output rem whole idx ctl)=(I_).exterior := by
  have prior := x.chip_uses begin_ rom q grain peer priorCables total modulo homes boundary cfg other
  have routed_ := routed fixed₀ tab₀ prior T row_
  exact ⟨AddressPlan.HeaderColumns.scalar fixed₀ tab₀ routed_ _ _ _ _ _ _ _ _ _ _,rfl,rfl,rfl,rfl,rfl⟩

theorem earlier {w : ℕ} (paid oldActors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid oldActors priorCables peer total modulo homes boundary)
    (romTop : rom+DescentTerminalDenseHeaderBoot.extent q grain≤x.literalBase begin_)
    (full : front+DescentTerminalPublicIdentity.total K W q piece codes raw cfg.packets≤ mask_)
    (end_ : AddressPlan.last V cfg I_ R_ mask_ < 2^w) :
    AddressPlan.Earlier cfg I_ base_ (C_).layout w := by
  obtain ⟨s0,s1,s2,s3,s4⟩ := AddressPlan.stages cfg I_ base_
  have arena : base_≤(row_).finish := (row_).start_le 22
  have localRoom : base_<2^w := arena.trans_lt
    (s0.trans_lt (s1.trans_lt (s2.trans_lt (s3.trans_lt (s4.trans_lt end_)))))
  have rawBefore : mask_≤base_ := by change mask_≤ mask_+_+_+_+_+3;omega
  obtain ⟨a,b,c,d,e,f,g,h,i⟩ := x.layers begin_
  have toMask : x.cohortEnd begin_≤ mask_ := by omega
  have toBook : x.bookEnd begin_≤base_ := by omega
  have toWeights : x.bookBegin begin_≤base_ := by omega
  have toDir : (x.controls begin_).finish≤base_ := by omega
  have toOrig : base_≤AddressPlan.takeOff cfg I_ base_ := arena.trans (s0.trans s1)
  have low : x.literalBase begin_≤AddressPlan.takeOff cfg I_ base_ := by omega
  have fit (a : Bank) (limit : a.base+a.size≤base_) : a.Fits w base_ :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (limit.trans_lt localRoom),limit⟩
  have bank (j : Fin 6) := x.book_banks begin_ j
  have masks := x.mask_before begin_ cfg V localRoom
  have ports := x.ports_before begin_ rom q grain peer priorCables total modulo homes boundary cfg other romTop
  have originals := x.priced_earlier begin_ rom q grain peer priorCables total modulo homes boundary cfg other
    T base_ V.roles V.privateWords V.nodes V.addresses grain vertices W B cfg.terminal.pool rawBefore
  have seed : id_+pad cfg.packets≤ mask_ := by
    change front+(_+pad cfg.packets)≤ mask_ at full
    simpa only [Nat.add_assoc] using full
  constructor
  · exact ⟨fun j=>fit _ ((bank j).1.trans toBook),fun j=>fit _ ((bank j).2.trans toWeights),
      fit _ (boot.total.trans (toMask.trans rawBefore)),fit _ (boot.modulo.trans (toMask.trans rawBefore)),
      fit _ (boot.homes.trans (toMask.trans rawBefore))⟩
  · intro j
    exact (DescentTerminalControlProgram.early_before (x.controls begin_) (x.parts begin_)
      (bank 1).1 j).trans (toDir.trans arena)
  · exact fun j=>⟨((masks.1 j).1).trans arena,((masks.1 j).2).trans arena⟩
  · exact masks.2.trans arena
  · exact originals
  · exact AddressPlan.public_controls_earlier cfg I_ base_ id_ (seed.trans rawBefore)
  · exact fun j=>(ports.1 j).trans low
  · exact fun j=>(ports.2 j).trans low
  · change (candidate_).base+(candidate_).size≤AddressPlan.takeOff cfg I_ base_
    rw [DescentTerminalPaidBoot.candidate_end]
    exact (show id_≤ mask_ from (Nat.le_add_right ..).trans seed).trans (rawBefore.trans toOrig)

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
