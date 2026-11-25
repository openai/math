import OAI.Hierarchy.DescentTerminalResetDatedFields
import OAI.Hierarchy.DescentResetControlCuts

namespace OAI
/-! The physical operand pass reads the field dictionary and the signed pages
in precisely the memory in which the two native renderers mounted them. -/
namespace Hierarchy.DescentResetWindowTail
open DescentNextSignedWindow ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

theorem fields_frame {X K b M w : ℕ} (base D cap H G : ℕ)
    (header : Fin X→Fin K→Expr) (rank : Fin X→Fin 3→Fin K→Expr) (m : Memory w)
    (early : ∀x j,(header x j).Fits w base) (prior : ∀x p j,(rank x p j).Fits w base)
    (space : endAddress base X cap b M H G<2^w) (i : ℕ) (hi : i<next base b M) :
    memory base X D cap b M H G header rank m i=DescentResetFieldAssembler.memory base b M m i := by
  have bounds:=lower base X cap b M H G
  have assembled:=DescentResetFieldAssembler.any base header rank m early prior (bounds.trans_lt space)
  have placed:=Native.All.any (next base b M) (D:=D)
    (DescentResetWindowTail.fields base b M cap header rank) (DescentResetFieldAssembler.memory base b M m)
    (fun x _=>assembled.2.1 x) space
  exact placed.2.1 i (.inl hi)

end
end Hierarchy.DescentResetWindowTail

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "plan" => (v).linkedRankInputs u.sectors ((v).sheetsStart b)
local notation "book" => (v).rankBook plan b
local notation "render" => (v).renderFromRanks plan b
local notation "rankMem" m:arg => (book).memory (((v).rankPortPhase b w).image m)

theorem operand_render_frame (ok : u.Ready) (actorMem : Memory w) (i : ℕ)
    (hi : i<(A).rendered ((v).fieldsEnd b)) :
    u.operandEntry ok actorMem i=(v).renderMemory render b u.degree (rankMem (u.candidateEntry ok actorMem)) i := by
  let ranked:=rankMem (u.candidateEntry ok actorMem)
  let rendered:=(v).renderMemory render b u.degree ranked
  let controlled:=((v).controlPhase b u.bank w).image rendered
  have cuts:=(v).control_address_bounds b
  have prior : i<(v).controlFloor b := hi
  have floorFits : (v).operandFloor b<2^w := cuts.2.2.2.trans_lt ok.full
  have latest := (v).operand_order b
  have extent : (v).operandStart b<2^w :=
    (((latest.1.trans latest.2).trans ((v).final_ge b)).trans_lt ok.full)
  have start : (v).operandFloor b ≤ (v).keepBase b := by
    change _ ≤ (v).setup.endAddress ((v).operandFloor b)
    rw [(v).setup.affine]
    exact Nat.le_add_right ..
  let setup:=((v).setup.code ((v).operandFloor b) w u.bank u.laws).image controlled
  have mounted := (v).setup.any ((v).operandFloor b) controlled u.bank u.laws ok.placed
    (((v).keep_before b).trans_lt extent)
  have kept := (v).keep_any b setup extent
  have registers := (v).controlRegisters.any ((v).controlFloor b) ((v).actor.scene ((v).middle.stop b))
    u.bank.count u.bank.inverse rendered ok.controls floorFits
  have below:=prior.trans_le cuts.2.2.1
  exact (kept.frame i (.inl (below.trans_le start))).trans
    ((mounted.frame i (.inl below)).trans (registers.2 i (.inl prior)))

theorem operand_fields_frame (ok : u.Ready) (actorMem : Memory w) (i : ℕ)
    (hi : i<(v).fieldsEnd b) :
    u.operandEntry ok actorMem i=DescentResetFieldAssembler.memory ((v).rankEnd b) (v).assemblerBits
      (A).lanes (rankMem (u.candidateEntry ok actorMem)) i := by
  let ranked:=rankMem (u.candidateEntry ok actorMem)
  have bounds:=(v).control_address_bounds b
  have endAt:=(v).render_end b ok.width
  have top:=(DescentResetWindowTail.lower ((v).rankEnd b) (A).blocks (A).capacity
    (v).assemblerBits (A).lanes (A).hosts (A).groups).trans endAt.le
  have renderSpace : (A).rendered ((v).fieldsEnd b)<2^w :=
    (bounds.2.2.1.trans bounds.2.2.2).trans_lt ok.full
  have rankSpace : (book).endAddress<2^w :=
    ((Nat.le_add_right ((v).rankEnd b) _).trans top).trans_lt renderSpace
  have before : ∀x j,((plan).header x j).Fits w ((v).rankEnd b) := by
    intro x j
    obtain ⟨h,i,k,o⟩:=(book).ordered
    exact ProtocolRAMGeneratedWrite.fits_mono _ (((h.trans i).trans k).trans o) (ok.ranks.header x j)
  have restored:=DescentResetWindowTail.fields_frame ((v).rankEnd b) u.degree (A).capacity (A).hosts (A).groups
    (plan).header (book).finalRank ranked before ((book).finalRank_fits ok.ranks rankSpace) (endAt.le.trans_lt renderSpace) i hi
  exact (u.operand_render_frame ok actorMem i (hi.trans_le top)).trans restored

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
