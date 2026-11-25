import OAI.Hierarchy.DescentPhysicalPreviousFieldFrame
import OAI.Hierarchy.DescentResetSignedMemory

namespace OAI
/-! # Genuine selected candidate fields at the fresh input pitch of the operand LUT -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentPackedZip DescentResetFieldAssembler DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput) (s : v.OperandInputs)
local notation "A" => v.receiver
local notation "b" => v.assemblerBits
variable («meta» : Fin v.receiver.blocks→Fin v.receiver.candidates→Fin v.receiver.hosts→Fin v.receiver.groups→Meta)
    (offs : Fin v.receiver.blocks→Fin 3→Fin v.receiver.candidates→Fin v.receiver.hosts→Fin v.receiver.groups→Cell v.assemblerBits)

/-- The terminating field lookup sees source, target and parallel offset in its
native signed lane width. Its output conversion is performed in OperandFieldJoin.take. -/
def previousValue (i : Fin (A).fields) (j : Fin (2*(A).candidates))
    (h : Fin (A).hosts) (g : Fin (A).groups) : Cell (A).signedBits :=
  let slot : Fin 2×Fin (A).candidates:=finProdFinEquiv.symm j
  let x:=v.operandIndex s i
  (pointerField x.2.1).elim 0 fun f=>
    (field (decide (slot.1.val=1)) f («meta» x.1 slot.2 h g) (offs x.1 (atField f) slot.2 h g).val : Cell (A).signedBits)

private theorem literalZero {H G M bits w : ℕ} (m : Memory w) :
    Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell bits)) M m:=by
  intro row
  change (0:Word w)=(((finFunctionFinEquiv (fun i:Fin M=>if _ : row.2.val*M+i.val<G then (0:Cell bits) else 0)).val:ℕ):Word w)
  simp

/-- Read the field assembler that the dated program actually mounted. The
input words are the reached metadata and local ranks, including empty slots. -/
theorem previous_at_fields (r : v.RenderInputs) (base : ℕ) {w : ℕ} (m : Memory w)
    (width : (A).signedBits=b)
    (headFit : ∀x j,(r.meta x j).Fits w (v.rankEnd base))
    (rankFit : ∀x p j,(r.offsets x p j).Fits w (v.rankEnd base))
    (header : ∀x j,Source (r.meta x j) (fun h g=>raw b («meta» x j h g)) (A).lanes m)
    (rank : ∀x p j,Source (r.offsets x p j) (offs x p j) (A).lanes m)
    (small : ∀x j h g t,digits («meta» x j h g) t<2^b)
    (room : v.fieldsEnd base<2^w) (i : Fin (A).fields) (j : Fin (2*(A).candidates)) :
    (v.previous s r base i j).Fits w (v.fieldsEnd base) ∧
    Source (v.previous s r base i j) (v.previousValue s «meta» offs i j) (A).lanes
      (DescentResetFieldAssembler.memory (v.rankEnd base) b (A).lanes m) := by
  have written:=DescentResetFieldAssembler.run (v.rankEnd base) r.meta r.offsets m «meta» offs
    headFit rankFit header rank small room
  let x:=v.operandIndex s i
  let pair : Fin 2 × Fin (A).candidates := finProdFinEquiv.symm j
  have value : v.previousValue s «meta» offs i j = fun h g =>
      (pointerField x.2.1).elim (0 : Cell (A).signedBits) (fun f =>
        (field (decide (pair.1.val=1)) f («meta» x.1 pair.2 h g) (offs x.1 (atField f) pair.2 h g).val : Cell (A).signedBits)) := rfl
  rw [value]
  cases f : pointerField x.2.1 with
  | none=>
    simp only [previous,←show x=v.operandIndex s i from rfl,f,Option.elim_none]
    exact ⟨trivial,literalZero _⟩
  | some f₀=>
    have read:=written.2.2.1 x.1 j f₀
    have fit:=written.2.1 x.1 j f₀
    simp only [previous,←show x=v.operandIndex s i from rfl,f,Option.elim_some]
    refine ⟨fit,?_⟩
    rw [width]
    exact read

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentResetFieldAssembler
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "base" => a.rebased floor
local notation "A" => (v).receiver
local notation "b" => (v).assemblerBits
local notation "plan" => (v).linkedRankInputs u.sectors ((v).sheetsStart base)
local notation "L" => (v).rankBook plan base
local notation "r" => (v).renderFromRanks plan base
local notation "rankMem" m:arg => (L).memory (((v).rankPortPhase base w).image m)

/-- At the actual operand clock the hidden field reads still see the ranked
metadata and three offsets from the original cable books. -/
theorem previous_read (ok : u.Ready) (m : Memory w)
    («meta» : Fin (A).blocks→Fin (A).candidates→Fin (A).hosts→Fin (A).groups→Meta)
    (offset : Fin (A).blocks→Fin 3→Fin (A).candidates→Fin (A).hosts→Fin (A).groups→Cell b)
    (heads : ∀x j, Source ((plan).header x j) (fun h g=>raw b («meta» x j h g)) (A).lanes
      (rankMem (u.candidateEntry ok m)))
    (ranks : ∀x p j, Source ((L).finalRank x p j) (offset x p j) (A).lanes
      (rankMem (u.candidateEntry ok m)))
    (small : ∀x j h g t,digits («meta» x j h g) t<2^b) (i j) :
    Source ((v).previous u.operand r base i j) ((v).previousValue u.operand «meta» offset i j)
      (A).lanes (u.operandEntry ok m) :=by
  have bounds:=(v).control_address_bounds base
  have endAt:=(v).render_end base ok.width
  have top:=(DescentResetWindowTail.lower ((v).rankEnd base) (A).blocks (A).capacity
    b (A).lanes (A).hosts (A).groups).trans endAt.le
  have after : (v).controlFloor base<2^w :=
    (bounds.2.2.1.trans bounds.2.2.2).trans_lt ok.full
  have area : (v).fieldsEnd base<2^w:=top.trans_lt after
  have space : (L).endAddress<2^w:=(Nat.le_add_right ((v).rankEnd base) _).trans_lt area
  obtain ⟨t₁,t₂,t₃,t₄⟩:=(L).ordered
  have before : ∀x j,((plan).header x j).Fits w ((v).rankEnd base):=fun x j=>
    ProtocolRAMGeneratedWrite.fits_mono _ (((t₁.trans t₂).trans t₃).trans t₄) (ok.ranks.header x j)
  obtain ⟨fits,read⟩:=(v).previous_at_fields u.operand «meta» offset r base (rankMem (u.candidateEntry ok m))
    ok.width before ((L).finalRank_fits ok.ranks space) heads ranks small area i j
  intro row
  exact (ProtocolRAM.eval_below _ _ _ _ fits (u.operand_fields_frame ok m)).trans (read row)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
