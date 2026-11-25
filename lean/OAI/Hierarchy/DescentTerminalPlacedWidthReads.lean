import OAI.Hierarchy.DescentTerminalPlacedHeaderDates

namespace OAI
/-! # The two width printers' five input banks survive the placed header instructions -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalEmitter DescentTerminalVertexFields
open DescentTerminalDenseHeader DescentTerminalDenseHeaderRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

/-- Writable result columns may differ between the earlier width printer and
this instruction. Only the five original physical inputs enter the read law. -/
def inputBanks (L : DescentTerminalDenseHeaderRAM.Layout) : Fin 5→Bank :=
  ![L.widths,L.offset,L.next,L.carry,L.format]

theorem five_reads {w q p n : ℕ} {old new : DescentTerminalDenseHeaderRAM.Layout}
    {a : Fin n→Profile q p} {m m' : Memory w} (prior : Reads old a m)
    (same : ∀ (i : Fin 5) (x : Word w),(inputBanks new i).read m' x=(inputBanks old i).read m x) :
    Reads new a m' := by
  obtain ⟨stream,offset,next,carry,format⟩:=prior
  exact ⟨fun i=>(same 0 _).trans (stream i),fun i=>(same 1 _).trans (offset i),
    fun z i=>(same 2 _).trans (next z i),fun z i=>(same 3 _).trans (carry z i),
    fun z i=>(same 4 _).trans (format z i)⟩

variable {blocks v B w : ℕ} (V : Home.Format) (S : DescentTerminalCompiledPrefix.Shape)
    (I : Input) (R : MaskAllocation.Channels blocks) (start head : ℕ)
    (short : v*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece ≤ B)
    (literal : Compact.Literals I.sources)
local notation "C_" => meter V R start
local notation "O_" => registers V S R start head
local notation "base_" => afterMeter V S R start
local notation "A_" => rowArena S I base_
local notation "L_" => layout S I base_ O_
local notation "E_" => emitter S I base_
local notation "μ" m => Suffix.events S L_ (C_).layout ((A_).mount (input V S I R start head short literal m))
local notation "fileAt" m => DescentTerminalDataPlane.file S.terminal.plane (E_).plane (μ m)
local notation "finalAt" m => DescentTerminalDataPlane.finalMem S.terminal.plane (E_).plane (μ m)

theorem low_width_dates (m : Memory w) (early : Earlier S I base_ (C_).layout w)
    (room : last V S I R start < 2^w) (x : ℕ) (low : x<start) :
    (fileAt m) x=m x ∧ (finalAt m) x=m x := by
  have native:=suffix_room S I base_ (C_).layout O_ early room
  have begin_ : start ≤ base_ := by change start ≤ start+_+_+_+_+3;omega
  have below : x<(A_).start+2 := by change x<base_+2;omega
  have saved:=before S I base_ O_ x below
  obtain ⟨p0,p1,_,_,_⟩:=stages S I base_
  have origin : x<takeOff S I base_ := saved.page.trans_le (p0.trans p1)
  have lo : BeforeKey S.terminal E_ x := by
    constructor <;> change x<takeOff S I base_+_ <;> omega
  have hi := after_start S I base_ O_ (a:=x) (by change x<takeOff S I base_+_;omega)
  have result : DescentTerminalEmitter.result S.terminal E_ (μ m) x=m x :=
    (printed_before S.terminal E_ (μ m) native.issuer lo hi).trans
      (events_original V S I R start head short literal m early room low)
  have after_ : (finalAt m) x=m x := (after_plane S.terminal E_ (μ m) native.issuer hi.later).symm.trans result
  exact ⟨(DescentTerminalDenseHeaderRAM.before_inputs (E_).plane.header (fileAt m) native.issuer.plane.widths hi.widths).symm.trans after_,after_⟩

/-- Both measured input streams refer to the same entering machine. The private
stream is read at the joined cable file, and the public stream at its successor. -/
theorem dated_widths {q p n d : ℕ} (m : Memory w) (early : Earlier S I base_ (C_).layout w)
    (room : last V S I R start < 2^w)
    (oldCable oldPublic : DescentTerminalDenseHeaderRAM.Layout)
    (privateProfiles : Fin n→Profile q p) (publicProfiles : Fin d→Profile q p)
    (privateInputs : inputBanks oldCable=I.cable) (publicInputs : inputBanks oldPublic=I.exterior)
    (privateBefore : ∀j,(I.cable j).base+(I.cable j).size ≤ start)
    (publicBefore : ∀j,(I.exterior j).base+(I.exterior j).size ≤ start)
    (privateWords : Reads oldCable privateProfiles m) (publicWords : Reads oldPublic publicProfiles m) :
    Reads (E_).plane.header privateProfiles (fileAt m) ∧
      Reads (E_).exteriorWidths publicProfiles (finalAt m) := by
  have dates:=low_width_dates V S I R start head short literal m early room
  have cable (j : Fin 5) : inputBanks (E_).plane.header j = I.cable j := by
    fin_cases j <;> rfl
  have exterior (j : Fin 5) : inputBanks (E_).exteriorWidths j = I.exterior j := by
    fin_cases j <;> rfl
  have original (b : Bank) (endBank : b.base+b.size ≤ start) (z : Word w) :
      b.base+z.val%b.size < start :=
    (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos b.bits)) _).trans_le endBank
  constructor
  · apply five_reads privateWords
    intro j z
    rw [privateInputs,cable]
    exact (dates _ (original _ (privateBefore j) z)).1
  · apply five_reads publicWords
    intro j z
    rw [publicInputs,exterior]
    exact (dates _ (original _ (publicBefore j) z)).2

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns

end OAI
