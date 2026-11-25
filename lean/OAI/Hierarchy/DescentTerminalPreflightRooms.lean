import OAI.Hierarchy.DescentTerminalPreflightLengths

namespace OAI
/-! # Numerical working room for every real preflight phase and the three incidence banks -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentTerminalPrimitiveArena DescentTerminalLocalPortBook DescentTerminalGrainProfiles
open DescentTerminalRowArena ProtocolRAM DescentSIMDLookup ThreeFlat.RAM
noncomputable section
variable (x:Spec) (base:ℕ) {w:ℕ} (word:x.maskBase base<2^w)
local notation "H" => x.scalar.shops
local notation "E" => x.cohortEnd base
local notation "P" => x.primitive base
local notation "U" => x.weights base
local notation "B" => x.bookBegin base
local notation "F" => x.bookEnd base
local notation "C" => DescentTerminalControlProgram.Plan.finish (x.controls base)
local notation "T" => x.cableEnd base
local notation "X" => x.publicWidths base
local notation "pub" => x.literalBase base
local notation "D" => x.draftBase base
local notation "last" => x.maskBase base

theorem bounds : E≤P ∧ P≤U ∧ U≤B ∧ B≤F ∧ F≤C ∧ C≤T ∧ T≤pub ∧ pub≤D ∧ D≤last:=x.layers base

private theorem fits_of {b:Bank} {lo top:ℕ} (endAt:b.base+b.size≤lo) (before:lo≤top) (high:top<2^w) :
    b.Fits w lo:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((endAt.trans before).trans_lt high),endAt⟩

/-- The only free addresses are attained old raster/peer/cable inputs and genuinely
mounted original count, modulus, address and row-boundary literals. -/
structure Before (paid actor:Fin x.scalar.blocks→Bank) (old:Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (neighbor total modulo homes:Bank) (boundary:ℕ) : Prop where
  oldPaid : ∀b,(paid b).base+(paid b).size≤E
  paidRows : ∀b,H*chunks x.groups x.paidLanes≤(paid b).size
  oldActor : ∀b,(actor b).base+(actor b).size≤E
  actorRows : ∀b,H*chunks x.groups x.actorLanes≤(actor b).size
  oldCables : ∀b j,(old b j).base+(old b j).size≤E
  roster : neighbor.base+neighbor.size≤E
  total : total.base+total.size≤E
  modulo : modulo.base+modulo.size≤E
  homes : homes.base+homes.size≤E
  boundary : boundary+(x.paidRows+1)≤E

variable (paid actor:Fin x.scalar.blocks→Bank) (old:Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (peer total modulo homes:Bank) (boundary:ℕ)
    (boot:x.Before base paid actor old peer total modulo homes boundary)
local notation "rack" => x.cables base peer old
local notation "arena" => x.draft base total modulo homes boundary

include boot in
theorem earlier_population : DescentTerminalPriorArena.Earlier x.scalar x.groups x.paidLanes x.actorLanes E
    paid actor (x.census base) :=
  ⟨boot.oldPaid,boot.paidRows,x.census_end base,Nat.le_pow_clog (by decide) _,boot.oldActor,boot.actorRows⟩

include word boot in
theorem fits_cables : (rack).Fits w := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩:=x.bounds base
  have near:E≤C:=by omega
  have before:C≤last:=by omega
  have wide:2^x.cableCellBits≤fee x.widthColumns x.cableCellBits:=by
    have positive:0<x.widthColumns:=by change 0<1+_;omega
    exact (Nat.le_mul_of_pos_left _ positive).trans (Nat.le_add_right ..)
  have avail:fee x.widthColumns x.cableCellBits≤T:=by rw [cable_size];unfold cableWords;omega
  exact ⟨fun k j=>fits_of ((boot.oldCables k j).trans near) before word,
    fits_of (boot.roster.trans near) before word,by change 2^x.cableCellBits<2^w;omega,by change T<2^w;omega⟩

include word in
theorem after_public : (X).old.Fits w (X).base ∧ (X).widthLayout.stop<2^w := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩:=x.bounds base
  have old:=x.census_end base
  exact ⟨fits_of (b:=x.census base) (lo:=T) (by omega) (by omega : T≤last) word,by change pub<2^w;omega⟩

include word in
theorem book_fits (populated:0<x.strips) : (∀j:Fin 6,((x.parts base j).source.Fits w F) ∧ ((x.parts base j).weights.Fits w F)) ∧
    2^x.printBits<2^w ∧ F<2^w := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩:=x.bounds base
  have before:F≤last:=by omega
  have wide:2^x.printBits≤fee x.strips x.printBits:=by
    exact (Nat.le_mul_of_pos_left _ populated).trans (Nat.le_add_right ..)
  have room_:fee x.strips x.printBits≤F:=by rw [book_size];unfold bookWords;omega
  exact ⟨fun j=>⟨fits_of (x.book_banks base j).1 before word,fits_of ((x.book_banks base j).2.trans d) before word⟩,
    by omega,by omega⟩

private theorem prefix_end (L:DescentTerminalWidthRowsRAM.Layout) : L.prefix.base+L.prefix.size≤L.stop := by
  change L.prefix.base+L.prefix.size≤L.prefix.base+L.prefix.size+L.output.size+1+L.groups+L.groups
  omega

include word boot in
theorem fits_draft : DescentTerminalHeaderDraft.Room arena (x.eventInputs base peer old) x.degree w ∧
    boundary+(x.paidRows+1)≤(arena).start := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩:=x.bounds base
  have first:E≤D:=by omega
  have oldFit {s:Bank} (early:s.base+s.size≤E) : s.Fits w D:=fits_of (early.trans first) i word
  have field (j:Fin 6) := x.book_banks base j
  have lower:(arena).Lower w:=⟨fun j=>fits_of ((field j).1.trans (by omega : F≤D)) i word,
    fun j=>fits_of ((field j).2.trans (by omega : B≤D)) i word,
    oldFit boot.total,oldFit boot.modulo,oldFit boot.homes⟩
  have cab:(rack).printer.prefix.base+(rack).printer.prefix.size≤T:=prefix_end _
  have «public»:(X).widthLayout.prefix.base+(X).widthLayout.prefix.size≤pub:=prefix_end _
  exact ⟨DescentTerminalHeaderDraft.allocate arena x.degree lower word (oldFit boot.roster)
    (fits_of (cab.trans (by omega : T≤D)) i word) (fits_of («public».trans h) i word),boot.boundary.trans first⟩

include word in
theorem all_lower :
    E<2^w ∧ P<2^w ∧ U<2^w ∧ B<2^w ∧ F<2^w ∧ C<2^w ∧ T<2^w ∧ pub<2^w ∧ D<2^w := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩:=x.bounds base
  omega

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
