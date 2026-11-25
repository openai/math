import OAI.Hierarchy.DescentNamedPreflightMachine

namespace OAI
/-! # Original registers and tape cells retained by the full fixed terminal prefix -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler Catalyst DescentTerminalPointerDigits DescentTerminalCombinedRole
open DescentTerminalPrimitiveArena DescentTerminalPreflightSpace DescentTerminalLocalPortBook
open DescentStaticWordColumn DescentSIMDLookup ProtocolRAM DescentColonies.SplitRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Routing CallPool
noncomputable section
set_option quotPrecheck false
variable {F:Type} [Field F] {cp P:ℕ} (X:Approximation F cp P) (G:PoweredGadget F)
  (S:AtomSchedule) {k tail:ℕ} (baseGroups:S.baseGroups=2^tail) (radix:S.radix=2^k)
  (g p q drift:ℕ) (op:RotorSpec) (headerRows paidRows origin romBase:ℕ)
local notation "spec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
local notation "nodes" => S.epochPower^S.localTokenExponent
local notation "maxArgs" => NativeBranch.privateSlotCapacity G S drift
local notation "s₀" => S.firstWidth G.b p
local notation "colors" => DescentPrimitivePalette.colors G s₀ (S.grainAt G.b p 0) op
local notation "groupLimit" => max 8 (2^S.capGain)
local notation "tagBits" => fun f:Fin 6=>DescentTerminalCombinedRole.width colors groupLimit maxArgs p drift f*nodes*(spec).groups
local notation "nodeBits" => Nat.clog 2 (nodes+1)
local notation "config" => (⟨nodeBits,Nat.clog 2 (maxArgs+1),fun _=>DescentOperandWidth.recordBits G S k tail drift 3 p,some nodes⟩:Widths)
local notation "index" => DescentExterior.terminalPin (S.groupWidth k tail 0+k) (S.groupWidth k tail S.length+k) (k*S.length)
local notation "psize" => poolBatchCount (s₀*1) p
local notation "f0" => publicCell (cap:=(spec).cap) (N:=nodes) (A:=maxArgs) (d:=(spec).scalar.pointerBits)
  3 q G.b psize (k*S.length) (spec).groups config
local notation "f7" => DescentTerminalPointerDigits.output (spec).cap nodes maxArgs 3 (spec).groups (spec).scalar.pointerBits
  (Nat.clog 2 (q+maxArgs+1)) q G.b psize config index
local notation "readBook" => decodeBook S G baseGroups radix p q 3 (spec).cap (spec).printBits (by decide)
local notation "fixedControl" => portTable (G:=4) (V:=(spec).vertices) (M:=(spec).vertices*(spec).arguments) (A:=(spec).arguments)
  (a:=Book.tokenBits ((spec).vertices*(spec).arguments)) q
local notation "shelf" => (spec).scanPages romBase q
local notation "blocks" => (spec).scalar.blocks
local notation "shops" => (spec).scalar.shops
variable (w:ℕ) (peer homes:Bank) (paid actor:Fin (2^k)→Bank) (signed:Fin (2^k)→Fin (2*((capCalendar G.b S.rounds g S.height).prod*256))→Bank)
    (matrix roleBase:ℕ) (rolePages:Fin 6→Bank) {Aphys:ℕ} (ptr:Fin 4→Fin Aphys→Fin (2^k)→Bank)
local notation "first" => DescentTerminalRoleTables.role tagBits rolePages roleBase
local notation "second" => DescentTerminalRoleTables.arity tagBits rolePages roleBase
local notation "previous" => DescentTerminalOperandRepack.padded (K:=maxArgs) ptr paid
local notation "raw" => (spec).pointerPages origin matrix previous signed
local notation "chart" => (raw).address (N:=nodes)

variable (m : Memory w)

local notation "run_" => fixedPreflight X G S baseGroups radix g p q drift op headerRows paidRows origin romBase w peer homes paid actor signed matrix roleBase rolePages ptr
local notation "end_" => fixedPreflightMemory X G S baseGroups radix g p q drift op headerRows paidRows origin romBase w peer homes paid actor signed matrix roleBase rolePages ptr m
local notation "clock_" => fixedPreflightClocks X G S (k:=k) (tail:=tail) g p q drift op headerRows paidRows origin romBase peer homes paid actor signed matrix ptr

local notation "literalized" => (shelf).image m
local notation "primitive" => (spec).primitiveSnapshot (base:=origin) (w:=w) (q:=q) (p:=p)
  (nd:=nodeBits) («nodes»:=nodes) (hidden:=maxArgs) (args:=maxArgs) (oldPaid:=paid) (actor:=actor)
  («first»:=first) («second»:=second) («chart»:=chart) («f0»:=f0) («f7»:=f7) literalized
local notation "booked" => (spec).bookSnapshot (base:=origin) (peer:=peer) (wing:=signed) (w:=w)
  (q:=q) (p:=p) (nd:=nodeBits) («nodes»:=nodes) (hidden:=maxArgs) (args:=maxArgs)
  (oldPaid:=paid) (actor:=actor) («first»:=first) («second»:=second) («chart»:=chart)
  («f0»:=f0) («f7»:=f7) (decode:=readBook) literalized

/-- The exact primitive image after installing the fixed scan tables. -/
def fixedPreflightPrimitive : Memory w := primitive

theorem fixed_preflight_frames_and_census
    (space:(shelf).stop≤origin)
  (before:(spec).Before origin paid actor signed peer (shelf).total (shelf).modulo homes (shelf).boundaries)
  (room:(spec).maskBase origin<2^w) (positive:0<w)
  (matrixEnd:matrix+1≤(spec).cohortEnd origin)
  (roleBefore:∀f,(rolePages f).base+(rolePages f).size≤(spec).cohortEnd origin)
  (roleEnd:roleBase+DescentTerminalRoleTables.count tagBits≤(spec).cohortEnd origin)
  (ptrEnd:∀f j b,(ptr f j b).base+(ptr f j b).size≤(spec).cohortEnd origin)
  (ptrRows:∀f j b,shops≤(ptr f j b).size)
  (paidRowsFit:∀b,shops≤(paid b).size) (signedRows:∀b j,shops≤(signed b j).size) :
    ((∀a,a<romBase ∨ (spec).maskBase origin≤a→end_ a=m a) ∧
    (∀a,a<(spec).weights origin→end_ a=primitive a) ∧
    (∀a,a<(spec).bookEnd origin→end_ a=booked a) ∧ (shelf).Reads booked) ∧
    ∀j, origin≤j → j<(spec).cohortEnd origin →
      end_ j=m j ∧ primitive j=m j := by
  have roles:=(spec).role_fits origin room tagBits rolePages roleBase roleBefore roleEnd
  have ptrE:∀f j b,(previous f j b).base+(previous f j b).size≤(spec).cohortEnd origin:=by
    intro f j b;unfold DescentTerminalOperandRepack.padded;split
    · exact ptrEnd _ _ _
    · exact before.oldPaid _
  have ptrH:∀f j b,shops≤(previous f j b).size:=by
    intro f j b;unfold DescentTerminalOperandRepack.padded;split
    · exact ptrRows _ _ _
    · exact paidRowsFit _
  have strips:0<(spec).strips:=by change 0<3+_;omega
  have columns_:0<(spec).scalar.columns:=by
    change 0<3+nodes+4*(nodes*maxArgs)+2*(spec).cap
    omega
  have ptrFit:=(spec).pointer_fits origin matrix previous signed room matrixEnd ptrE ptrH before.oldCables signedRows nodes
  have run:=(spec).purchased_frames origin peer signed w q p nodeBits nodes maxArgs maxArgs paid actor first second chart
    f0 f7 readBook (shelf).total (shelf).modulo homes (shelf).boundaries fixedControl literalized
    before room positive strips columns_ roles.1 roles.2 ptrFit
  have initial:=(spec).incoming origin
  have ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=(spec).layers origin
  have origRoom:(shelf).stop<2^w:=by omega
  have startBound:romBase≤(shelf).stop:=by
    change romBase≤romBase+_;exact Nat.le_add_right ..
  have startRun:=(shelf).install m origRoom
  refine ⟨?_,?_⟩
  · refine ⟨?_,run.2.2.2.1,run.2.2.2.2,?_⟩
    · intro a hit
      exact (run.2.2.1 a (hit.imp (by omega) id)).trans
        (startRun.2.2.2 a (hit.imp id (by omega)))
    · exact (spec).funded_book_pages romBase q origin peer signed w p nodeBits nodes maxArgs maxArgs paid actor
        first second chart f0 f7 readBook homes fixedControl m space before room positive strips columns_
        roles.1 roles.2 ptrFit

  · intro j above below
    have untouched := (run.2.2.1 j (.inl below)).trans
      (startRun.2.2.2 j (.inr (space.trans above)))
    exact ⟨untouched,(run.2.2.2.1 j (below.trans_le (a₁.trans a₂))).symm.trans untouched⟩

theorem fixed_preflight_frames
    (space:(shelf).stop≤origin)
  (before:(spec).Before origin paid actor signed peer (shelf).total (shelf).modulo homes (shelf).boundaries)
  (room:(spec).maskBase origin<2^w) (positive:0<w)
  (matrixEnd:matrix+1≤(spec).cohortEnd origin)
  (roleBefore:∀f,(rolePages f).base+(rolePages f).size≤(spec).cohortEnd origin)
  (roleEnd:roleBase+DescentTerminalRoleTables.count tagBits≤(spec).cohortEnd origin)
  (ptrEnd:∀f j b,(ptr f j b).base+(ptr f j b).size≤(spec).cohortEnd origin)
  (ptrRows:∀f j b,shops≤(ptr f j b).size)
  (paidRowsFit:∀b,shops≤(paid b).size) (signedRows:∀b j,shops≤(signed b j).size) :
    (∀a,a<romBase ∨ (spec).maskBase origin≤a→end_ a=m a) ∧
    (∀a,a<(spec).weights origin→end_ a=primitive a) ∧
    (∀a,a<(spec).bookEnd origin→end_ a=booked a) ∧ (shelf).Reads booked :=
  (fixed_preflight_frames_and_census X G S baseGroups radix g p q drift op headerRows paidRows origin romBase
    w peer homes paid actor signed matrix roleBase rolePages ptr m space before room positive
    matrixEnd roleBefore roleEnd ptrEnd ptrRows paidRowsFit signedRows).1

/-- The original seed verdict, profile rows, all seventeen copied exterior columns
and all paid candidate columns survive the priced terminal prefix on the same run. -/
theorem fixed_preflight_archive
    (space:(shelf).stop≤origin)
  (before:(spec).Before origin paid actor signed peer (shelf).total (shelf).modulo homes (shelf).boundaries)
  (room:(spec).maskBase origin<2^w) (positive:0<w)
  (matrixEnd:matrix+1≤(spec).cohortEnd origin)
  (roleBefore:∀f,(rolePages f).base+(rolePages f).size≤(spec).cohortEnd origin)
  (roleEnd:roleBase+DescentTerminalRoleTables.count tagBits≤(spec).cohortEnd origin)
  (ptrEnd:∀f j b,(ptr f j b).base+(ptr f j b).size≤(spec).cohortEnd origin)
  (ptrRows:∀f j b,shops≤(ptr f j b).size)
  (paidRowsFit:∀b,shops≤(paid b).size) (signedRows:∀b j,shops≤(signed b j).size) (j r t e lo cellSeed compact extra:ℕ) (original:Memory w)
    (seedRead:m cellSeed=original cellSeed)
    (readonly:∀u,lo≤u→u<compact+17*DescentExteriorShelf.span j r t e+extra→m u=original u)
    (placement:compact+17*DescentExteriorShelf.span j r t e+extra≤romBase)
    (seedLow:cellSeed<lo) (profile:lo≤compact) :
    end_ cellSeed=original cellSeed ∧
    (∀u,u<lo→end_ u=m u) ∧
    (∀u,lo≤u→u<compact→end_ u=original u) ∧
    (∀(col:Fin 17) u,u<DescentExteriorShelf.span j r t e→
      let a:=(DescentExteriorShelf.bank j r t e compact col.val).base+u
      end_ a=original a) ∧
    (∀u<extra,let a:=compact+17*DescentExteriorShelf.span j r t e+u
      end_ a=original a) := by
  have saved := fixed_preflight_frames X G S baseGroups radix g p q drift op headerRows paidRows origin romBase
    w peer homes paid actor signed matrix roleBase rolePages ptr m space before room positive
    matrixEnd roleBefore roleEnd ptrEnd ptrRows paidRowsFit signedRows
  have low (u:ℕ) (hu:u<romBase) : end_ u=m u := saved.1 u (.inl hu)
  have authenticated (u:ℕ) (left:lo≤u) (right:u<compact+17*DescentExteriorShelf.span j r t e+extra) :
      end_ u=original u := (low u (right.trans_le placement)).trans (readonly u left right)
  refine ⟨(low _ (by omega)).trans seedRead,fun u hu=>low _ (by omega),
    fun u left hu=>authenticated u left (by omega),?_,?_⟩
  · intro col u hu
    have hcol:col.val+1≤17:=col.isLt
    have bound:=Nat.mul_le_mul_right (DescentExteriorShelf.span j r t e) hcol
    rw [Nat.add_mul,one_mul] at bound
    apply authenticated
    · change lo≤compact+col.val*DescentExteriorShelf.span j r t e+u
      omega
    · change compact+col.val*DescentExteriorShelf.span j r t e+u<_
      omega
  · intro u hu
    exact authenticated _ (by omega) (by omega)


end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
