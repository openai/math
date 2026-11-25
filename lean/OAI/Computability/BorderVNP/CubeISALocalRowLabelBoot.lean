import OAI.Computability.BorderVNP.CubeISALocalRowPinnedBoot
import OAI.Computability.BorderVNP.CubeISALocalRowLabelPrefix
import OAI.Computability.BorderVNP.RoutingISABlockAppend

/-! # The native label, interval, powers and declaration prefix on the pinned cube

The memory entering the powers pass is the actual deterministic return of the
first two programs. Its low words still spell the copied broadcast and the
cube's physical scalar and address operands.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open CubeHeaderInstall TeamContraction.JointHeader
open private seq_assoc from OAI.Computability.BorderVNP.RoutingISABlockAppend

/-- The secondary header and its dense claims precede the public label scratch. -/
theorem header_le_publicBase (a : CubeArena.Layout) : a.header.header ≤ a.publicBase := by
  have bank : a.header.header ≤ a.header.packetBase := by unfold Inputs.packetBase; omega
  have endBank := (arenaExtents a).1
  have single : a.packetEnd+8+a.h = a.singleBank := rfl
  have bounds := a.separated
  omega

/-- Every returning label-and-interval trace preserves the low memory. In
particular the actual geometric cell count in frame word eleven survives. -/
theorem labelPrefix_preserved {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    {r out : Bank w} {m result : Memory w} {es : List (TeamRAM.Event w)}
    (fit : LabelPrefixFits (pub 0).val w (readings m))
    (run : Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) r m es out result) :
    (∀ x < readings m ((pub 0).val+48), readings result x = readings m x) ∧
      readings result ((pub 0).val+11) = readings m ((pub 0).val+11) := by
  obtain ⟨_,_,_,actual,_,keep⟩ := labelPrefix_run pub mac r m fit
  obtain ⟨_,rfl,rfl⟩ := run.unique_of_deterministic (by decide) actual
  have start := fit.frame
  exact ⟨keep,keep _ (by omega)⟩

/-- Execute the label and directed-width programs and continue with the actual
power table and dense declaration. Every successful path sees the same selected
label memory and every rejected declaration has no such continuation. -/
theorem labelBoot_pinned {w : ℕ} (pub : Arg → Word w) (f : BroadcastFrame)
    (a : CubeArena.Layout) (old : Fin 81 → Word w) (fresh gates outputs width off ell : ℕ)
    (mac : TeamOpcode.Macros w 8) (r : Bank w) (m : Memory w)
    (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (decl : Broadcast a.n a.header.d a.header.cap) :
    let raw := padded (TeamContraction.JointHeader.spelling (G++DeclarationBits.spelling decl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w a.header.d a.n a.header.blocks a.b a.h a.s
    let ext := jointFields (a.extension old) fresh G.length gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s
    let labelPass : Code := .seq LabelIndex.directoryProgram NativeIntervals.prepare
    let labelTicks := labelPrefixCost (pub 0).val (readings m)
    BootPins pub f ext raw m → a.header = physical →
    (pub 0).val+112 ≤ a.header.header → f.dst+raw.length ≤ a.header.header →
    0 < a.header.d → 0 < a.header.blocks → 0 < bankWidth a.n a.b a.h a.K a.s → a.stop < 2^w →
    LabelPrefixFits (pub 0).val w (readings m) →
    ∃ tr mid selected, Runs pub mac labelPass r m tr mid selected ∧ traceCost tr ≤ labelTicks ∧
      (∀ x < a.publicBase, readings selected x = readings m x) ∧ BootPins pub f ext raw selected ∧
      TestRun pub mac (.block [LabelIndex.directoryProgram,NativeIntervals.prepare,CubePowers.install,
        install a.n (selectorWidth a.n a.K a.h),HeaderDecode.program]) r m
        (labelTicks+publicBootCost a f.dst) (declarationInRange decl)
        (DecodedRows a (readings pub) f.dst decl (readings selected)) := by
  intro raw physical ext labelPass labelTicks pins eq frame stream alphabet blocks stride high fit
  have bounds := a.separated
  have pubRoom : a.publicBase < 2^w := by omega
  have lab : readings m ((pub 0).val+48) = a.publicBase :=
    pins.arenaOperand a old fresh G.length gates outputs width off ell rfl pubRoom
  obtain ⟨es,t,mt,prefixRun,clock,kept⟩ := labelPrefix_run pub mac r m fit
  have low (x : ℕ) (hx : x < a.publicBase) : readings mt x = readings m x := kept x (lab ▸ hx)
  have start := header_le_publicBase a
  have middle := pins.below (frame.trans start) (stream.trans start) low
  have boot := publicBoot_pinned a old fresh gates outputs width off ell mac t G claims pad decl
    middle eq frame stream alphabet blocks stride high
  refine ⟨es,t,mt,prefixRun,clock,low,middle,⟨?_,?_⟩⟩
  · intro valid
    obtain ⟨fs,u,mu,execute,ticks,rows⟩ := boot.complete valid
    exact ⟨es++fs,u,mu,seq_assoc.mpr (prefixRun.seq execute),
      (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add clock ticks),rows⟩
  · intro fs u mu execute
    have joined : Runs pub mac (.seq labelPass (publicBoot a.n (selectorWidth a.n a.K a.h))) r m fs u mu :=
      seq_assoc.mp execute
    cases joined with
    | atom ha _ _ => cases ha
    | seq rp rb =>
      obtain ⟨_,rfl,rfl⟩ := rp.unique_of_deterministic (show labelPass.deterministic=true by decide) prefixRun
      exact boot.sound rb

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
