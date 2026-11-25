import OAI.Computability.BorderVNP.FiniteEvaluatorSignedRouteInvalid
import OAI.Computability.BorderVNP.CubeISALocalRowBootMinimum
import OAI.Computability.BorderVNP.CubeRouteScheduledWriters

/-! # Reading the declaration used by the finite field evaluator's route inverse

An actual return of the powers, static initializer, declaration parser and
first-minimum guard supplies the intermediate registers, row words and pointer
bounds for recovering the later all-team owned assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.DeclarationReturn

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open RoutingISA RoutingISA.CubeHeaderInstall RoutingISA.LocalRow TeamContraction.JointHeader

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
variable (r : Bank w) (m : Memory w) (a : CubeArena.Layout) (saved : ℕ)
variable (geometry : List Bool) (claims : List (List Bool)) (pad : ℕ)
variable (word : Broadcast a.n a.header.d a.header.cap)

local notation "width" => selectorWidth (CubeArena.Layout.n a) (CubeArena.Layout.K a) (CubeArena.Layout.h a)
local notation "raw" => padded (TeamContraction.JointHeader.spelling (geometry++DeclarationBits.spelling word) claims) pad
local notation "dyn" => Inputs.decoder (CubeArena.Layout.header a) saved

/-- Construct the declaration recovery inputs from the physical compact stream,
the addressed pre-boot frame, and the actual powered decoder and minimum returns.
The coordinate and dense rows in the conclusion are the words from that stream. -/
theorem ofPublicBoot
    (loaded : a.header.Loaded (readings pub) (readings m)) (profile : a.header.profile=geometry.length)
    (bc : frameField (readings pub) (readings m) 61=a.h*a.b) (powers : frameField (readings pub) (readings m) 62=a.powerBase)
    (start : frameField (readings pub) (readings m) 25=saved) (copied : FlatAt m saved raw)
    (extent : saved+(raw).length ≤ a.header.header) (room : a.ReplayRoom w (readings pub 0))
    (run : Evaluator.Returns (.seq (publicBoot a.n width) CubeLengths.minimum) pub mac r m) :
    ∃ valid : declarationInRange word, Nonempty (DeclarationReturn
      (⟨⟨readCode (a.n+1) word.1,valid.1⟩,fun pair j => readCode (a.header.cap+1) (word.2 pair j)⟩ :
        LengthDeclaration a.n a.header.d) pub mac) := by
  obtain ⟨out,after,es,fs,_,boot,minimum⟩ := Runs.seq_iff.mp run.property
  obtain ⟨t,mt,gs,hs,_,pow,prepared⟩ := Runs.seq_iff.mp boot
  obtain ⟨u,mu,ds,js,_,installed,decoded⟩ := Runs.seq_iff.mp prepared
  let frame := readings pub 0
  have fit := staticFits_of_arena a w frame room.primary room.alphabet room.positive room.stopFit
  have decoderFit := decoderFits_of_copy a.header w a.n width frame saved geometry claims pad word
    room.axes profile extent fit
  have ⟨_,labelFit⟩ := bootScalars_of_arena a w room.alphabet (Nat.pos_of_mul_pos_right room.payload) room.stopFit
  have sumRoom := columnSum_room a w room.stopFit
  have ⟨valid,image⟩ := (publicBoot_run pub mac r m a saved geometry claims pad word loaded room.axes profile bc powers
    start copied room.primary extent room.alphabet room.stopFit labelFit fit decoderFit sumRoom).sound boot
  have rows : DecodedRows a (readings pub) saved word (readings m) (.ofWords out after) := image
  have fields := rows.minimumLayout a (readings pub) saved word (readings m) _ room.axes
  change CubeLengths.layout (readings pub) (readings after) = _ at fields
  obtain ⟨bank,sep,top⟩ := arenaExtents a
  have headLow : a.header.header+13 ≤ a.header.packetBase := by unfold Inputs.packetBase; omega
  have low := room.primary
  have high := room.stopFit
  change a.packetEnd+8+a.h ≤ a.powerBase at sep
  have powImage : readings mt=CubePowers.image a.header.d a.powerBase (a.n+1) (readings m) :=
    (((CubePowers.install_run pub mac r m a.header.d (a.n+1) a.powerBase loaded.d (loaded.a.trans room.axes)
      powers room.alphabet (by omega) (by omega) labelFit).asTest (by decide)).sound pow).2
  have same (j : ℕ) (hj : j<112) : frameField (readings pub) (readings mt) j = frameField (readings pub) (readings m) j := by
    rw [powImage]
    simp [frameField,CubePowers.image,show ¬ a.powerBase ≤ readings pub 0+j by omega]
  have source : a.header.Loaded (readings pub) (readings mt) :=
    ⟨(same 63 (by decide)).trans loaded.header,(same 59 (by decide)).trans loaded.d,
     (same 60 (by decide)).trans loaded.a,(same 109 (by decide)).trans loaded.blocks,
     (same 110 (by decide)).trans loaded.profile,(same 111 (by decide)).trans loaded.cap⟩
  have static : readings mu=a.header.image a.n width (readings mt) :=
    (((install_run pub mac t mt a.header source fit).asTest (install_deterministic ..)).sound installed).2
  have atFrame : HeaderDecode.AtFrame dyn (readings pub) (readings mu) :=
    static ▸ a.header.decoder_at a.n width saved (readings pub) (readings mt) source ((same 25 (by decide)).trans start) low
  have packet : a.header.header+13+2*a.header.entries+a.header.a < 2^w := fit.bank
  have sizes : CubeLengths.Fits w (readings pub) (readings after) := by
    refine ⟨by omega,?_,?_,?_,?_⟩
    · rw [show frameField (readings pub) (readings after) 63=a.header.header from rows.2.1.header]
      omega
    · rw [fields]; dsimp only; omega
    · rw [fields]; dsimp only; omega
    · rw [fields]; dsimp only; have := room.axes; omega
  refine ⟨valid,⟨⟨dyn,u,mu,⟨⟨js,out,after⟩,decoded⟩,⟨⟨fs,run.val.2⟩,minimum⟩,decoderFit,atFrame,by omega,?_,?_,?_,
    sumRoom,rfl,room.axes,sizes,congrArg CubeLengths.Layout.claimed fields,congrArg CubeLengths.Layout.totals fields,
    (congrArg CubeLengths.Layout.coordinates fields).trans room.axes.symm,congrArg CubeLengths.Layout.chosen fields,
    rows.2.2.2.2.2.1⟩⟩⟩
  · change a.header.header+12 < _; omega
  · exact packet.le
  · left
    change a.header.header+13+a.header.entries+a.header.entries ≤ a.header.header+13+2*a.header.entries
    omega


/-- At the genuine public writer entry, the physical joint pins and common
header copy supply the declaration checks for any returning schedule. The
label and interval passes retain the copy and primary operands before the
three powered decoder passes and first-minimum guard execute. -/
theorem ofWriterHistory
    (f : RoutingISA.BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell : ℕ)
    (pins : BootPins pub f (jointFields (a.extension old) fresh geometry.length gates outputs bitWidth off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) raw m)
    (shape : a.header=geometryInputs fresh geometry.length gates outputs bitWidth w a.header.d a.n a.header.blocks a.b a.h a.s)
    (extent : f.dst+(raw).length ≤ a.header.header) (room : a.ReplayRoom w (readings pub 0))
    (labelsFit : LabelPrefixFits (pub 0).val w (readings m))
    {es : List (TeamRAM.Event w)} {out : Bank w} {after : Memory w}
    (history : Evaluator.WriterHistory a.n width pub mac r m es out after) :
    ∃ valid : declarationInRange word, Nonempty (DeclarationReturn
      (⟨⟨readCode (a.n+1) word.1,valid.1⟩,fun pair j => readCode (a.header.cap+1) (word.2 pair j)⟩ :
        LengthDeclaration a.n a.header.d) pub mac) := by
  obtain ⟨s₁,m₁,_,_,_,labels,rest⟩ := Runs.seq_iff.mp history.prefixRun
  obtain ⟨s₂,m₂,_,_,_,intervals,rest⟩ := Runs.seq_iff.mp rest
  obtain ⟨_,_,_,_,_,powers,rest⟩ := Runs.seq_iff.mp rest
  obtain ⟨_,_,_,_,_,installed,rest⟩ := Runs.seq_iff.mp rest
  obtain ⟨_,_,_,_,_,decoded,rest⟩ := Runs.seq_iff.mp rest
  obtain ⟨_,_,_,_,_,minimum,_⟩ := Runs.seq_iff.mp rest
  have kept := (labelPrefix_preserved pub mac labelsFit (labels.seq intervals)).1
  have stop := room.stopFit
  have bounds := a.separated
  have base : readings m ((pub 0).val+48)=a.publicBase :=
    pins.arenaOperand a old fresh geometry.length gates outputs bitWidth off ell rfl (by omega)
  have before := header_le_publicBase a
  have middle := pins.below (room.primary.trans before) (extent.trans before)
    (fun addr inside => kept addr (base.symm ▸ inside))
  have fit := staticFits_of_arena a w (pub 0).val room.primary room.alphabet room.positive stop
  have bank : a.header.header+13+2*a.header.entries+a.header.a < 2^w := fit.bank
  have ⟨block,_⟩ := bootScalars_of_arena a w room.alphabet (Nat.pos_of_mul_pos_right room.payload) stop
  have len : geometry.length ≤ (raw).length := by simp only [TeamContraction.JointHeader.padded,TeamContraction.JointHeader.spelling,List.length_append,List.length_cons,List.length_replicate]; omega
  have power := (arenaExtents a).2.2
  obtain ⟨loaded,bc⟩ := resident_inputs pub m₂ (a.extension old) fresh geometry.length gates outputs bitWidth off ell
    a.header.d a.n a.header.blocks a.b a.h a.s middle.extension (shape ▸ fit) (by omega) block
  exact ofPublicBoot pub mac s₂ m₂ a f.dst geometry claims pad word (shape ▸ loaded) (congrArg Inputs.profile shape)
    bc (middle.arenaOperand a old fresh geometry.length gates outputs bitWidth off ell rfl (by omega))
    middle.saved middle.copy extent room ⟨⟨_,_,_⟩,(powers.seq (installed.seq decoded)).seq minimum⟩

end FiniteEvaluator.DeclarationReturn

end BorderVNP
end Computability
end OAI
