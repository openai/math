import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling
import OAI.Computability.BorderVNP.GeometryAdvicePipeline

/-! # Recovering the public profile from every native signed preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally GeometryFrameEncoding

variable {w dim K h : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}

private theorem groups_deterministic (n bits : ℕ) : (scheduleGroups n bits).deterministic=true := by
  simp only [scheduleGroups,Code.block,Code.deterministic,CubeHeaderInstall.install_deterministic,
    show LabelIndex.directoryProgram.deterministic=true by decide,show NativeIntervals.prepare.deterministic=true by decide,
    show CubePowers.install.deterministic=true by decide,show HeaderDecode.program.deterministic=true by decide,
    show CubeLengths.minimum.deterministic=true by decide,show GroupWeights.checkedSchedule.deterministic=true by decide,
    show CellBanks.install.deterministic=true by decide,show PairDirectory.directory.deterministic=true by decide,
    show Transmission.DataWriter.program.deterministic=true by decide,show SharedRows.program.deterministic=true by decide,
    Bool.and_self]

/-- The concrete geometry evaluator runs before any routing operation. The rest
of the public schedule introduces no choices, including all its validation branches. -/
theorem schedule_geometry (p : Returns (schedule dim K h) pub mac s m) :
    ∃ e : Returns GeometryAdvice.reconstruct pub mac s m,
      p.val.1.flatMap TeamRAM.Event.choices=e.val.1.flatMap TeamRAM.Event.choices := by
  have first : Runs pub mac (.seq (.seq GeometryAdvice.reconstruct PrivatePlacement.program)
    (.seq Packing.Directory.ISA.program (scheduleGroups dim (selectorWidth dim K h)))) s m
    p.val.1 p.val.2.1 p.val.2.2 := p.property
  obtain ⟨_,_,es,fs,eq,epoch,rest⟩ := Runs.seq_iff.mp first
  obtain ⟨_,_,a,d,ea,geom,place⟩ := Runs.seq_iff.mp epoch
  have no := Pins.noChoices rest (by
    simp only [Code.deterministic,show Packing.Directory.ISA.program.deterministic=true by decide,
      groups_deterministic,Bool.and_self])
  exact ⟨⟨(_,_,_),geom⟩,by simp only [eq,ea,List.flatMap_append,no,Pins.noChoices place (by decide),List.append_nil]⟩

variable {u o b : ℕ} (f : BroadcastFrame) (a : GeometryAdvice.Stripe) (L : Pins.Layout)
    (P : Pins.ProcessorFields L) (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool)
    (fit : f.Fits w (pub 0).val) (space : a.Fits f w (pub 0).val)
    (layout : GeometryOutput.Placement pub l base start a.dense src t)
    (physical : GeometryAdvice.PhysicalInput pub m f a L P l base start src t x)

include fit space layout physical in
/-- A returned native public schedule forces its *actual* selected profile to be valid
and consumes zero private bits. The interpreter's free-input instruction is dormant
because the actual physical table has `Fin 0` free inputs. -/
theorem schedule_profile (p : Returns (schedule dim K h) pub mac s m) :
    GeometryOutput.validBit t (Sum.elim x Fin.elim0)=true ∧ p.val.1.flatMap TeamRAM.Event.choices=[] := by
  obtain ⟨g,ge⟩ := schedule_geometry p
  have valid : GeometryOutput.validBit t (Sum.elim x Fin.elim0)=true := by
    cases v : GeometryOutput.validBit t (Sum.elim x Fin.elim0) with
    | false => exact (GeometryAdvice.reconstruct_invalid pub mac s m f a L P l base start src t x
        fit space layout physical v g.property).elim
    | true => rfl
  obtain ⟨es,z,mz,r,_cost,bits,_image⟩ := GeometryAdvice.reconstruct_runs pub mac s m f a L P l base start src t x
    fit space layout physical valid
  let e : Returns GeometryAdvice.reconstruct pub mac s m := ⟨(es,z,mz),r⟩
  have eq := return_eq_of_empty pub mac (by decide) e g bits
  exact ⟨valid,ge.trans ((congrArg (fun p : Returns GeometryAdvice.reconstruct pub mac s m =>
    p.val.1.flatMap TeamRAM.Event.choices) eq).symm.trans bits)⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
