import OAI.Computability.BorderVNP.CubeISAHeaderInstallBoot
import OAI.Computability.BorderVNP.CubeISAHeaderInstall
import OAI.Computability.BorderVNP.CubeISAHeaderDecodeFrame
import OAI.Computability.BorderVNP.PackedHistoryGeometryExecute

/-! # Installing the cube header after the actual public geometry program

Geometry preserves the primary scalar fields and ends before the secondary
header reservation. The native initializer writes the actual thirteen words
and supplies the exact frame read by the dynamic declaration decoder.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeHeaderInstall

open VPVNP.BurstRAM PackedHistoryCircuit TeamContraction.ProcessorSlots

/-- Decoder layout read from the static cube header and the copied common broadcast. -/
def Inputs.decoder (l : Inputs) (broadcast : ℕ) : HeaderDecode.Layout :=
  ⟨l.header,broadcast+1+l.profile,l.d,l.a,Nat.clog 2 l.a,Nat.clog 2 (l.cap+1),l.cap,
    l.header+13+l.entries,l.header+13+2*l.entries⟩

/-- All addressed frame words for dynamic decoding after static installation.
The grouping coordinate still occupies the initial zero field. -/
theorem Inputs.decoder_at (l : Inputs) (n bits broadcast : ℕ) (p : Arg → ℕ) (mem : ℕ → ℕ)
    (load : l.Loaded p mem) (start : frameField p mem 25 = broadcast)
    (separate : p 0 + 112 ≤ l.header) :
    HeaderDecode.AtFrame (l.decoder broadcast) p (l.image n bits mem) := by
  have frame (k : ℕ) (hk : k < 112) :
      frameField p (l.image n bits mem) k = frameField p mem k := by
    simp [frameField,Inputs.image,show ¬(l.header ≤ p 0+k ∧ p 0+k < l.header+13) by omega]
  have cell (k : ℕ) (hk : k < 13) :
      l.image n bits mem (l.header+k) = l.value n bits k := by
    simp [Inputs.image,hk]
  exact ⟨(frame 63 (by decide)).trans load.header,(frame 59 (by decide)).trans load.d,
    by change frameField p (l.image n bits mem) 25 + 1 + l.image n bits mem (l.header+9) = broadcast+1+l.profile
       rw [frame 25 (by decide),start,cell 9 (by decide)]; rfl,
    cell 1 (by decide),cell 2 (by decide),cell 3 (by decide),cell 4 (by decide),
    cell 10 (by decide),cell 11 (by decide),cell 12 (by decide)⟩

/-- The static initializer follows any real accepted geometry execution. Its
inputs come from the original pinned extension, which the execution preserves.
The resulting memory is the exact header image and satisfies the native
decoder's addressed input contract. -/
theorem install_after_geometry {w D o : ℕ} {L : Pins.Layout} {P : Pins.ProcessorFields L}
    {f : BroadcastFrame} {A : AdviceLayout} {rp : ReferencePacket w D}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bits : List Bool}
    {original result : Memory w} {r after : Bank w} {fresh dest clock : ℕ}
    {out : Fin o → ℕ} {trace : List (TeamRAM.Event w)}
    (inputs : ProfileOperands P f A rp pub bits original)
    (geometry : GeometryReturn pub mac r original fresh dest clock out trace after result)
    (old : Fin 81 → Word w) (profile gates outputs width off ell d n blocks b h s : ℕ)
    (pins : rp.extension = jointFields old fresh profile gates outputs width off ell d n blocks b h s)
    (frameRoom : (pub 0).val+112 ≤ fresh) (profileFit : profile < 2^w) (blockFit : h*b < 2^w)
    (selectorBits : ℕ) :
    let l := geometryInputs fresh profile gates outputs width w d n blocks b h s
    l.Fits w n selectorBits (pub 0).val →
      BoundedRun pub mac (install n selectorBits) after result (l.cost n selectorBits) (fun z =>
        z.mem = l.image n selectorBits (readings result) ∧
        HeaderDecode.AtFrame (l.decoder f.dst) (readings pub) z.mem) := by
  intro l fit
  have installed (j : Fin 81) : result ((pub 0).val+31+j.val) =
      jointFields old fresh profile gates outputs width off ell d n blocks b h s j :=
    (geometry.preserved _ (by have := j.isLt; omega)).trans ((inputs.extension j).trans (congrFun pins j))
  obtain ⟨loaded,_⟩ := resident_inputs pub result old fresh profile gates outputs width off ell d n blocks b h s
    installed fit profileFit blockFit
  have start : frameField (readings pub) (readings result) 25 = f.dst :=
    (congrArg Fin.val (geometry.preserved ((pub 0).val+25) (by omega))).trans inputs.frame.broadcast.2.2.2.2.2.2
  have apart : (pub 0).val+112 ≤ l.header := by
    dsimp [l,geometryInputs,GeometryAdvice.Allocation.stop,GeometryAdvice.Allocation.packed,
      GeometryAdvice.Allocation.dense,GeometryAdvice.Allocation.dest,GeometryAdvice.Allocation.temp]
    omega
  apply (install_run pub mac after result l loaded fit).mono le_rfl
  intro z hz
  exact ⟨hz,hz ▸ l.decoder_at n selectorBits f.dst (readings pub) (readings result) loaded start apart⟩

end RoutingISA.CubeHeaderInstall

end BorderVNP
end Computability
end OAI
