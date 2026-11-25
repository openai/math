import OAI.Computability.BorderVNP.CubeISAHeaderInstallGeometry
import OAI.Computability.BorderVNP.CubeISAHeaderBroadcastRun

/-! # Building the physical cube declaration after geometry reconstruction

The preceding geometry return preserves the copied physical prefix and the
reference-packet extension. Static installation writes the secondary cube
header. Dynamic decoding reads the actual transmitted coordinate and compact
row words, writing the dense table and its column sums.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeHeaderInstall

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.DeclarationBits PackedHistoryCircuit
open TeamContraction.JointHeader TeamContraction.ProcessorSlots

/-- The two consecutive native stages that materialize the public declaration
before any group loads or team assignments are computed. -/
def prepare (n selectorWidth : ℕ) : RoutingISA.Code := .seq (install n selectorWidth) HeaderDecode.program

/-- Starting from a true geometry return, the actual saved common-header bits
and pinned length metadata supply both phases of the declaration preparation. -/
theorem prepare_after_geometry {w D o : ℕ} {L : Pins.Layout} {P : Pins.ProcessorFields L}
    {f : BroadcastFrame} {A : AdviceLayout} {rp : ReferencePacket w D}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {original result : Memory w}
    {r after : Bank w} {fresh dest clock : ℕ} {out : Fin o → ℕ} {trace : List (TeamRAM.Event w)}
    (geometry : GeometryReturn pub mac r original fresh dest clock out trace after result)
    (old : Fin 81 → Word w) (gates outputs width off ell d n blocks B h s selectorWidth : ℕ)
    (G : List Bool) (fields : List (List Bool)) (pad : ℕ)
    (decl : Broadcast n d (declarationCap n d blocks B h s)) :
    let raw := padded (TeamContraction.JointHeader.spelling (G++DeclarationBits.spelling decl) fields) pad
    let stat := geometryInputs fresh G.length gates outputs width w d n blocks B h s
    let dyn := stat.decoder f.dst
    ProfileOperands P f A rp pub raw original →
      rp.extension = jointFields old fresh G.length gates outputs width off ell d n blocks B h s →
      (pub 0).val+112 ≤ fresh → f.dst+raw.length ≤ fresh → G.length < 2^w → h*B < 2^w →
      stat.Fits w n selectorWidth (pub 0).val → HeaderDecode.Fits dyn w → d*d*stat.cap < 2^w →
      TestRun pub mac (prepare n selectorWidth) after result
        (stat.cost n selectorWidth+(HeaderDecode.cost dyn + HeaderTotals.cost (n+1) (d*d)))
        (readCode (n+1) decl.1 < n+1 ∧ ∀ pair j, readCode (stat.cap+1) (decl.2 pair j) < stat.cap+1)
        (fun z => z.mem = dyn.finalImage (stat.image n selectorWidth (readings result)) ∧
          z.mem (stat.header+5) = readCode (n+1) decl.1 ∧
          CubeLengths.StoredRows z.mem dyn.dense (fun pair j => readCode _ (decl.2 pair j)) ∧
          ∀ j : Fin (n+1), z.mem (dyn.totals+j.val) = ∑ pair, readCode _ (decl.2 pair j)) := by
  intro raw stat dyn data pins prim before prof bit fit room sumRoom
  have hin := install_after_geometry data geometry old G.length gates outputs width off ell d n blocks B h s
    pins prim prof bit selectorWidth fit
  have low : fresh ≤ stat.header := by
    dsimp [stat,geometryInputs,GeometryAdvice.Allocation.stop,GeometryAdvice.Allocation.packed,
      GeometryAdvice.Allocation.dense,GeometryAdvice.Allocation.dest,GeometryAdvice.Allocation.temp]
    omega
  have hHead : stat.header+12 < 2^w := by
    have hf := fit.bank
    change stat.header+13+2*stat.entries+stat.a < 2^w at hf
    omega
  have roomTotals : dyn.totals+dyn.a ≤ 2^w := fit.bank.le
  have disjoint : dyn.dense+dyn.entries ≤ dyn.totals := by
    change stat.header+13+stat.entries+stat.entries ≤ stat.header+13+2*stat.entries
    omega
  have dhead : dyn.header+5 < dyn.totals := by
    change stat.header+5 < stat.header+13+2*stat.entries
    omega
  apply ((hin.asTest (install_deterministic ..)).seq (fun u mu hi => ?_)).mono le_rfl
    (by simp only [true_and]; exact Iff.rfl) (fun _ hh => hh)
  have hmem : readings mu = stat.image n selectorWidth (readings result) := hi.1
  have hf : FlatAt mu f.dst raw := by
    intro j
    apply Fin.ext
    change readings mu (f.dst+j.val) = _
    rw [hmem]
    have below : f.dst+j.val < fresh := by have := j.isLt; omega
    have same : stat.image n selectorWidth (readings result) (f.dst+j.val) = readings result (f.dst+j.val) := by
      simp [Inputs.image,show ¬(stat.header ≤ f.dst+j.val ∧ f.dst+j.val < stat.header+13) by omega]
    rw [same]
    exact congrArg Fin.val ((geometry.preserved _ below).trans (data.header j))
  have hw : 0 < w := by by_contra! hz; have hsmall := room.small; simp [Nat.eq_zero_of_le_zero hz] at hsmall
  have hd := program_from_copy decl G fields pad stat.header f.dst dyn.dense dyn.totals pub mac u mu hf hw room
    hi.2 (by omega) hHead roomTotals (.inl disjoint) (.inl dhead) sumRoom
  apply hd.mono le_rfl Iff.rfl
  intro z hz
  exact ⟨hz.1.trans (congrArg dyn.finalImage hmem), hz.2⟩

end RoutingISA.CubeHeaderInstall

end BorderVNP
end Computability
end OAI
