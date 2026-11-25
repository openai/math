import OAI.Computability.BorderVNP.DiagonalPositiveHeaderClaims
import OAI.Computability.BorderVNP.PackedHistoryGeometryExecute

/-! # Recovery of the source profile from a genuine positive geometry return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader.PositiveFields

open VPVNP BurstRAM RoutingISA VerifierNetwork PackedHistoryCircuit TeamContraction ProcessorSlots
open GeometryAdvice GeometryFrameEncoding DiagonalResidueRAM

variable {σ S V I : Type*} [Fintype σ] [Fintype S] [Fintype V]
variable {reserve active axes groups cap teams dim tally w o b d : ℕ} {L : Pins.Layout}
local notation "Fields" => PositiveFields reserve axes groups cap teams dim tally

/-- Every actual successful geometry reconstruction on the parsed physical packet
determines a unique original history for its checked profile encoding. The output
bank, choice tape and signed contribution belong to the same native return. -/
theorem profile_of_return (p : Fields) (history : Frame (σ ⊕ S) (V ⊕ Unit)) (order : S ≃ Fin active)
    (fits : active ≤ reserve) (emit : Frame ((σ ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : σ → Bool)
    (encode : I ≃ {v : Fin reserve → Bool // validProfile order fits (fun g => history.eval (Sum.elim x g) (.inr ()) = true) v})
    (P : Pins.ProcessorFields L) (f : BroadcastFrame) (A : AdviceLayout) (rp : ReferencePacket w d)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (mem : Memory w)
    (post : ProfileOperands P f A rp pub p.bits mem) (D : Packing.Directory.Layout) (head free team : ℕ)
    (boot : Stripe) (bootBits : List Bool) (strings : Fin D.entries → Fin D.description → Bool)
    (fresh off ell : ℕ) (old : Fin 81 → Word w) (froom : f.Fits w (pub 0).val) :
    let t := geometryTable history order fits emit x
    let st := Allocation.stripe fresh reserve t.size o b off ell
    let packed := Allocation.packed fresh reserve t.size o b w
    let bits := serialized (packet (w:=w) fresh packed t (profileSources f))
    let fs := Allocation.fields old fresh reserve t.size o b off ell
    JointImage D head free boot st bootBits bits strings team P → rp.extension = fs →
    (pub 0).val+112 ≤ f.dst → f.dst+1+reserve ≤ fresh → b ≤ w → 0 < ell →
    off+ell ≤ f.literal → GeometryOutput.packetCount reserve t.size o b*w ≤ f.processors*ell →
    Allocation.stop fresh reserve t.size o b w < 2^w → ∀ {es after result},
      Runs pub mac reconstruct bank mem es after result →
      (∃! q : I, (encode q).val = p.profile) ∧
        GeometryReturn pub mac bank mem fresh (Allocation.dest fresh reserve t.size o b)
          (GeometryAdviceRate.ticks t.size reserve o b w) (emittedWords history order fits emit x p.profile) es after result := by
  intro t st packed bits fs image extension past before width positive literal budget room es after result run
  have copied : ProfileOperands P f A rp pub (Cube.RouteRecords.emittedHeader p.profile p.cube tally p.rawCounts 0) mem :=
    p.bits_eq_emitted ▸ post
  obtain ⟨check,complete⟩ := checked_geometry_runs history order fits emit x P f A rp pub mac bank mem p.profile
    (Cube.DeclarationBits.spelling p.cube) tally 0 p.rawCounts copied D head free team boot bootBits strings
    fresh off ell old froom image extension past before width positive literal budget room
  have valid := check.mp ⟨es,_,run.execute⟩
  let q := encode.symm ⟨p.profile,valid⟩
  have correct : (encode q).val = p.profile := congrArg Subtype.val (encode.apply_symm_apply _)
  obtain ⟨trace,z,mz,success⟩ := complete valid
  have same := (success.unique _ es).mp run.execute
  obtain rfl := same.1
  obtain ⟨_,rfl,rfl⟩ := run.eq_of_shared_events success.run (tail:=[]) (tail':=[]) rfl
  exact ⟨⟨q,correct,fun z hz => encode.injective (Subtype.ext (hz.trans correct.symm))⟩,success⟩

end TeamContraction.JointHeader.PositiveFields

end BorderVNP
end Computability
end OAI
