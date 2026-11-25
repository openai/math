import OAI.Computability.BorderVNP.TransmissionJointHeader
import OAI.Computability.BorderVNP.DiagonalNativeSequence

/-! # Recovering the unique common header from the native startup copies -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader

open VPVNP BurstRAM Diagonal.Layout RoutingISA Routing DiagonalResidueRAM
open private exists_partner from OAI.Computability.BorderVNP.RoutingWireBroadcast

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}

/-- An arbitrary return of the actual pre-scheduling header reader equates
the prefixes of every two incident physical blocks. -/
theorem incident_of_header_return (u : Fin (R+1)) (ib hb sb dst : ℕ) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (r : Bank w) (m : Memory w) (hw : 0 < w)
    (physical : (G.processorFields u pin ext ib hb sb).ContainsInput m)
    (frame : (G.transferFrame u L.header dst).At (readings pub) (readings m))
    (fit : (G.transferFrame u L.header dst).Fits w (pub 0).val)
    {es r' m'} (run : Runs pub mac readBroadcast r m es r' m') :
    ∀ b c : Block (R+1), Incident u b → Incident u c →
      (L.exteriorEquiv ext).broadcast b = (L.exteriorEquiv ext).broadcast c := by
  let f := G.transferFrame u L.header dst
  obtain ⟨ne,lt⟩ := f.partner_spec L.three
  let partner : Fin (R+1) := ⟨f.partner,lt⟩
  have hp : u ≠ partner := fun eq => ne (congrArg Fin.val eq.symm)
  have read (v : Fin (R+1)) (diff : u ≠ v) (i : Fin L.header) :
      readings m (f.addr v i.val) = ((L.exteriorEquiv ext).broadcast (blockOf u v diff) i).toNat :=
    G.read_message_header L u v diff pin ext ib hb sb m physical hw i
  have bits : f.ReferenceBits (readings m) := fun i hi => (read partner hp ⟨i,hi⟩).trans_lt (Bool.toNat_lt _)
  have ok := (readBroadcast_test f pub mac r m frame fit bits).sound run
  have each (v : Fin (R+1)) (diff : u ≠ v) (i : Fin L.header) :
      ((L.exteriorEquiv ext).broadcast (blockOf u v diff) i).toNat =
        ((L.exteriorEquiv ext).broadcast (blockOf u partner hp) i).toNat :=
    (read v diff i).symm.trans ((ok.1 v v.isLt (fun eq => diff (Fin.ext eq.symm)) i.val i.isLt).trans (read partner hp i))
  intro b c atB atC
  obtain ⟨v,hv,rfl⟩ := exists_partner atB
  obtain ⟨z,hz,rfl⟩ := exists_partner atC
  funext i
  exact (show Function.Injective Bool.toNat by decide) ((each v hv i).trans (each z hz i).symm)

/-- The observed header is the full physical prefix of a fixed unordered block. -/
def observed (L : WireLayout (R+1) r link) (ext : Exterior R r link → Bool) (fixed : Block (R+1)) : List Bool :=
  List.ofFn ((L.exteriorEquiv ext).broadcast fixed)

@[simp] theorem observed_length (L : WireLayout (R+1) r link) (ext : Exterior R r link → Bool) (fixed : Block (R+1)) :
    (observed L ext fixed).length = L.header := List.length_ofFn

/-- The observed list records the genuine broadcast function at the fixed block. -/
theorem observed_bits (L : WireLayout (R+1) r link) (ext : Exterior R r link → Bool) (fixed : Block (R+1)) :
    headerBits (observed L ext fixed) (observed_length ..) = (L.exteriorEquiv ext).broadcast fixed := by
  funext i
  simp only [headerBits,observed,List.getElem_ofFn]

/-- All returning native header copies store this one exact list in every team's
RAM, including the branch bit and every advertised coordinate. -/
theorem observed_of_returns (fixed : Block (R+1)) (ib hb sb dst : Fin (R+1) → ℕ)
    (pub : Fin (R+1) → Arg → Word w) (mac : Fin (R+1) → TeamOpcode.Macros w 8)
    (regs : Fin (R+1) → Bank w) (m : Fin (R+1) → Memory w) (hw : 0 < w)
    (physical : ∀ u, (G.processorFields u pin ext (ib u) (hb u) (sb u)).ContainsInput (m u))
    (frame : ∀ u, (G.transferFrame u L.header (dst u)).At (readings (pub u)) (readings (m u)))
    (fit : ∀ u, (G.transferFrame u L.header (dst u)).Fits w (pub u 0).val)
    (z : ∀ u, Evaluator.Returns readBroadcast (pub u) (mac u) (regs u) (m u)) :
    LocalBroadcast (L.exteriorEquiv ext).broadcast ∧
      ∀ u, FlatAt (z u).val.2.2 (dst u) (observed L ext fixed) := by
  have all : LocalBroadcast (L.exteriorEquiv ext).broadcast := fun u =>
    incident_of_header_return u (ib u) (hb u) (sb u) (dst u) (pub u) (mac u) (regs u) (m u) hw
      (physical u) (frame u) (fit u) (z u).property
  refine ⟨all,?_⟩
  intro u
  obtain ⟨es,bank,mem,canon,_,_,_,read⟩ := native_copy L G u pin ext (observed L ext fixed) (observed_length ..)
    (fun k => (broadcast_eq all k fixed).trans (observed_bits ..).symm)
    (ib u) (hb u) (sb u) (dst u) (pub u) (mac u) (regs u) (m u) hw (physical u) (frame u) (fit u)
  have same := (canon.unique_of_deterministic (by decide) (z u).property).2.2
  exact same ▸ flatAt_of_values hw mem (dst u) (observed L ext fixed) read

end TeamContraction.JointHeader

end BorderVNP
end Computability
end OAI
