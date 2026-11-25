import OAI.Computability.BorderVNP.RoutingWireNative

/-! # The physical block and native copy of the whole common header -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA

variable {R r t d link inner n w : ℕ} {Edge : Type}
variable {G : Wiring R r t d link inner n Edge} {L : WireLayout (R+1) r link}

/-- The list of field bits viewed as one full physical block header. -/
def headerBits {H : ℕ} (bits : List Bool) (fit : bits.length = H) (j : Fin H) : Bool :=
  bits[j.val]'(fit ▸ j.isLt)

/-- The exterior bit assignment for a completely specified common header and demand
payloads. Both legs use the same payload, and every unused exterior wire is zero. -/
noncomputable def exterior (L : WireLayout (R+1) r link) (bits : List Bool) (fit : bits.length = L.header)
    (payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) : Exterior R r link → Bool :=
  L.exteriorEquiv.symm ⟨fun _ => headerBits bits fit,
    fun u _ p => payload (min u p.1) (max u p.1) p.2.val,fun _ => false⟩

/-- Every unordered block actually contains the entire same list, including its branch bit. -/
theorem exterior_header (L : WireLayout (R+1) r link) (bits : List Bool) (fit : bits.length = L.header)
    (payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) (k : Block (R+1)) :
    (L.exteriorEquiv (exterior L bits fit payload)).broadcast k = headerBits bits fit := by
  simp [exterior]

/-- All physical routing, padding and header clauses hold, and they force this exterior
bit assignment uniquely. This includes an all-zero unit header and payload. -/
theorem exterior_unique (L : WireLayout (R+1) r link) (fixed : Block (R+1)) (bits : List Bool)
    (fit : bits.length = L.header) (high payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) :
    ∀ ext, Checks L.three L.width fixed (headerBits bits fit) high payload (L.exteriorEquiv ext) ↔
      ext = exterior L bits fit payload := by
  have valid : Checks L.three L.width fixed (headerBits bits fit) high payload
      (L.exteriorEquiv (exterior L bits fit payload)) := by
    unfold exterior
    rw [Equiv.apply_symm_apply]
    unfold Checks
    exact ⟨fun _ _ _ _ _ => rfl,rfl,fun _ _ _ _ => rfl,
      fun _ _ p => by simp [otherHop,min_comm,max_comm],fun _ => rfl⟩
  obtain ⟨x,_,unique⟩ := L.existsUnique_exterior fixed (headerBits bits fit) high payload
  exact fun ext => ⟨fun h => (unique ext h).trans (unique _ valid).symm,fun h => h ▸ valid⟩

/-- Read and compare the common bit list from the actual processor fields after
startup. No populated routing-table assumption is needed before these instructions. -/
theorem native_copy (L : WireLayout (R+1) r link) (G : Wiring R r t d link inner n Edge)
    (u : Fin (R+1)) (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (bits : List Bool)
    (length : bits.length = L.header) (common : ∀ k, (L.exteriorEquiv ext).broadcast k = headerBits bits length)
    (ibase hbase starbase dst : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (hw : 0 < w)
    (physical : (G.processorFields u pin ext ibase hbase starbase).ContainsInput m)
    (image : (G.transferFrame u L.header dst).At (readings pub) (readings m))
    (fit : (G.transferFrame u L.header dst).Fits w (pub 0).val) :
    let f := G.transferFrame u L.header dst
    BoundedRun pub mac readBroadcast s m f.readTicks (fun z =>
      f.Stable z.reg ∧ z.mem = f.copied (readings m) L.header ∧
      ∀ j : Fin bits.length, z.mem (dst+j.val) = bits[j.val].toNat) := by
  intro f
  have h := f.partner_spec L.three
  let partner : Fin (R+1) := ⟨f.partner,h.2⟩
  have hp : u ≠ partner := fun he => h.1 (congrArg Fin.val he.symm)
  have read (v : Fin (R+1)) (hv : u ≠ v) (i : Fin L.header) :
      readings m (f.addr v i) = (headerBits bits length i).toNat := by
    have got := G.read_message_header L u v hv pin ext ibase hbase starbase m physical hw i
    rw [common] at got
    exact got
  have agree : f.Agrees (readings m) := by
    intro v hv hd j hj
    exact (read ⟨v,hv⟩ (fun he => hd (congrArg Fin.val he.symm)) ⟨j,hj⟩).trans (read partner hp ⟨j,hj⟩).symm
  have source : f.ReferenceBits (readings m) := fun i hi => (read partner hp ⟨i,hi⟩).trans_lt (Bool.toNat_lt _)
  apply ((readBroadcast_test f pub mac s m image fit source).complete agree).mono le_rfl
  rintro z ⟨stable,stored⟩
  refine ⟨stable,stored,?_⟩
  intro j
  have bound : j.val < L.header := length ▸ j.isLt
  change z.mem (f.dst+j.val) = _
  rw [stored,f.copied_at (readings m) (show j.val < f.header from bound)]
  exact read partner hp ⟨j.val,bound⟩

end TeamContraction.JointHeader

end BorderVNP
end Computability
end OAI
