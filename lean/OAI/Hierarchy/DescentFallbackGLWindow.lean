import OAI.Hierarchy.DescentResetFieldShuffle
import OAI.Hierarchy.DescentFallbackPeriodBanks
import OAI.Hierarchy.DescentPackedMaskedData

namespace OAI
/-! # Low-coordinate readback of signed controls from the measured global GL shuffle -/
namespace Hierarchy.DescentFallbackPeriod
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentPackedFallbackTree.Image
open DescentGLPacked DescentGL DescentGLPacked.BankImage DescentColonies DescentSharedCableNames.Stage
open DescentIssuedFallbackPanel DescentSixParty DescentGroupPeerOrder DescentStageEdgeReceipt
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M w bytes slots field : ℕ}

/-- The same dictionary shape extracts either a signed field, a plain owner field, or a tagged
endpoint for exchange through the earlier shared physical neighbor roster. -/
def project (j : Fin slots) (additional : ℕ) (key : Cell (bytes*slots)) : Cell field :=
  ((((encode bytes slots).symm key j).val+additional:ℕ):Cell field)

theorem projected (banks : Banks) (out : ℕ) (j : Fin slots) (plus : ℕ)
    (x : Fin H→Fin G→Fin slots→Cell bytes) (m : Memory w)
    (safe : Fits banks (bytes*slots) field M H G w out)
    (source : Reads banks.source (fun h g=>encode bytes slots (x h g)) M m)
    (dict : resident (project (field:=field) (bytes:=bytes) j plus) banks H G M m) :
    Source (DescentSIMDLookup.lookup banks) (fun h g=>((x h g j).val+plus:Cell field)) M m := by
  let arr:=fun h g=>encode bytes slots (x h g)
  let f:=project (field:=field) (bytes:=bytes) j plus
  have fixed : PinFrame (M:=M) banks f arr m := by
    refine ⟨?_,source⟩
    intro a b
    cases a with
    | inl a=>exact congrArg (fun n=>Computability.VPVNP.RAMSerialization.wordBits w n b) (dict.1 a)
    | inr a=>exact congrArg (fun n=>Computability.VPVNP.RAMSerialization.wordBits w n b) (dict.2 a)
  intro p
  have value:=lookup_read banks out safe f arr m fixed p
  rw [masked_eq_data] at value
  simpa only [f,arr,project,Equiv.symm_apply_apply,Nat.cast_add] using value

theorem publish_projected (banks : Banks) (out : ℕ) (j : Fin slots) (plus : ℕ)
    (x : Fin H→Fin G→Fin slots→Cell bytes) (m : Memory w)
    (safe : Fits banks (bytes*slots) field M H G w out)
    (source : Reads banks.source (fun h g=>encode bytes slots (x h g)) M m)
    (dict : resident (project (field:=field) (bytes:=bytes) j plus) banks H G M m) :
    let m':=imageBank H G M out banks m
    (DescentSIMDLookup.program banks out H G M w).Exec m m' (4+44*(H*chunks G M)) ∧
    (∀p : Row H G M,m' (out+(row H G M p).val)=
      ((data (fun h g=>((x h g j).val+plus:Cell field)) p).val:Word w)) ∧
    ∀a,(a<out ∨ out+H*chunks G M≤a)→m' a=m a := by
  have ok : (DescentSIMDLookup.lookup banks).Fits w out:=⟨⟨safe.dictionary,safe.source,trivial⟩,safe.mask,trivial⟩
  have read:=projected banks out j plus x m safe source dict
  refine ⟨?_,fun p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans (read p),fun a away=>
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ away⟩
  rw [Nat.mul_comm 44]
  exact @ProtocolRAM.scan_exec w out (H*chunks G M) (DescentSIMDLookup.lookup banks) m ok safe.output

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i big low c : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gate : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W gate q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block (big+low)≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank groupKey ids)
local notation "sign" => signedPanel A native S ready names
variable (μ : Layout (big+low)) (fits : c≤big+low)
local notation "L" => 2^(big+low-c)
local notation "b" => DescentSignedCableCodec.width A.degree A.cap
local notation "shelf" => fun v hi lo=>donor digits μ fits v hi lo

/-- An incoming signed channel names the physical donor, before any reset classification. -/
theorem signed_panel (bank : Bank) (slot : Fin (2*A.cap)) (x : Fin H→Block (big+low)→Cell b)
    (trueOld : ∀v z,x (vertex v) z=DescentSignedCableCodec.encode
      (sign (((digits z).1,v),(digits z).2) slot))
    (pitch : M*L=2^low) (pos : 0<M) (mem : Memory w)
    (reached : Dense (h:=big) (l:=low) bank.base (fun v z=>x v ((rearrange μ).symm z)) mem) :
    let words:=fun h hi lo=>x h ((rearrange μ).symm (join fits hi lo))
    Reads bank (fun h hi=>encode b L (words h hi)) M mem ∧
      ∀v hi lo,words (vertex v) hi lo=DescentSignedCableCodec.encode (sign (shelf v hi lo) slot) := by
  exact ⟨DescentPlainTerminal.Suffix.grouped_remix fits pitch pos bank.base x μ mem reached,
    fun v hi lo=>trueOld v _⟩

theorem signed_field (banks : Banks) (out : ℕ) (slot : Fin (2*A.cap)) (lo : Fin L)
    (x : Fin H→Block (big+low)→Cell b)
    (trueOld : ∀v z,x (vertex v) z=DescentSignedCableCodec.encode (sign (((digits z).1,v),(digits z).2) slot))
    (pitch : M*L=2^low) (pos : 0<M) (mem : Memory w)
    (reached : Dense (h:=big) (l:=low) banks.source.base (fun v z=>x v ((rearrange μ).symm z)) mem)
    (safe : Fits banks (b*L) field M H (2^c) w out)
    (dict : resident (project (field:=field) (bytes:=b) lo 0) banks H (2^c) M mem) :
    let words:=fun h hi j=>x h ((rearrange μ).symm (join fits hi j))
    Source (DescentSIMDLookup.lookup banks) (fun h hi=>((words h hi lo).val:Cell field)) M mem ∧
      ∀v hi,words (vertex v) hi lo=DescentSignedCableCodec.encode (sign (shelf v hi lo) slot) := by
  obtain ⟨actual,group⟩:=signed_panel A S ready digits native groupKey vertex μ fits banks.source slot x trueOld pitch pos mem reached
  exact ⟨by simpa using projected banks out lo 0 _ mem safe actual dict,fun v hi=>group v hi lo⟩

end
end Hierarchy.DescentFallbackPeriod

end OAI
