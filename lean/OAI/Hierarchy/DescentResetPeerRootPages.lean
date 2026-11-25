import OAI.Hierarchy.DescentPreparedRootWords
import OAI.Hierarchy.DescentIssuedFallbackRoot
import OAI.Hierarchy.DescentResetPeerRootFields

namespace OAI
/-! # Private peer pages in the physically installed reset root catalog -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetHostSize
open DescentSixParty.Chronology DescentSixParty DescentResetGates DescentPackedWalsh DescentPlainTerminal.Suffix
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

abbrev PrivateTicket (r n : ℕ) := Code r ⊕ (Code r×Option (Fin (2^n)))
def privatePage {r n : ℕ} (s : Bool) : PrivateTicket r n→RootPage r (2^n)
  | .inl t=>(s,.inl (t,.inl true))
  | .inr t=>(s,.inr t)

variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w)
    (b : RootBook n r D (2^r) cap field)
local notation "L" => 2^r
local notation "J" => 2^c
local notation "slots" => H*chunks J M

def privatePageBank (s : Bool) (t : PrivateTicket r n) : Bank :=
  ⟨(RootTemplates.arena (a.headerEnd b) H J M r n D).output (rootIndex r (2^n) (privatePage s t)).val,Nat.clog 2 slots⟩

theorem privatePage_room (s : Bool) (t : PrivateTicket r n) (next : ℕ)
    (below : a.preparedEnd b ≤ next) (wide : next < 2^w) :
    (a.privatePageBank b s t).Fits w next ∧ slots ≤ (a.privatePageBank b s t).size := by
  let p:=rootIndex r (2^n) (privatePage s t)
  let A:=RootTemplates.arena (a.headerEnd b) H J M r n D
  have top : A.first (p.val+1) ≤ a.preparedEnd b :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ p.isLt) _
  have endRow : A.output p.val+RootArena.span slots=A.first (p.val+1):=RootArena.end_row ..
  have fit : A.output p.val+RootArena.span slots ≤ next := by rw [endRow]; exact top.trans below
  change (0 < RootArena.span slots ∧ RootArena.span slots < 2^w ∧ A.output p.val+RootArena.span slots ≤ next) ∧ _
  exact ⟨⟨Nat.two_pow_pos _,((Nat.le_add_left ..).trans fit).trans_lt wide,fit⟩,RootArena.le_span _⟩

variable (E : EstimatorArena) (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr) (f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "B" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "A" => RootTemplates.arena (a.headerEnd B) H J M r n D
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor board).Edge) (2^(Ht+1))
local notation "digits" => DescentPackedPrivateMenu.fieldBits board r Ht (L*(2*cap)) layerBits C packet
variable (space : a.PreparedFits (a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage)) (mem : Memory w) (positive : 0 < M)
variable (headers : Code r→Fin H→Fin (2^c)→Fin 3→Cell field)
    (packets : Bool→(Code r×Option (Fin (2^n)))→Fin H→Fin (2^c)→Packet D (2^r) cap n r field)

def privatePageValue (side : Bool) : PrivateTicket r n→Fin H→Fin J→Cell (digits*(capacity*5))
  | .inl root=>fun v g=>DescentIssuedGoodHeaders.compactHeaders board packet f Ht (L*(2*cap)) layerBits C capacity side root (headers root v g)
  | .inr root=>fun v g=>law board r Ht layerBits C packet capacity side root (encodePacket (packets side root v g))

include positive in
/-- Both private families use the original two prepared root laws. Every padded high host
and group lane is included in the packed read, even for a physically absent private edge. -/
theorem issued_private_words
    (fits : ∀side root j,let pg:=privatePage (r:=r) (n:=n) side root
      ;((((B).table pg).2).reads j).Fits w ((A).middle (rootIndex r (2^n) pg).val))
    (wide : ∀side root,let pg:=privatePage (r:=r) (n:=n) side root
      ;M*max (((B).table pg).2.field*((B).table pg).1) ((B).table pg).2.outputBits ≤ w/2)
    (live : ∀s root j,Source ((((B).good s root (.inl true)).2).reads j)
      (fun v g=>headers root v g j) M (a.rootInputState B space mem (privatePage s (.inl root))))
    (tree : ∀s root j,Source (((B).exceptional s root).reads j)
      (fun v g=>packets s root v g (number.symm j)) M (a.rootInputState B space mem (privatePage s (.inr root)))) :
    ∀s t,Reads (a.privatePageBank B s t)
      (privatePageValue (Ht:=Ht) (board:=board) (packet:=packet) (C:=C) (layerBits:=layerBits) (f:=f) headers packets s t) M (a.preparedImage B space mem) := by
  intro side root
  cases root with
  | inl t =>
    let p:=privatePage (r:=r) (n:=n) side (.inl t)
    have words:=a.prepared_root_words B space mem p (headers t) (fits side (.inl t))
      (wide side (.inl t)) (live side t) positive
    change Reads _ (fun v g=>DescentIssuedGoodHeaders.compactHeaders board packet f Ht (L*(2*cap)) layerBits C capacity side t
      ((encode field 3).symm (encode field 3 (headers t v g)))) M _ at words
    simp only [Equiv.symm_apply_apply] at words
    exact words
  | inr t =>
    let p:=privatePage (r:=r) (n:=n) side (.inr t)
    exact a.prepared_root_words B space mem p (fun v g j=>packets side t v g (number.symm j))
      (fits side (.inr t)) (wide side (.inr t)) (tree side t) positive

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
