import OAI.Hierarchy.DescentSparseHubBits
import OAI.Hierarchy.DescentPublishedHubBits
import OAI.Hierarchy.DescentClosedReset
import OAI.Hierarchy.DescentDenseHostTape

namespace OAI
/-! # The live reset-host tag issued from the common structural roster and its prefix -/
namespace Hierarchy.DescentDenseHostOrder
open DescentCommonHost DescentContacts DescentChosenRouter
open scoped Classical
noncomputable section
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h)

def hubShape {V : Type} : Node V (V×Endpoint (2^n)) (DescentCommonPalette.rotor G).Site→Bool
  | .trunk false z=>z.2.2.isNone
  | _=>false

def hubCode (r Ht : ℕ) (i : Fin (roster G r Ht).card) : Bool :=
  let toRow:=localRank G r Ht
  let printed:=Equiv.ofBijective toRow ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨toRow.injective,by simp⟩)
  hubShape G (printed.symm i).val

theorem hubCode_at (r Ht : ℕ) (x : ↥(roster G r Ht)) :
    hubCode G r Ht (localRank G r Ht x)=hubShape G x.val := by
  unfold hubCode
  exact congrArg (fun y : ↥(roster G r Ht)=>hubShape G y.val) (Equiv.symm_apply_apply _ x)

end
end Hierarchy.DescentDenseHostOrder

namespace Hierarchy.DescentSixParty.ResetInput
open DescentDenseHostOrder DescentCommonHost DescentHubBits DescentCensusRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "pool" => roster Z.graph (Z.k-T.commonDepth) Ht
set_option quotPrecheck false in
local notation "Vnew" => ↥(commonNames Z T)
variable {H pad : ℕ} (vertex : Z.V↪Fin H) (room : Fintype.card ↥(commonNames Z T) ≤ pad)
local notation "key" => rawHostRank Z T vertex
local notation "rank" => Function.Embedding.trans (denseHostRank Z T vertex) (Fin.castLEEmb room)
local notation "slots" => H * Finset.card pool

def hubROM (j : Fin slots) := hubCode Z.graph (Z.k-T.commonDepth) Ht (finProdFinEquiv.symm j).2

theorem hubROM_at (v : Vnew) : hubROM Z T (key v)=Z.commonTag T v := by
  change hubCode Z.graph _ _ (finProdFinEquiv.symm (finProdFinEquiv (hostFields Z T vertex v))).2=_
  rw [Equiv.symm_apply_apply]
  change hubCode Z.graph _ _ (localRank Z.graph _ _ (Z.localShape T v))=_
  rw [hubCode_at]
  change hubShape Z.graph (shape Z.graph v.val)=_
  obtain ⟨z,hz⟩:=v
  cases z with
  | trunk b u=>cases b <;> rfl
  | good b u cell=>rfl
  | fall b u path=>rfl

attribute [local irreducible] commonNames reenter DescentResetTrunks.install denseHostRank rawHostRank

theorem true_hub_column {w : ℕ} (banks : Banks w slots (pad+1)) (flags ids codes : Bank)
    (mem : Memory w) (ff : flags.Fits w banks.first) (idd : ids.Fits w banks.first)
    (codeRoom : codes.Fits w banks.first) (roomF : slots≤flags.size) (roomI : slots ≤ ids.size)
    (roomC : slots≤codes.size)
    (bitsRead : ∀i : Fin slots,mem (flags.base+i.val)=
      (DescentEdgeTapePrefix.row (fun _ : Vnew=>1) (fun v=>(key v).val) i.val:Word w))
    (prefixRead : ∀v : Vnew,mem (ids.base+(key v).val)=((denseHostRank Z T vertex v).val:Word w))
    (static : ∀j : Fin slots,mem (codes.base+j.val)=((hubROM Z T j).toNat:Word w)) :
    let target:=DescentHubBits.destination banks.bins pad flags ids
    ∃out : Memory w,(tally banks target (.lookup codes .row)).Exec mem out
        (tallyCost banks target (.lookup codes .row)) ∧
      (∀v : Vnew,out (banks.bins+(denseHostRank Z T vertex v).val)=((Z.commonTag T v).toNat:Word w)) ∧
      (∀v : Fin pad,(¬∃a : Vnew,(denseHostRank Z T vertex a).castLE room=v)→ out (banks.bins+v.val)=0) ∧
      ∀a<banks.first,out a=mem a := by
  classical
  have present (i : Fin slots) : mem (flags.base+i.val)=(if active key i then 1 else 0) := by
    rw [bitsRead]
    by_cases e : active key i
    · obtain ⟨v,rfl⟩:=e
      have live : active key (key v) := ⟨v,rfl⟩
      rw [ite_eq_left live, DescentEdgeTapePrefix.row_present (fun _ : Vnew => 1)
        (fun u : Vnew => (key u).val) (fun a b h => (key).injective (Fin.ext h)) v]
      exact Nat.cast_one
    · rw [ite_eq_right e, DescentEdgeTapePrefix.row_absent (fun _ : Vnew => 1)
        (fun u : Vnew => (key u).val) i.val (fun v h => e ⟨v,Fin.ext h⟩)]
      exact Nat.cast_zero
  obtain ⟨out,run,l,a,f⟩:=DescentHubBits.emit key (rank) banks flags ids codes (hubROM Z T)
    mem ff idd codeRoom roomF roomI roomC present prefixRead static
  refine ⟨out,run,?_,a,f⟩
  intro v
  rw [←hubROM_at Z T vertex v]
  exact l v

/-- The rank used to write each tag is produced by this same execution's prefix
of the true occupied-host bitmap. The shape ROM is fixed over the sparse rectangle. -/
theorem prefix_hubs {w : ℕ} (banks : Banks w slots (pad+1)) (flags ids codes : Bank)
    (m : Memory w) (ff : flags.Fits w banks.first) (idd : ids.Fits w banks.first)
    (cf : codes.Fits w banks.first) (roomF : slots≤flags.size) (roomI : slots ≤ ids.size)
    (roomC : slots≤codes.size) (fl : flags.base+slots≤ ids.base)
    (cd : codes.base+slots≤ ids.base) (headRoom : ids.base+slots+1<2^w)
    (bitsRead : ∀i : Fin slots,m (flags.base+i.val)=
      (DescentEdgeTapePrefix.row (fun _ : Vnew=>1) (fun v=>(key v).val) i.val:Word w))
    (static : ∀j : Fin slots,m (codes.base+j.val)=((hubROM Z T j).toNat:Word w)) :
    let expr:=DescentHubBits.destination banks.bins pad flags ids
    let first:=ProtocolRAMEndpointPrefix.exclusive w flags.base ids.base slots
    ∃out : Memory w,(first.seq (tally banks expr (.lookup codes .row))).Exec m out
        ((10+(3+12*slots))+tallyCost banks expr (.lookup codes .row)) ∧
      (∀v : Vnew,out (banks.bins+(denseHostRank Z T vertex v).val)=((Z.commonTag T v).toNat:Word w)) ∧
      (∀v : Fin pad,(¬∃a : Vnew,(denseHostRank Z T vertex a).castLE room=v)→ out (banks.bins+v.val)=0) ∧
      ∀a< min ids.base banks.first,out a=m a := by
  let tape:=Z.hostTape T vertex
  let after:=ProtocolRAMEndpointPrefix.image ids.base
    (DescentEdgeTapePrefix.before tape.span tape.rank) m tape.slots
  obtain ⟨first,ranks⟩:=Z.hostTape_native T vertex m fl headRoom (fun j hj=>bitsRead ⟨j,hj⟩)
  have kept (x : ℕ) (hx : x < ids.base) : after x=m x:=
    ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl hx)
  obtain ⟨out,run,actual,ghost,low⟩:=Z.true_hub_column T vertex room banks flags ids codes after
    ff idd cf roomF roomI roomC
    (fun j=>(kept _ (by have:=j.isLt;omega)).trans (bitsRead j)) ranks
    (fun j=>(kept _ (by have:=j.isLt;omega)).trans (static j))
  exact ⟨out,first.then run,actual,ghost,fun a h=>(low a (lt_min_iff.mp h).2).trans
    (kept _ (lt_min_iff.mp h).1)⟩

end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentSixParty.ClosedReset
open DescentPacking.PackedMatch.Local.Stage DescentCompiler DescentColonies
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z wire hist : ℕ} {W : MarkedWorld F d P bits}
  {D n h C f g cut tail : ℕ} {input : Reached W G q ε S k i z D wire hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)

theorem hub_for_chooser {pad w : ℕ} (room : Fintype.card B.next.V≤pad) (bin : ℕ) (out : Memory w)
    (actual : ∀v,out (bin+(B.next.vertex v).val)=((B.reset.commonTag B.terminals v).toNat:Word w))
    (blank : ∀j : Fin pad,(¬∃v,(B.next.vertex v).castLE room=j)→ out (bin+j.val)=0) :
    ∀j : Fin pad,out (bin+j.val)=((Census.hub B.next.placement
      (B.next.vertex.trans (Fin.castLEEmb room)) j).val:Word w) := by
  apply DescentHubBits.column B.next.placement _ bin out _ blank
  intro v
  change out (bin + (B.next.vertex v).val) = ((B.next.placement.hub v).toNat : Word w)
  rw [B.next_hub]
  exact actual v

end
end Hierarchy.DescentSixParty.ClosedReset

end OAI
