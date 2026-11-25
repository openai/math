import OAI.Hierarchy.DescentPackedDonorPrimitives
import OAI.Hierarchy.DescentPrintedDonor
import OAI.Hierarchy.DescentOrdinaryAtomBirthRead

namespace OAI
/-! # The eight donor coefficients use only the actual selected profile word -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentKernelHistory.BitDescription DescentSixParty.StarKeys
open DescentRawCablePanel DescentSixParty DescentStageEdgeReceipt DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOrdinaryAtomFieldRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1000000
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
    (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "K" => 2^(k+1)
local notation "r" => 2^k
local notation "p" => 2*A.cap
local notation "names" => cableNames k rank
local notation "peers" => rotor A rank
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "C" => ScanColonies he A.stage
local notation "panel" => terrain (short:=short) A native S ready names win peers
local notation "real" => spread groups hosts panel
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ)
local notation "s" => shape r A.degree p profile
local notation "fieldsAt" => Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real)
local notation "seat" => slot he A groups hosts hm
variable (b : ℕ) (m : Memory w) (sumSize : (shape (2^k) A.degree (2*A.cap) profile).outputBits*M≤w)
    (stored : ∀i : Fin ((2^(k+1)*H)*chunks G M),
      m (b+i.val)=((topologyWords (M:=M) (shape (2^k) A.degree (2*A.cap) profile)
        (Gather.flat (Gather.descriptorInputs («K»:=2^(k+1)) (shape (2^k) A.degree (2*A.cap) profile) A.cap
          (spread groups hosts (terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank))))) i).val:Word w))
variable (c : ScanColonies he A.stage)
local notation "num" => pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions
local notation "Pair" => Matched T A.cap (thinList home color c) (thickList home color c)
local notation "x" => inputs s A.cap (heap (addr c).2) (panel (addr c).1) (fun _=>0)


local notation "old" => colorPick W.graph W.core home color A.cap
local notation "nativeC" => normBits A.cap gadget.b gadget.C gadget.k
local notation "PairSet" => NativePair W.graph W.core home color A.cap
variable (choice : (A.stage.result he).Choice) (dest : ℕ) (issuedMem : Memory w)
local notation "selected" => (scannedRows he A.stage).profile choice

private theorem birth_digit (j : Fin (M*(s).pairs*6)) (v : ℕ) :
    digit ((s).digit+1) j.val (SixBirths.cut (SixBirths.width s M) v).val=digit ((s).digit+1) j.val v := by
  have part : 2^(((s).digit+1)*(j.val+1))∣2^(SixBirths.width s M) :=
    pow_dvd_pow _ (Nat.mul_le_mul_left _ j.isLt)
  simp only [SixBirths.cut,digit,Nat.mod_mod_of_dvd _ part]

def measureSupply (q : DescentSharedCableNames.Stage.Positive A) (wire : Fin 8) : Cell nativeC :=
  let u:=W.graph.src q.val
  let c:=home u
  let qid:=word (s).digit (donorAddress A native S ready q)
  let keys:=topologyWords (M:=M) s fieldsAt (seat c).1
  let fresh:=SixBirths.cut (SixBirths.width s M) (issuedMem (dest+(seat c).1.val)).val
  let isFirst:=(query A.cap profile (panel (A.pos u)) (A.block u) (DescentSharedCableNames.Stage.outgoing A native S ready q).val true).isSome
  if isFirst then word nativeC (digit nativeC (seat c).2.val
    (bornField s M A.z (branchDigit nativeC gadget.C gadget.k wire) qid 0 keys fresh).val) else 0

include fit winner in
theorem measured_seat (q : DescentSharedCableNames.Stage.Positive A) (wire : Fin 8) :
    let u:=W.graph.src q.val
    numericSupply s A.cap profile nativeC gadget.C gadget.k A.z hm (panel (A.pos u)) (hosts (A.pos u).2)
      (groups (A.pos u).1) (A.block u) (DescentSharedCableNames.Stage.outgoing A native S ready q) K
      (topologyWords (M:=M) s fieldsAt) (fun i=>SixBirths.cut (SixBirths.width s M) (issuedMem (dest+i.val)).val) wire=
        measureSupply (short:=short) A native S ready rank win he groups hosts hm profile dest issuedMem q wire := by
  intro u
  let c:=home u
  have leaf_:=winner_leaf A native S ready names win peers he fit winner u
  have legal:heap (addr c).2<K:=(keyAt he A c).isLt
  have site:=source_host A he u
  have where_:=slot_eq he A groups hosts hm c
  rw [sourceIndex_eq] at where_
  dsimp only [u,c] at legal leaf_ where_ site ⊢
  simp only [measureSupply,numericSupply,leaf_,dite_eq_left legal,where_,site,donorAddress]
  rfl

include coord named fit winner df edgeOrder sumSize stored in
/-- The field at each emitted birth slot is provided directly by
`Stage.ordinary_births`, on the same physical memory that contains the
previously issued topology. -/
theorem supply_read
    (birth : ∀c : C,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=SixBirths.slot (seat c).2 j q
        SixBirths.atom A.stage.z (digit ((s).digit+1) ip.val (issuedMem (dest+(seat c).1.val)).val) ip.val=
          some (A.stage.z,DescentTerminalEpochFlags.encode (selected ⟨c,e⟩),q.val))
    (q : DescentSharedCableNames.Stage.Positive A) (wire : Fin 8) :
    measureSupply (short:=short) A native S ready rank win he groups hosts hm profile dest issuedMem q wire=
      ((DescentRawCablePanel.first old q.val).map (fun j=>(⟨normalized A selected (.inr (.inr (j,wire))),normalized_fits A S ready selected _⟩:Cell nativeC))).getD 0 := by
  let u:=W.graph.src q.val
  let source:=home u
  have test:=query_iff A native S ready rank win he coord named fit winner df edgeOrder profile q true
  change (query A.cap profile (panel (A.pos u)) (A.block u) (DescentSharedCableNames.Stage.outgoing A native S ready q).val true).isSome=true ↔
    ∃j : PairSet,old (j,0)=q.val at test
  cases found:DescentRawCablePanel.first old q.val with
  | none=>
    have no : ¬∃j : PairSet,old (j,0)=q.val := by
      rintro ⟨j,h⟩
      have yes : DescentRawCablePanel.first old q.val=some j := h ▸ DescentRawCablePanel.first_pick old j
      exact Option.some_ne_none j (yes.symm.trans found)
    have missing := mt test.mp no
    dsimp only [u] at missing
    unfold measureSupply
    dsimp only
    rw [ite_eq_right missing]
    rfl
  | some pair=>
    obtain ⟨c,e⟩:=pair
    have eqn:=first_spec old found
    have chosen := test.mpr ⟨⟨c,e⟩,eqn⟩
    have prev:=(picked_old A he c e true).trans eqn
    have actual:c=source := by simpa only [prev] using (picked A he c e true).property.2.1.symm
    subst c
    let id:=DescentTerminalEpochFlags.encode (selected ⟨source,e⟩)
    let f:=branchDigit nativeC gadget.C gadget.k wire
    let shipped:=SixBirths.cut (SixBirths.width s M) (issuedMem (dest+(seat source).1.val)).val
    obtain ⟨j,ordered,sealed⟩:=birth source e
    have raw:=actual_birth A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder profile b m sumSize stored
      source f A.stage.z id e 0 shipped ⟨j,ordered,by simpa only [shipped,birth_digit] using sealed 0⟩
    have address_:=source_handle_eq A native S ready rank he source true (picked A he source e true)
    have ident : (⟨(picked A he source e true).val,A.quantum_positive _ (picked A he source e true).property.1⟩ : DescentSharedCableNames.Stage.Positive A)=q :=
      Subtype.ext prev
    rw [ident] at address_
    have width_:=normalized_fits A S ready selected (.inr (.inr (⟨source,e⟩,wire)))
    have coefficient:=profile_field nativeC (fun _ (prof : Profile gadget.C) _=>(prof.val wire).val+gadget.k) A.stage.z (selected ⟨source,e⟩) 0 width_
    dsimp only [u] at chosen
    apply Fin.ext
    unfold measureSupply
    dsimp only
    rw [ite_eq_left chosen]
    change (digit nativeC _ _)%2^nativeC=_
    rw [←address_]
    exact (congrArg (fun n : ℕ => n % 2^nativeC) (raw.trans coefficient)).trans (Nat.mod_eq_of_lt width_)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
