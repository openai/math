import OAI.Hierarchy.DescentClosedReset
import OAI.Hierarchy.DescentResetExteriorRows
import OAI.Hierarchy.DescentPinCohorts
import OAI.Hierarchy.DescentExteriorPublicPins

namespace OAI
/-! # Exterior coordinate retained by a recorded reset -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentRelativeContacts
open scoped Classical
noncomputable section

private theorem named_pin {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V]
    [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (s : Equiv.Perm W.graph.Site)
    (e : Equiv.Perm W.graph.Edge) (eqn : W'=PhysicalRename.world W s e) (p : P) :
    let A' : GroupStage W' G q ε J V k := eqn.symm ▸ A.names s e
    A'.pos (W'.graph.attach p)=A.pos (W.graph.attach p) ∧
      A'.block (W'.graph.attach p)=A.block (W.graph.attach p) := by
  subst W'
  change A.pos (s.symm (s (W.graph.attach p)))=_ ∧ A.block (s.symm (s (W.graph.attach p)))=_
  simp

namespace ClosedReset
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail : ℕ}
    {W : MarkedWorld F d P bits} {input : Reached W G q ε S k i z D w hist}
    {ctl : ResetRates G S k D n h C f g cut tail} (b : ClosedReset input ctl)

local notation "oldPin" => W.graph.attach
local notation "side" => S.groupWidth k tail i
local notation "digit" => S.resetOutputDigits ctl.base ctl.radix b.age b.commonDepth
local notation "ord" => StarKeys.filled W.graph input.placement.pos input.placement.block
  (S.resetInputDigits ctl.base ctl.radix i)

theorem raw_pin (p : P) :
    b.next.placement.pos (b.reblock.result.graph.attach p) =
      b.reset.groupPosition b.terminals digit ((b.reset.reenter b.terminals).graph.attach p) ∧
    b.next.placement.block (b.reblock.result.graph.attach p) =
      b.reset.groupBlock b.terminals digit ((b.reset.reenter b.terminals).graph.attach p) := by
  obtain ⟨pos,block⟩ := b.rawGeometry
  let vertex := b.frame.host.symm.toEmbedding.trans input.vertex
  let key := DescentOrderedReset.grains W b.count b.order
  let norm := b.reset.orderedReblock b.terminals key
  let rank := (b.reset.rawHostRank b.terminals vertex).trans Fin.valEmbedding
  let rows := DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n := S.groupCount (i+1))) rank
  let site := b.raw.siteFrom rows b.valid.coordinates
  let tape := b.reset.nativeResetEdges b.terminals vertex key
  let edge := DescentResetLocalOrder.allCode b.raw (tape.order.trans Fin.valEmbedding) S b.valid site
  let sites := DescentPhysicalOrder.rename site
  let edges := DescentPhysicalOrder.rename edge
  have named : b.next.placement.pos (b.reblock.result.graph.attach p)=b.raw.pos ((b.reset.reenter b.terminals).graph.attach p) ∧
      b.next.placement.block (b.reblock.result.graph.attach p)=b.raw.block ((b.reset.reenter b.terminals).graph.attach p) :=
    named_pin b.raw sites edges (norm.appendNames_result sites edges) p
  exact ⟨named.1.trans (congrFun pos _),named.2.trans (congrFun block _)⟩

/-- Re-entry puts every public pin on the first trunk node of its physical
terminal. Erasing the coarse digits of a terminal preserves its old host. -/
theorem public_trunk (p : P) :
    (PinCohorts.host b.next p).val=
      DescentCommonHost.Node.trunk false (shortName b.terminals.commonDepth
        (b.terminals.code (b.terminals.home (oldPin p)))) := by
  change (b.next.placement.pos _).2.val=_
  rw [(b.raw_pin p).1]
  let view := Sum.elim
    (fun st : Bool × b.reset.Fallback =>
      DescentCommonHost.Node.trunk st.1 (shortName b.terminals.commonDepth (b.terminals.code st.2)))
    (DescentCommonHost.bankNode b.reset.placement b.reset.graph b.terminals.commonDepth
      b.terminals.code b.reset.positive b.reset.pay b.reset.circuit d)
  exact congrArg view (b.reset.read_source_pin b.terminals p)

theorem previous_host_of_equal {p p' : P} (same : PinCohorts.host b.next p=PinCohorts.host b.next p') :
    PinCohorts.host input p=PinCohorts.host input p' := by
  have physical:=congrArg Subtype.val same
  rw [b.public_trunk p,b.public_trunk p'] at physical
  have tag:=DescentCommonHost.Node.trunk.inj physical
  have name:=congrArg Prod.fst tag.2
  change (b.terminals.code (b.terminals.home (oldPin p))).1 =
    (b.terminals.code (b.terminals.home (oldPin p'))).1 at name
  exact b.frame.host.injective ((b.frame.homeHost (oldPin p)).symm.trans
    (name.trans (b.frame.homeHost (oldPin p'))))

/-- The frozen digits are precisely the low coordinates of the measured basis.
The next active coordinate is the high prefix of that same transformed address. -/
def pinStep (owns : ∀p,input.placement.hub (input.placement.pos (oldPin p)).2=true) :
    PinCohorts.Step input b.next ctl.base ctl.radix := by
  let eqn : side=S.groupWidth k tail (i+1)+k := S.group_cut b.age
  let L:=b.frame.basis
  let split:=L.trans (splitRows side k)
  refine ⟨split.trans ((castBits eqn).prodCongr (LinearEquiv.refl _ _)),?_,?_⟩
  · intro p
    let nextSite := b.reblock.result.graph.attach p
    let rawBlock := b.reset.blockId b.terminals ((b.reset.reenter b.terminals).graph.attach p)
    let nextDigits := S.resetInputDigits ctl.base ctl.radix (i+1)
    have named := b.raw_pin p
    have first := congrArg
      (fun u : Fin (S.groupCount (i+1)) × ↥(b.reset.commonNames b.terminals) => u.1) named.1
    have pair_eq : ((b.next.placement.pos nextSite).1, b.next.placement.block nextSite) =
        digit rawBlock :=
      Prod.ext first named.2
    have uncast : (nextDigits.symm (digit rawBlock)).val = rawBlock.val :=
      congrArg Fin.val (nextDigits.symm_apply_apply
        (finCongr (congrArg (fun s : ℕ => 2^s) (b.commonDepth.trans eqn)) rawBlock))
    have decoded : (nextDigits.symm ((b.next.placement.pos nextSite).1,
        b.next.placement.block nextSite)).val = rawBlock.val :=
      (congrArg (fun t => (nextDigits.symm t).val) pair_eq).trans uncast
    have old : rawBlock.val = group side (rearrange L (ord (oldPin p))) :=
      (ResetInput.source_pin_block (Z := b.reset) (T := b.terminals) b.frame p (owns p)).trans
        (congrArg (fun m : ℕ => group m (rearrange L (ord (oldPin p)))) b.commonDepth)
    have hi := (split_index side k L (ord (oldPin p))).1
    apply (address _).injective
    apply Fin.ext
    change (address _ (castBits eqn (split ((address _).symm (ord (oldPin p)))).1)).val =
      (address _ ((address _).symm (nextDigits.symm
        ((b.next.placement.pos nextSite).1, b.next.placement.block nextSite)))).val
    rw [address_cast, Equiv.apply_symm_apply]
    exact hi.trans (old.symm.trans decoded.symm)
  · intro p p' same low
    apply Subtype.ext
    rw [b.public_trunk p,b.public_trunk p',b.frame.atHub _ (owns p),b.frame.atHub _ (owns p'),b.commonDepth]
    have sameHost : (input.placement.pos (oldPin p)).2=(input.placement.pos (oldPin p')).2:=same
    rw [sameHost]
    have enough : side≤ side+k-g := by simpa only [b.commonDepth] using b.frame.enough
    have reg : side+k-k=side := by omega
    have val := congrArg (fun x : Bits k => (address k x).val) low
    change (address k (split ((address _).symm (ord (oldPin p)))).2).val =
      (address k (split ((address _).symm (ord (oldPin p')))).2).val at val
    have resid : residue k (rearrange L (ord (oldPin p))) =
        residue k (rearrange L (ord (oldPin p'))) := by
      apply Fin.ext
      exact ((split_index side k L (ord (oldPin p))).2).symm.trans
        (val.trans (split_index side k L (ord (oldPin p'))).2)
    have norm (x : Block (side+k)) :
        group (side+k-g) x % 2^(side+k-g-side) =
          group (side+k-g-side) (residue k x) := by
      simpa only [reg] using
        id_relative (Nat.le_add_left k side) (show side+k-k ≤ side+k-g by omega)
          (Nat.sub_le (side+k) g) x
    have groupEq :=
      (norm (rearrange L (ord (oldPin p)))).trans
        ((congrArg (fun y : Block k => group (side+k-g-side) y) resid).trans
          (norm (rearrange L (ord (oldPin p')))).symm)
    exact congrArg (fun x : ℕ =>
      DescentCommonHost.Node.trunk false
        (b.frame.host (input.placement.pos (oldPin p')).2, ((side+k-g-side, x), none))) groupEq

end ClosedReset
end
end Hierarchy.DescentSixParty

end OAI
