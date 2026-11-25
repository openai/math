import OAI.Hierarchy.DescentDatedPublicPacketRows
import OAI.Hierarchy.DescentDatedPacketSnapshot

namespace OAI
/-! # Looking up the component actually emitted from each of the two original packed root operands -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedColony DescentSIMDLookup DescentPackedZip DescentOperandRootPull ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {A : PhysicalReset} {floor w : ℕ} (u : A.DateInputs floor w) (ok : u.Ready)
local notation "v" => A.successor
local notation "b" => A.rebased floor
local notation "C" => (v).setup
local notation "O" => (C).packets
local notation "base" => (v).operandFloor b
local notation "start" => (C).placed base
local notation "root" => A.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "head" => A.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => A.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "actBase" => (v).middle.stop b
local notation "actors" => (v).actor.actorBody u.actor actBase w
local notation "atime" => (v).actor.actorTicks u.actor actBase w
local notation "scene" => (v).front.trunkScene ((v).actorEnd b) ((v).issuedScene b u.earlier) u.sceneFits

variable (active : Expr) (regs : Fin 4→Expr)
local notation "pub" => OperandMenu.publicPorts (a:=A) u.shape floor u.count u.hub u.g u.Y active regs
local notation "packed" f:arg => Cell ((O).oldBits*((O).stage 0 f).fields)
variable (words : ∀f : Bool, Fin A.successor.setup.packets.actors → Fin (A.successor.setup.packets.groups*A.successor.setup.packets.blocks) → Cell (A.successor.setup.packets.oldBits * (A.successor.setup.packets.stage 0 f).fields))
    (owner : Fin A.successor.setup.packets.receivers → Fin A.successor.setup.packets.actors)
local notation:max "content" f:arg h:arg g:arg j:arg => (encode (O).oldBits ((O).stage 0 f).fields).symm (words f h g) j

/-- The native two-root gather has one genuine source array for each of its requested printed fields.
The input packed words remain identifiable even when they are zero or contain an unpaid operand. -/
theorem public_packed_rows (initial afterRoots atActors : Memory w)
    (produced : (head).Exec initial afterRoots ht) (extras : (actors).Exec afterRoots atActors atime)
    (original : ∀f,((O).original f).Fits w ((root).preparedEnd u.book) ∧
      Source ((O).original f) (words f) (O).beforeLanes afterRoots)
    (parents : DescentResetStemKeyReindex.Directory (O).parent owner ((scene).image atActors))
    (kept : (O).parent+(O).receivers≤(v).trunkEnd b) (positive : 0<(O).beforeLanes)
    (word : (O).endAddress start<2^w) (bits : (pub).casts.width 0=(O).oldBits)
    (lane : (pub).casts.lanes=(O).afterLanes) :
    ∃data : (f : Bool)→Fin ((O).stage 0 f).fields→Fin (O).blocks→
        Fin (O).receivers→Fin (O).groups→Cell ((pub).casts.width 0),
      (∀f j z,let t:=(pub).packets.src (pub).packetBase f j z
        t.Fits w (pub).castBase ∧ Source t (data f j z) (pub).casts.lanes
          ((pub).packets.image (pub).packetBase (u.beforePacketImage ok atActors))) ∧
      ∀f j z h g,(data f j z h g).val=(content f (owner h) (finProdFinEquiv (g,z)) j).val :=by
  obtain ⟨m,chosen,_,_,_,frame⟩:=u.before_packet_from_roots ok produced
  have eqn : m=atActors:=ProtocolRAM.exec_unique _ _ _ _ chosen extras
  subst m
  let m₀:=u.beforePacketImage ok atActors
  have mounted : DescentResetStemKeyReindex.Directory (O).parent owner m₀:=by
    intro j
    exact ((u.before_packet_scene ok atActors) _ (.inl (lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) kept))).trans (parents j)
  have held (f : Bool) : Source ((O).original f)
      (fun h g=>encode (O).oldBits ((O).stage 0 f).fields (fun j=>content f h g j)) (O).beforeLanes m₀:=by
    simp only [Equiv.apply_symm_apply]
    intro p
    exact (eval_below _ _ _ _ (original f).1 (fun n hn=>frame n (.inl hn))).trans ((original f).2 p)
  have got:=(O).read start m₀ (fun f h g j=>content f h g j) owner ok.placed.packets positive held mounted word
  let data := fun (f : Bool) (j : Fin ((O).stage 0 f).fields) (z : Fin (O).blocks) (h : Fin (O).receivers) (g : Fin (O).groups) =>(content f (owner h) (finProdFinEquiv (g,z)) j).cast (congrArg (2^·) bits.symm)
  refine ⟨data,?_,fun _ _ _ _ _=>rfl⟩
  intro f j z
  refine ⟨(got f j z).1,?_⟩
  have restore {aa bb : ℕ} (eqn : aa=bb) {pitch₀ : ℕ} {F₀ : Fin (O).receivers→Fin (O).groups→Cell bb}
      {t : Expr} {mem : Memory w} (rd : Source t F₀ pitch₀ mem) :
      Source t (fun h g=>(F₀ h g).cast (congrArg (2^·) eqn.symm)) pitch₀ mem:=by subst aa;exact rd
  rw [lane]
  exact restore bits (got f j z).2

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
