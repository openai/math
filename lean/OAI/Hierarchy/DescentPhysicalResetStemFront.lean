import OAI.Hierarchy.DescentDatedCandidateFront
import OAI.Hierarchy.DescentResetParentDate
import OAI.Hierarchy.DescentResetStemProjected

namespace OAI
/-! # One parent directory and all stem lookups on a fixed reset's actual address book -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentDyadicSpan DescentResetStemPackedIssue DescentResetStemIncidence ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront)
local notation "p₀" => v.peer
structure StemInputs where
  flags : Bank
  parse : DescentResetStemKey.Decoder (p₀).oldDegree v.stemField
  side : Fin v.signedQueries→Bool
  operands : Fin v.signedQueries→Fin ((p₀).oldDegree+2)→Expr
  ports : DescentResetStemIncidence.Ports (2*v.oldTicketCount)
  queries : v.projectionCount=v.signedQueries*((p₀).oldDegree+2)
  digits : v.projectionBits=v.stemField

variable (s : v.StemInputs) (floor : ℕ)
local notation "start₀" => v.parentStart floor
local notation "start₁" => v.parentEnd floor
local notation "ptr" => (v.parent floor).base
local notation "h₀" => (p₀).oldHosts
local notation "h₁" => v.newHosts
local notation "D" => (p₀).oldDegree
local notation "f" => v.stemField
local notation "b" => v.metaBits
local notation "g" => (p₀).groups
local notation "M" => (p₀).lanes
local notation "P" w => Mixed.Projected.program start₁ ptr b h₀ h₁ g v.blocks v.oldLanes M s.parse s.side s.operands s.ports w

include s in
theorem stem_boundary :
    Mixed.Projected.extent start₁ ptr D f b v.oldTicketCount h₀ h₁ g v.blocks v.oldLanes M v.signedQueries=v.mixed floor := by
  unfold Mixed.Projected.extent Mixed.Projected.splitAt mixed projected
  rw [s.queries,s.digits]

structure StemRoom (w : ℕ) : Prop where
  prev : s.flags.Fits w start₀
  bitmap : (p₀).hosts≤ s.flags.size
  positive : 0<M
  blocks : 0<v.blocks
  sources : ∀q i,(s.operands q i).Fits w start₁
  ports : s.ports.All (Expr.Fits w start₁)
  final : v.mixed floor<2^w

theorem front_order : start₀≤ start₁ ∧ start₁≤v.mixed floor ∧ ptr+span h₁≤ start₁ := by
  have low:=DescentResetParentAperture.extent start₀ (p₀).hosts h₁
  have high:=Mixed.affine (v.projected floor) ptr D f b v.oldTicketCount h₀ h₁ g M v.blocks v.signedQueries
  have pre:=DescentResetStemProject.extent start₁ v.projectionCount h₀ g v.blocks v.projectionBits v.oldLanes M
  refine ⟨by change start₀≤DescentResetParentAperture.endAddress start₀ (p₀).hosts h₁; omega,?_,?_⟩
  · unfold mixed
    rw [high]
    unfold projected
    rw [pre]
    omega
  · change DescentResetParentAperture.bins start₀ (p₀).hosts h₁+span h₁≤
        DescentResetParentAperture.bins start₀ (p₀).hosts h₁+max (h₁+1) (span h₁)
    exact Nat.add_le_add_left (Nat.le_max_right ..) _

def stemFront (w : ℕ) (room : v.StemRoom s floor w) :=
  (DescentResetParentDate.program start₀ (p₀).hosts h₁ (p₀).shapes s.flags w
    ((v.front_order floor).2.1.trans_lt room.final)).seq (P w)
def stemTime (w : ℕ) (room : v.StemRoom s floor w) :=
  DescentResetParentDate.ticks start₀ (p₀).hosts h₁ s.flags w ((v.front_order floor).2.1.trans_lt room.final)+
    Mixed.Projected.ticks start₁ ptr b h₀ h₁ g v.blocks v.oldLanes M s.parse s.side s.operands s.ports w
def stemImage {w : ℕ} (room : v.StemRoom s floor w) (m : Memory w) :=
  Mixed.Projected.image start₁ ptr b h₀ h₁ g v.blocks v.oldLanes M s.parse s.side s.operands s.ports
    (DescentResetParentDate.memory start₀ (p₀).hosts h₁ (p₀).shapes s.flags m ((v.front_order floor).2.1.trans_lt room.final))

theorem stem_any {w : ℕ} (room : v.StemRoom s floor w) (m : Memory w) :
    (v.stemFront s floor w room).Exec m (v.stemImage s floor room m) (v.stemTime s floor w room) ∧
    (∀x,x<start₀ ∨ v.mixed floor≤x → v.stemImage s floor room m x=m x) ∧ CheapCode (v.stemFront s floor w room) := by
  obtain ⟨lo,mid,banks⟩:=v.front_order floor
  let p:=DescentResetParentDate.memory start₀ (p₀).hosts h₁ (p₀).shapes s.flags m (mid.trans_lt room.final)
  have one:=DescentResetParentDate.any start₀ (p₀).hosts h₁ (p₀).shapes s.flags m room.prev room.bitmap (mid.trans_lt room.final)
  have two:=Mixed.Projected.any_full start₁ ptr b h₀ h₁ g v.blocks v.oldLanes M s.parse s.side s.operands s.ports p
    room.positive room.blocks room.sources room.ports banks (by rw [v.stem_boundary s floor];exact room.final)
  let parent := DescentResetParentDate.program start₀ (p₀).hosts h₁ (p₀).shapes s.flags w
    (mid.trans_lt room.final)
  refine ⟨@Procedure.Exec.then w parent (P w) m p (v.stemImage s floor room m) _ _ one.1 two.1, ?_,
    @cheap_seq w parent (P w) (@one.2.1) (@two.2.2)⟩
  rintro i (small|big)
  · exact (two.2.1 i (.inl (small.trans_le lo))).trans (one.2.2.1 i (.inl small))
  · exact (two.2.1 i (.inr (by rw [v.stem_boundary s floor];exact big))).trans (one.2.2.1 i (.inr (mid.trans big)))

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
