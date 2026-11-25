import OAI.Hierarchy.DescentOrdinaryHostPad
import OAI.Hierarchy.DescentRegisterTypes

namespace OAI
/-! # Align the three predecessor archives with the physical height of the next reset -/
namespace Hierarchy.DescentResetPriorHostPad
open DescentOrdinaryHostPad DescentSIMDLookup DescentSixParty.Chronology DescentDatedAddressBook ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

structure Shape where
  oldHosts : ℕ
  newHosts : ℕ
  groups : ℕ
  blocks : ℕ
  arguments : ℕ
  operandLanes : ℕ
  roleLanes : ℕ

namespace Shape
variable (s : Shape)

def dataRect : Rect := ⟨s.oldHosts,s.newHosts,s.groups,(2+7*s.arguments)*s.blocks,s.operandLanes⟩
def roleRect : Rect := ⟨s.oldHosts,s.newHosts,s.groups,s.blocks,s.roleLanes⟩
def roleStart (base : ℕ) := s.dataRect.finish base
def endAddress (base : ℕ) := s.roleRect.finish (s.roleStart base)
def operandBank (base : ℕ) (j : Fin s.dataRect.pages) := s.dataRect.bank base j
def roleBank (base : ℕ) (j : Fin s.blocks) := s.roleRect.bank (s.roleStart base) j

/-- The two metadata pages begin directly at the front of the output. The
physical metadata-layout flag selects this direct row address. -/
def history (base : ℕ) (prev : PriorResetArchive) : PriorResetArchive :=
  ⟨base,base+(2*s.blocks)*s.dataRect.rows,true,
    ⟨s.roleStart base,s.roleRect.rows,Nat.clog 2 (s.roleRect.rows+1),s.blocks⟩,prev.count⟩

def phase (base : ℕ) (src : Fin s.dataRect.pages→Bank) (role : Fin s.blocks→Bank) (w : ℕ) : NativePhase w :=
  (s.dataRect.phase base src w).seq (s.roleRect.phase (s.roleStart base) role w)

theorem translated (base : ℕ) : s.endAddress base=base+s.endAddress 0:=by
  unfold endAddress roleStart
  rw [s.roleRect.translated (s.dataRect.finish base),s.roleRect.translated (s.dataRect.finish 0),
    s.dataRect.translated base,Nat.add_assoc]

theorem cuts (base : ℕ) : base≤ s.roleStart base ∧ s.roleStart base≤ s.endAddress base:=
  ⟨s.dataRect.base_le _,s.roleRect.base_le _⟩

theorem any {w : ℕ} (base : ℕ) (src : Fin s.dataRect.pages→Bank) (role : Fin s.blocks→Bank)
    (m : Memory w) (sources : ∀j,(src j).Fits w base) (roles : ∀j,(role j).Fits w base)
    (room : s.endAddress base<2^w) :
    (s.phase base src role w).Runs m ∧
    ∀i,i<base ∨ s.endAddress base≤ i → (s.phase base src role w).image m i=m i :=by
  obtain ⟨b,e⟩:=s.cuts base
  have first:=s.dataRect.any base src m sources (e.trans_lt room)
  let mid:=(s.dataRect.phase base src w).image m
  have after : ∀j,(role j).Fits w (s.roleStart base):=fun j=>⟨(roles j).1,(roles j).2.1,(roles j).2.2.trans b⟩
  have last:=s.roleRect.any (s.roleStart base) role mid after room
  refine ⟨NativePhase.seq_runs _ _ _ first.1 last.1,?_⟩
  intro i outside
  change (s.roleRect.phase (s.roleStart base) role w).image mid i=m i
  rw [last.2 i (outside.imp (fun t=>t.trans_le b) id)]
  exact first.2 i (outside.imp id (fun t=>e.trans t))

theorem operand_fit {w : ℕ} (base : ℕ) (room : s.endAddress base<2^w) (j : Fin s.dataRect.pages) :
    (s.operandBank base j).Fits w (s.endAddress base) ∧ s.dataRect.rows≤(s.operandBank base j).size:=by
  have h:=s.dataRect.placed base ((s.cuts base).2.trans_lt room) j
  exact ⟨⟨h.1.1,h.1.2.1,h.1.2.2.trans (s.cuts base).2⟩,h.2⟩

theorem role_fit {w : ℕ} (base : ℕ) (room : s.endAddress base<2^w) (j : Fin s.blocks) :
    (s.roleBank base j).Fits w (s.endAddress base) ∧ s.roleRect.rows≤(s.roleBank base j).size:=
  s.roleRect.placed _ room j

end Shape
end
end Hierarchy.DescentResetPriorHostPad

end OAI
