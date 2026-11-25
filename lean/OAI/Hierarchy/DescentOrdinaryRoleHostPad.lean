import OAI.Hierarchy.DescentOrdinaryRoleRetile
import OAI.Hierarchy.DescentOrdinaryHostPad

namespace OAI
/-! Repitch primitive roles on the predecessor's genuine host rectangle, then pad them to the current
ordinary host grid. The new deck is emitted for all current hosts, including the absent tail. -/
namespace Hierarchy.DescentOrdinaryRoleHostPad
open DescentSIMDLookup DescentPackedColony ProtocolRAM DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
structure Layout where
  blocks : ℕ
  oldHosts : ℕ
  hosts : ℕ
  groups : ℕ
  beforeLanes : ℕ
  afterLanes : ℕ
  bits : ℕ
namespace Layout
variable (L : Layout) (base : ℕ) (input : Fin L.blocks→Bank)
def retile : DescentOrdinaryRoleRetile.Layout :=⟨L.blocks,L.oldHosts,L.groups,L.beforeLanes,L.afterLanes,L.bits⟩
def rect : DescentOrdinaryHostPad.Rect :=⟨L.oldHosts,L.hosts,L.groups,L.blocks,L.afterLanes⟩
def split :=L.retile.roof base
def roof :=L.rect.finish (L.split base)
def bank (x : Fin L.blocks) :=L.rect.bank (L.split base) x
def phase (w : ℕ) : NativePhase w :=
  (L.retile.phase base input w).seq (L.rect.phase (L.split base) (L.retile.bank base) w)
def rows :=L.hosts*chunks L.groups L.afterLanes
theorem translated : L.roof base=base+L.roof 0:=by
  rw [roof,L.rect.translated,split,L.retile.translated,roof,L.rect.translated (L.split 0),split]
  omega
theorem base_le : base≤L.roof base:=by rw [L.translated];exact Nat.le_add_right ..
theorem placed {w : ℕ} (room : L.roof base<2^w) (x : Fin L.blocks) :
    (L.bank base x).Fits w (L.roof base) ∧ L.rows≤(L.bank base x).size:=L.rect.placed (L.split base) room x
variable {w : ℕ} (m : Memory w) (fits : ∀x,(input x).Fits w base) (room : L.roof base<2^w)
include fits room
theorem any : (L.phase base input w).Runs m ∧ ∀i,i<base ∨ L.roof base ≤ i → (L.phase base input w).image m i=m i:=by
  have low : base≤L.split base := L.retile.base_le base
  have high : L.split base≤L.roof base := L.rect.base_le (L.split base)
  have safe : L.split base<2^w := high.trans_lt room
  let mid:=(L.retile.phase base input w).image m
  have first:=L.retile.any base input m fits safe
  have last:=L.rect.any (L.split base) (L.retile.bank base) mid
    (fun x=>(L.retile.placed base safe x).1) room
  exact ⟨NativePhase.seq_runs _ _ m first.1 last.1,fun i hi=>
    (last.2 i (hi.imp_left (·.trans_le low))).trans (first.2 i (hi.imp_right (high.trans ·)))⟩
theorem reads (x : Fin L.blocks) (value : Fin L.oldHosts→Fin L.groups→Cell L.bits)
    (live : 0<L.beforeLanes) (span : L.oldHosts*chunks L.groups L.beforeLanes≤(input x).size)
    (read : Reads (input x) value L.beforeLanes m) :
    Reads (L.bank base x) (DescentOrdinaryHostPad.extend L.hosts value) L.afterLanes ((L.phase base input w).image m):=by
  have safe : L.split base<2^w := (L.rect.base_le (L.split base)).trans_lt room
  have old:=L.retile.reads base input m fits safe x value live span read
  exact L.rect.reads (L.split base) (L.retile.bank base) _ (fun i=>(L.retile.placed base safe i).1) room x value
    (L.retile.placed base safe x).2 old
end Layout
end
end Hierarchy.DescentOrdinaryRoleHostPad

end OAI
