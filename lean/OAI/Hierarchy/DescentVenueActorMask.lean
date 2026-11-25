import OAI.Hierarchy.DescentStageVenueBookLayout
import OAI.Hierarchy.DescentPackedColumnSum
import OAI.Hierarchy.DescentPackedMatchPrepareIssued

namespace OAI
/-! # Publishing the next matcher actor word from the actual bit on each block -/
namespace Hierarchy.DescentActorRaster.Venue
open DescentSixParty DescentSIMDLookup DescentPackedColony DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentPackedZip
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W gadget q ε J V k) (groups : J↪Fin G) (hosts : V↪Fin H)

def actual (x : Fin (2^k)) (h : Fin H) (g : Fin G) : Cell 1 :=
  if ∃u : W.graph.Site, hosts (A.pos u).2=h ∧ groups (A.pos u).1=g ∧ A.block u=x then 1 else 0

theorem actor_word (h : Fin H) (g : Fin G) :
    encode 1 (2^k) (fun x=>actual A groups hosts x h g)=Prepare.actors A groups hosts h g := by
  unfold Prepare.actors Prepare.spreadField
  split
  next hp =>
    unfold actorMask
    apply congrArg (encode 1 (2^k))
    funext x
    unfold actual present
    have same : (∃u : W.graph.Site,hosts (A.pos u).2=h ∧ groups (A.pos u).1=g ∧ A.block u=x) ↔
        ∃u : W.graph.Site,A.pos u=hp.choose ∧ A.block u=x := by
      constructor
      · rintro ⟨u,loc,grp,atx⟩
        exact ⟨u,Prod.ext (groups.injective (grp.trans hp.choose_spec.1.symm))
          (hosts.injective (loc.trans hp.choose_spec.2.symm)),atx⟩
      · rintro ⟨u,where_,atx⟩
        exact ⟨u,by simpa only [where_] using hp.choose_spec.2,by simpa only [where_] using hp.choose_spec.1,atx⟩
    simp only [same]
  next hp =>
    have vacant (x : Fin (2^k)) : actual A groups hosts x h g=0:=by
      apply ite_eq_right
      rintro ⟨u,hu,gu,_⟩
      exact hp ⟨A.pos u,gu,hu⟩
    apply Fin.ext
    change (finFunctionFinEquiv _).val=0
    rw [finFunctionFinEquiv_apply]
    simp [vacant]

def place (x : Fin (2^k)) (b : Cell 1) := b.val*2^x.val
def output (base k H G M : ℕ) : Bank :=⟨outBase base k M,Nat.clog 2 (H*chunks G M)⟩
def program (w base k H G M : ℕ) (src : Fin (2^k)→Expr) :=
  DescentPackedColumnSum.program w base (outBase base k M) 1 M (1*2^k) H G (fun _=>1) place src
def ticks (base k H G M : ℕ) (src : Fin (2^k)→Expr) :=
  DescentPackedColumnSum.ticks base 1 M H G (fun _ : Fin (2^k)=>1) src
def after (base k H G M : ℕ) (src : Fin (2^k)→Expr) (m : Memory w) :=
  DescentPackedColumnSum.after base (outBase base k M) 1 M (1*2^k) H G (fun _=>1) place src m

theorem run (base : ℕ) (src : Fin (2^k)→Expr) (m : Memory w) (fits : ∀x,(src x).Fits w base)
    (issued : ∀x,Source (src x) (actual A groups hosts x) M m)
    (room : outBase base k M+H*chunks G M<2^w) :
    let next:=after base k H G M src m
    (program w base k H G M src).Exec m next (ticks base k H G M src) ∧
      Reads (output base k H G M) (Prepare.actors A groups hosts) M next ∧
      (∀a,a<base ∨ outBase base k M+H*chunks G M≤a→next a=m a) ∧
      CheapCode (program w base k H G M src) := by
  apply DescentPackedColumnSum.run _ _ 1 M (1*2^k) H G _ _ src (actual A groups hosts)
  · intro x;simp [place]
  · intro h g;rw [←actor_word A groups hosts h g]
    change _=(finFunctionFinEquiv _).val
    rw [finFunctionFinEquiv_apply]
    simp [place]
  · exact fun _=>le_rfl
  · exact fits
  · exact issued
  · exact le_rfl
  · exact room

end
end Hierarchy.DescentActorRaster.Venue

end OAI
