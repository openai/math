import OAI.Hierarchy.DescentDatedActorGate
import OAI.Hierarchy.DescentDatedActorAperture
import OAI.Hierarchy.DescentResetAnyActorDirectory
import OAI.Hierarchy.DescentSharedBookScan

namespace OAI
/-! Publish the shape-major actor plane, compact the new hosts and retain both true name directions. -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentActorRaster DescentResetNewActorDirectory ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option maxHeartbeats 1600000
variable {w : ℕ} (v : ActorSetup)
structure Inputs where
  population : Bank
  depths : Bank
  shared : DescentSharedBookScan.Chart
  degree : ℕ
  treeCap : ℕ
  control : Fin v.shapes→Headers.Control
  query : Fin v.shapes→CPU.Query
  stencil : Expr

variable (u : v.Inputs)
local notation "book" => DescentSharedBookScan.expr u.shared v.hosts u.degree u.treeCap

def actorBody (base w : ℕ) :=
  ((v.headers base u.depths book w).seq (v.operator base u.population u.control u.query u.stencil (w:=w))).seq ((v.directory base).program w (v.scene base))
def actorTicks (base w : ℕ) :=
  (v.headerTime base u.depths book w + v.operatorTime base u.population u.control u.query u.stencil w)+(v.directory base).ticks (v.scene base)

structure Ready (base w : ℕ) : Prop where
  raw : u.depths.Fits w base
  refs : (book).Fits w base
  gates : v.GateFits base u.population u.control u.stencil w
  parts : v.chunksPerHost≤2^w
  room : v.directoryEnd base<2^w

def classifier (base w : ℕ) := (v.headers base u.depths book w).seq (v.operator base u.population u.control u.query u.stencil (w:=w))
def classifierTime (base w : ℕ) := v.headerTime base u.depths book w + v.operatorTime base u.population u.control u.query u.stencil w

private theorem compose_dated_parts (A B C : Procedure w) (m h g : Memory w)
    (lo cut stop hi ta tb tc : ℕ) (loCut : lo≤cut) (cutStop : cut ≤ stop) (stopHi : stop ≤ hi)
    (first : A.Exec m h ta ∧ CheapCode A ∧ ∀z,z<lo ∨ cut≤z → h z=m z)
    (second : B.Exec h g tb ∧ CheapCode B ∧ ∀z,z<cut ∨ stop ≤ z → g z=h z)
    (third : ∃out : Memory w,C.Exec g out tc ∧ CheapCode C ∧ ∀z,z < stop ∨ hi≤z → out z=g z) :
    ∃mid out : Memory w,(A.seq B).Exec m mid (ta+tb) ∧ C.Exec mid out tc ∧
      CheapCode ((A.seq B).seq C) ∧ ∀z,z<lo ∨ hi≤z → out z=m z := by
  obtain ⟨scan,cheapA,frameA⟩ := first
  obtain ⟨operate,cheapB,frameB⟩ := second
  obtain ⟨out,publish,cheapC,frameC⟩ := third
  refine ⟨g,out,?_,@publish,cheap_seq (cheap_seq cheapA cheapB) cheapC,?_⟩
  · intro labels regs keys machine
    exact Procedure.Exec.then (A:=A) (B:=B) (a:=m) (b:=h) (c:=g) scan operate machine
  · intro z away
    have fc := frameC z (away.imp (fun h=>h.trans_le (loCut.trans cutStop)) id)
    have fb := frameB z (away.imp (fun h=>h.trans_le loCut) (fun h=>stopHi.trans h))
    have fa := frameA z (away.imp id (fun h=>(cutStop.trans stopHi).trans h))
    exact fc.trans (fb.trans fa)

private theorem dated_ranges (base : ℕ) :
    base≤(v.gate base).scalar ∧ (v.gate base).scalar≤v.endAddress base ∧
      v.endAddress base≤v.directoryEnd base ∧ (v.scene base).size≤v.endAddress base := by
  have gateLo : base≤(v.gate base).scalar := by
    obtain ⟨d,c,s,l,h⟩ := v.monotone base
    omega
  obtain ⟨scalarEnd,repeatEnd,gateEnd⟩ := v.gate_order base
  have repeatLo : (v.gate base).repeatBase≤(v.gate base).gateBase := by
    rw [←repeatEnd]
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have sceneEnd : (v.gate base).output+(v.scene base).size=v.endAddress base := rfl
  have scalarEndLe : (v.gate base).scalar≤v.endAddress base := by omega
  have high : v.endAddress base≤v.directoryEnd base := Nat.le_add_right _ _
  exact ⟨gateLo,scalarEndLe,high,(Nat.le_add_left _ _).trans sceneEnd.le⟩

set_option maxHeartbeats 3200000 in
theorem dated_parts (base : ℕ) (m : Memory w) (ready : v.Ready u base w) :
    ∃mid out : Memory w,(v.classifier u base w).Exec m mid (v.classifierTime u base w) ∧
      ((v.directory base).program w (v.scene base)).Exec mid out ((v.directory base).ticks (v.scene base)) ∧
      CheapCode (v.actorBody u base w) ∧ ∀z,z<base ∨ v.directoryEnd base≤z→ out z=m z := by
  obtain ⟨loCut,cutStop,stopHi,sizeEnd⟩ := dated_ranges v base
  let h := v.headerImage base u.depths book m
  let g := v.operatorImage base u.population u.control u.query u.stencil h
  have sceneFits : (v.scene base).Fits w (v.directory base).first :=
    ⟨Nat.two_pow_pos _,sizeEnd.trans_lt ready.gates.endFit,le_rfl⟩
  exact compose_dated_parts (v.headers base u.depths book w)
    (v.operator base u.population u.control u.query u.stencil (w:=w))
    ((v.directory base).program w (v.scene base)) m h g
    base (v.gate base).scalar (v.endAddress base) (v.directoryEnd base)
    (v.headerTime base u.depths book w) (v.operatorTime base u.population u.control u.query u.stencil w)
    ((v.directory base).ticks (v.scene base)) loCut cutStop stopHi
    (v.headers_any base u.depths book m ready.raw ready.refs (cutStop.trans_lt ready.gates.endFit))
    (v.operator_any base u.population u.control u.query u.stencil h ready.gates)
    ((v.directory base).any (v.scene base) g sceneFits ready.parts ready.room)

theorem dated_any (base : ℕ) (m : Memory w) (ready : v.Ready u base w) :
    ∃out : Memory w,(v.actorBody u base w).Exec m out (v.actorTicks u base w) ∧ CheapCode (v.actorBody u base w) ∧
      ∀z,z<base ∨ v.directoryEnd base≤z→ out z=m z := by
  obtain ⟨mid,out,scan,publish,cheap,frame⟩:=v.dated_parts u base m ready
  refine ⟨out,?_,cheap,frame⟩
  intro labels regs keys machine
  exact Procedure.Exec.then (A:=v.classifier u base w) (B:=(v.directory base).program w (v.scene base))
    (a:=m) (b:=mid) (c:=out) scan publish machine


end
end Hierarchy.DescentDatedAddressBook.ActorSetup

end OAI
