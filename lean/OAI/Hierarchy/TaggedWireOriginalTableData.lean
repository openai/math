import OAI.Hierarchy.TaggedWireRolePageCore
import OAI.Hierarchy.TaggedWirePublicPorts
import OAI.Hierarchy.TaggedWireRoleIndices

namespace OAI
/-! # Tables of static original roles and signed site ordinals -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe WireTelescope ReportSockets ProtocolRAM
open scoped Classical Fin.CommRing
variable {h W k attempts edges R : ℕ} (S : PurchaseSampler)

abbrev Axis (k : ℕ) := Fin k × Bool

/-- The signed axis plus physical site uniquely recovers the public altimeter
port, including the central input where both signs share a site. -/
def altKey (q : StageColumns h (2^W) × Axis k) :=
  ((name (goodsSite (.inr q) : Site h (2^W) k)),q.2)

theorem altKey_injective : Function.Injective (altKey (h:=h) (W:=W) (k:=k)) := by
  rintro ⟨u,l⟩ ⟨v,s⟩ eq
  have pos := name.injective (congrArg Prod.fst eq)
  have col : u=v := Sum.inl.inj (Sum.inr.inj (congrArg Prod.fst pos))
  have axis := congrArg Prod.snd eq
  exact Prod.ext col axis

def altTable (S : PurchaseSampler) (h W k attempts : ℕ)
    (i : Fin ((siteLast h (2^W) k+1)*(2*k))) : ℕ :=
  let (v,l):=finProdFinEquiv.symm i
  let E:=Fintype.equivFin (Axis k)
  let x : Axis k:= E.symm (Fin.cast (by simp [Axis,Nat.mul_comm]) l)
  if yes:∃z:StageColumns h (2^W)×Axis k,altKey z=(v,x) then
    (Fintype.equivFin (Public S h W k attempts) (.inr (.inl (.inr yes.choose)))).val else 0

def axisCode (x : Axis k) : Fin (2*k) :=
  Fin.cast (by simp [Axis,Nat.mul_comm]) (Fintype.equivFin _ x)

def exteriorTable (h W k attempts : ℕ) (S : PurchaseSampler) (side : Bool) (p : Fin (2^h)) :=
  (Fintype.equivFin (Public S h W k attempts) (.inr (.inl (.inl (p,side))))).val

/-- A held altimeter uses the center input of its owner's tile and its actual
signed-layer output. The two row ordinals only depend on the original item. -/
def altRow (order : Fin R≃Edges S h (2^W) k) (p : Fin (2^h)) (t : StageAt h (2^W)) (l : Axis k) (side : Bool) :=
  order.symm (.inr ((p,t),if side then some l else none))

def freeTable (order : Fin R≃Edges S h (2^W) k) (attempts : ℕ) (b : Bool) (i : Fin R) : ℕ :=
  match order i with
  | .inl f=>(Fintype.equivFin (Public S h W k attempts) (.inl (.inl (f,b)))).val
  | .inr _=>0

/-- A public per-item row, independent of all earlier paid/tag values. -/
def metadata (order : Fin R≃Edges S h (2^W) k) (attempts edges : ℕ) (x : Old h W k edges) : Fin 7→ℕ :=
  match x with
  | .inl e=>![0,e.val,0,0,0,0,0]
  | .inr (.inl (.inl p))=>![1,p.val,0,0,0,0,0]
  | .inr (.inl (.inr ((p,t),l)))=>![2,0,(altRow S order p t l false).val,(altRow S order p t l true).val,(axisCode l).val,0,0]
  | .inr (.inr c)=>![3,0,0,0,0,
    (Fintype.equivFin (Public S h W k attempts) (.inr (.inr (c,false)))).val,
    (Fintype.equivFin (Public S h W k attempts) (.inr (.inr (c,true)))).val]

def metadataTable (order : Fin R≃Edges S h (2^W) k) (attempts edges : ℕ) (j : Fin 7)
    (i : Fin (Fintype.card (Old h W k edges))) :=
  metadata S order attempts edges (SettledMatrix.Layout.numbered (r:=edges) i) j

def «meta» (base old : ℕ) (j : Fin 7) := RoleROM.expr (base+j.val*old) old .row

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
end

end OAI
