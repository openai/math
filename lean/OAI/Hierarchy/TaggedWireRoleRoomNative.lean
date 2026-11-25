import OAI.Hierarchy.TaggedWireRoleTableROM
import OAI.Hierarchy.TaggedWireRoleRoomShape
import OAI.Hierarchy.TaggedWireOriginalTableData
import OAI.Hierarchy.TaggedWireRoleProgramCore
import OAI.Hierarchy.TaggedWireRoleRoomCore

namespace OAI
/-! # The terminal signed-turn directory on the original public role and row orders -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe ReportSockets ProtocolRAM TaggedShorterSupergroups
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
variable {h W k attempts H R w edges : ℕ} (S : PurchaseSampler)

namespace RoleRoom

variable (order : Fin R≃Edges S h (2^W) k)
variable (dir : Directory (reserved h W (copies k attempts)) H)

def tables (edges : ℕ) : Tables (shape (R:=R) S dir edges) where
  «meta» i := let v : Fin 7×Fin (Fintype.card (Old h W k edges)) := finProdFinEquiv.symm i
            metadataTable S order attempts edges v.1 v.2
  code := RoleROM.publicTable S h W k attempts
  site := publicSites h W k attempts S
  free := freeTable S order attempts
  exterior := exteriorTable h W k attempts S
  signed := altTable S h W k attempts
  positive := RoleROM.positiveTable S dir

def mount (edges start : ℕ) (raw : Memory w) : Memory w :=
  let z := shape (R:=R) S dir edges
  RoleROM.publish start (tables S order dir edges).pages (SiteROM.mount dir (z.offset start) raw)

theorem ready (edges start : ℕ) (raw : Memory w) :
    let z := shape (R:=R) S dir edges
    let x := tables S order dir edges
    let m := mount S order dir edges start raw
    x.Resident start m ∧ SiteROM.Resident dir (z.offset start) m := by
  dsimp only
  let z := shape (R:=R) S dir edges
  let x := tables S order dir edges
  let low := SiteROM.mount dir (z.offset start) raw
  refine ⟨x.resident start low,?_⟩
  have retained (u : ℕ) (above : z.offset start≤u) : mount S order dir edges start raw u=low u :=
    RoleROM.publish_frame x.pages start u low (Or.inr ((x.extent start).le.trans above))
  have installed := SiteROM.resident dir (z.offset start) raw
  constructor
  · intro g
    rw [retained _ (Nat.le_add_right (z.offset start) g.val)]
    exact installed.offset g
  · intro g s
    rw [retained _ ((Nat.le_add_right (z.offset start) dir.groups).trans
      (Nat.le_add_right _ (g.val*H+s.val)))]
    exact installed.target g s

theorem outside (edges start u : ℕ) (raw : Memory w)
    (out : u < start ∨ (shape (R:=R) S dir edges).stop start≤u) :
    mount S order dir edges start raw u=raw u := by
  let z := shape (R:=R) S dir edges
  let x := tables S order dir edges
  have first : start≤z.offset start := by
    unfold Sizes.offset Sizes.positive Sizes.axis Sizes.ext Sizes.free Sizes.pub
    omega
  change u < start ∨ z.offset start+SiteROM.footprint dir.groups H≤u at out
  change RoleROM.publish start x.pages (SiteROM.mount dir (z.offset start) raw) u=raw u
  have upper : u<start ∨ start+RoleROM.words x.pages≤u := by
    rcases out with h | h
    · exact Or.inl h
    · exact Or.inr ((x.extent start).le.trans ((Nat.le_add_right (z.offset start) _).trans h))
  rw [RoleROM.publish_frame x.pages start u _ upper]
  have miss : ¬(z.offset start≤u ∧ u<z.offset start+SiteROM.footprint dir.groups H) := by omega
  simp only [SiteROM.mount,ThreeFlat.RAM.fillSegment,ite_eq_right miss]

theorem meta_read (edges start : ℕ) (raw : Memory w) (field : Fin 7)
    (r : Fin (Fintype.card (Old h W k edges))) (room : Fintype.card (Old h W k edges)≤2^w) :
    («meta» start (Fintype.card (Old h W k edges)) field).eval (mount S order dir edges start raw) (r.val:Word w)=
      (metadataTable S order attempts edges field r:Word w) := by
  apply RoleROM.read _ .row _ r room rfl
  intro i
  have value := (ready S order dir edges start raw).1.meta (finProdFinEquiv (field,i))
  let N := Fintype.card (Old h W k edges)
  change mount S order dir edges start raw (start+(finProdFinEquiv (field,i)).val)=
    (metadataTable S order attempts edges (finProdFinEquiv.symm (finProdFinEquiv (field,i))).1
      (finProdFinEquiv.symm (finProdFinEquiv (field,i))).2 : Word w) at value
  rw [Equiv.symm_apply_apply] at value
  have addr : start+field.val*N+i.val=start+(finProdFinEquiv (field,i)).val := by
    change start+field.val*N+i.val=start+(i.val+N*field.val)
    ac_rfl
  change mount S order dir edges start raw (start+field.val*N+i.val)=_
  rw [addr]
  exact value

end RoleRoom
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
end

end OAI
