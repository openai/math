import OAI.Hierarchy.TaggedWireRolePages

namespace OAI
/-! # Layout and range checks for the native signed-turn tables -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
variable {w : ℕ}

/-- Positions of all consecutive ROM intervals. Both public code and
site tables accept the same ordinal, and both orientations of a free row
accept the same original core index. -/
structure Sizes where
  old : ℕ
  publicRows : ℕ
  freeRows : ℕ
  wires : ℕ
  signedSites : ℕ
  groups : ℕ
  slots : ℕ

namespace Sizes
variable (z : Sizes) (start : ℕ)
def pub := start+7*z.old
def free := z.pub start+2*z.publicRows
def ext := z.free start+2*z.freeRows
def axis := z.ext start+2*z.wires
def positive := z.axis start+z.signedSites
def offset := z.positive start+z.groups*z.slots
def stop := z.offset start+(z.groups+z.groups*z.slots)

/-- All machine banks may read up to their rounded binary capacity. The
same linear-sized upper address covers their full indexed domains. -/
def ceiling := 3*(z.stop start+1)

theorem rounded_fits {base size : ℕ} (before : base+size≤z.stop start) :
    base+(RoleROM.bank base size).size≤z.ceiling start := by
  have binary := ProtocolRAMPurchaseSampler.span_le size
  change base+ProtocolRAMPurchaseSampler.span size≤3*(z.stop start+1)
  omega
end Sizes

structure Tables (z : Sizes) where
  «meta» : Fin (7*z.old)→ℕ
  code : Fin z.publicRows→ℕ
  site : Fin z.publicRows→ℕ
  free : Bool→Fin z.freeRows→ℕ
  exterior : Bool→Fin z.wires→ℕ
  signed : Fin z.signedSites→ℕ
  positive : Fin (z.groups*z.slots)→ℕ

namespace Tables
variable {z : Sizes} (x : Tables z)
private def page {m : ℕ} (fn : Fin m→ℕ) : RoleROM.Page := ⟨m,fn⟩
def pages : List RoleROM.Page :=
  [page x.meta,page x.code,page x.site,page (x.free false),page (x.free true),
    page (x.exterior false),page (x.exterior true),page x.signed,page x.positive]

theorem extent (start : ℕ) : start+RoleROM.words x.pages=z.offset start := by
  dsimp [pages,page,RoleROM.words,Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub]
  omega

structure Resident (start : ℕ) (m : Memory w) : Prop where
  «meta» : RoleROM.Mounted start x.meta m
  code : RoleROM.Mounted (z.pub start) x.code m
  site : RoleROM.Mounted (z.pub start+z.publicRows) x.site m
  free : ∀s : Bool,RoleROM.Mounted (z.free start+s.toNat*z.freeRows) (x.free s) m
  exterior : ∀s : Bool,RoleROM.Mounted (z.ext start+s.toNat*z.wires) (x.exterior s) m
  signed : RoleROM.Mounted (z.axis start) x.signed m
  positive : RoleROM.Mounted (z.positive start) x.positive m

theorem resident (start : ℕ) (m : Memory w) :
    x.Resident start (RoleROM.publish start x.pages m) := by
  let p := page x.meta
  let c := page x.code
  let s := page x.site
  let f := page (x.free false)
  let g := page (x.free true)
  let l := page (x.exterior false)
  let r := page (x.exterior true)
  let a := page x.signed
  let b := page x.positive
  have here {n base : ℕ} {fn : Fin n→ℕ} (left right : List RoleROM.Page)
      (layout : x.pages=left++page fn::right) (location : base=start+RoleROM.words left) :
      RoleROM.Mounted base fn (RoleROM.publish start x.pages m) := by
    rw [layout,location]
    exact RoleROM.mounted_at left (page fn) right start m
  constructor
  · exact here [] [c,s,f,g,l,r,a,b] rfl rfl
  · apply here [p] [s,f,g,l,r,a,b] rfl
    change start+7*z.old=start+(7*z.old+0)
    omega
  · apply here [p,c] [f,g,l,r,a,b] rfl
    change start+7*z.old+z.publicRows=start+(7*z.old+(z.publicRows+0))
    omega
  · intro side
    cases side
    · apply here [p,c,s] [g,l,r,a,b] rfl
      dsimp [p,c,s,page,Sizes.free,Sizes.pub,RoleROM.words]
      omega
    · apply here [p,c,s,f] [l,r,a,b] rfl
      dsimp [p,c,s,f,page,Sizes.free,Sizes.pub,RoleROM.words]
      omega
  · intro side
    cases side
    · apply here [p,c,s,f,g] [r,a,b] rfl
      dsimp [p,c,s,f,g,page,Sizes.ext,Sizes.free,Sizes.pub,RoleROM.words]
      omega
    · apply here [p,c,s,f,g,l] [a,b] rfl
      dsimp [p,c,s,f,g,l,page,Sizes.ext,Sizes.free,Sizes.pub,RoleROM.words]
      omega
  · apply here [p,c,s,f,g,l,r] [b] rfl
    dsimp [p,c,s,f,g,l,r,page,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub,RoleROM.words]
    omega
  · apply here [p,c,s,f,g,l,r,a] [] rfl
    dsimp [p,c,s,f,g,l,r,a,page,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub,RoleROM.words]
    omega

theorem Resident.frame {start : ℕ} {m out : Memory w} (original : x.Resident start m)
    (keep : ∀u,start≤u → u<z.offset start → out u=m u) : x.Resident start out := by
  have transport {n base : ℕ} {f : Fin n→ℕ} (present : RoleROM.Mounted base f m)
      (lo : start≤base) (hi : base+n≤z.offset start) : RoleROM.Mounted base f out := by
    intro i
    have bounded := i.isLt
    exact (keep _ (by omega) (by omega)).trans (present i)
  constructor
  · apply transport original.meta le_rfl
    simp only [Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub]
    omega
  · apply transport original.code <;> try simp only [Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub]; omega
  · apply transport original.site <;> try simp only [Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub]; omega
  · intro side
    cases side <;> apply transport (original.free _) <;>
      simp [Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub] <;> omega
  · intro side
    cases side <;> apply transport (original.exterior _) <;>
      simp [Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub] <;> omega
  · apply transport original.signed <;> try simp only [Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub]; omega
  · apply transport original.positive <;> try simp only [Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub]; omega
end Tables

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
end

end OAI
