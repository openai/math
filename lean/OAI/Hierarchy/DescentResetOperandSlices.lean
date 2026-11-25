import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentOperandStateCodec

namespace OAI
/-! # Issuing the new cable serial and its in-child operand chunk from the reached reset -/
namespace Hierarchy.DescentResetOperandSlices
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM.ROM DescentPackedZip DescentOperandStateBanks
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {b w : ℕ}

/-- A stem has one grain, a trunk splits away from the hub, and a contact or
private circuit edge always splits. The last two input bits below come from
the old node's operand tag and the reached terminal hub indication. -/
inductive Role where | stem | trunk | routed
  deriving DecidableEq
def marked : Role→Bool→Bool
  | .stem,_ => false
  | .trunk,hub => !hub
  | .routed,_ => true

def mode {b : ℕ} (role : Role) (tag : Cell b) (hub : Cell 1) : Cell 2 :=
  if tag.val=1 then if marked role (decide (hub.val=1)) then 2 else 1 else 0

def part (unit : ℕ) (serial : Bool) {b : ℕ} (m : Cell 2) (x : Cell b) : Cell b :=
  if m.val=0 then 0 else if m.val=2 then
    if serial then (x.val/unit : ℕ) else (x.val%unit : ℕ)
  else if serial then 0 else x

theorem none_part (unit : ℕ) (f : Bool) (x : Cell b) : part unit f 0 x=0 := by simp [part]
theorem one_part (u : ℕ) (x : Cell b) : part u true 1 x=0 ∧ part u false 1 x=x :=by simp [part]
theorem two_part (u : ℕ) (x : Cell b) : part u true 2 x=(x.val/u:ℕ) ∧ part u false 2 x=(x.val%u:ℕ) :=by simp [part]
theorem case_mode (r : Role) (tag : Cell b) (h : Cell 1) (prior : tag.val=1) :
    mode r tag h=if marked r (decide (h.val=1)) then (2:Cell 2) else 1 :=by simp [mode,prior]

/-- A single-grain old stem needs no marked bit. -/
theorem stem_aligned (unit : ℕ) (tag : Cell b) (hub : Cell 1) (x : Cell b) (real : tag.val=1) :
    (part unit true (mode .stem tag hub) x).val=0 ∧ (part unit false (mode .stem tag hub) x).val=x.val := by
  simp [mode,real,marked,part]


def dial (r : Role) : Fin 3 := match r with | .stem=>0 | .trunk=>1 | .routed=>2
def roles (j : Fin 3) : Role := if j=0 then .stem else if j=1 then .trunk else .routed
theorem roles_dial (r : Role) : roles (dial r)=r :=by cases r <;> decide

def pages (u b M : ℕ) (i : Fin 10) : Page :=
  let pair:=(finProdFinEquiv.symm i : Fin 5×Fin 2)
  if live:pair.1.val<3 then binary (mode (b:=b) (roles ⟨_,live⟩)) M pair.2
  else binary (part u (decide (pair.1.val=4)) (b:=b)) M pair.2

def width (b M : ℕ) :=(b+2)*M
def ix (j : Fin 5) (z : Fin 2) : Fin 10 :=finProdFinEquiv (j,z)
def firstIndex (r : Role) : Fin 5:=⟨(dial r).val,(dial r).isLt.trans (by decide)⟩
def lastIndex (f : Bool) : Fin 5:= if f then 4 else 3
def tables (u b M base : ℕ) (j : Fin 5) := joined (pages u b M) (width b M) base (ix j)
def expr (u b M base : ℕ) (r : Role) (serial : Bool) (tag hub chunk : Expr) :=
  (tables u b M base (lastIndex serial)).read ((tables u b M base (firstIndex r)).read tag hub) chunk

theorem first_page (u b M : ℕ) (r : Role) (z : Fin 2) :
    pages u b M (ix (firstIndex r) z)=binary (mode (b:=b) r) M z :=by
  simp [pages,ix,firstIndex,(dial r).isLt,roles_dial]

theorem last_page (u b M : ℕ) (f : Bool) (z : Fin 2) :
    pages u b M (ix (lastIndex f) z)=binary (part u f (b:=b)) M z :=by
  cases f <;> simp [pages,ix,lastIndex]

theorem bounds (u b M : ℕ) (i : Fin 10) : (pages u b M i).bits≤width b M := by
  obtain ⟨⟨j,z⟩,rfl⟩:=(finProdFinEquiv (m:=5) (n:=2)).surjective i
  fin_cases j <;> fin_cases z <;> simp [pages,binary,width,Nat.add_mul] <;> omega

def endAddress (base b M : ℕ) := base+10*2^(width b M)
def program (u b M base w : ℕ) := mount (pages u b M) (width b M) w base
def image (u b M base : ℕ) (m : Memory w) :=after (pages u b M) (width b M) base m

theorem mount_any (u b M base : ℕ) (m : Memory w) (room : endAddress base b M<2^w) :
    (program u b M base w).Exec m (image u b M base m) (4+10*(10*2^(width b M))) ∧
    (∀y,y<base ∨ endAddress base b M≤y → image u b M base m y=m y) ∧
    DescentStaticWordColumn.names (program u b M base w)=15*(10*2^(width b M)+1) ∧
    CheapCode (program u b M base w) :=
  ⟨(DescentOrdinaryAtomFieldRAM.ROM.run _ _ _ m room).1,frame _ _ _ m,
    (DescentOrdinaryAtomFieldRAM.ROM.run _ _ _ m room).2,DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _⟩

theorem issue {H G w : ℕ} (u b M base : ℕ) (r : Role) (f : Bool) (tag hub chunk : Expr) (m : Memory w)
    (tx cx : Fin H→Fin G→Cell b) (hx : Fin H→Fin G→Cell 1)
    (te : tag.Fits w base) (he : hub.Fits w base) (ce : chunk.Fits w base)
    (ts : Source tag tx M m) (hs : Source hub hx M m) (cs : Source chunk cx M m)
    (space : endAddress base b M<2^w) :
    (expr u b M base r f tag hub chunk).Fits w (endAddress base b M) ∧
    Source (expr u b M base r f tag hub chunk) (fun h g=>part u f (mode r (tx h g) (hx h g)) (cx h g))
      M (image u b M base m) := by
  let out:=endAddress base b M
  let done:=image u b M base m
  have low : base≤out:=Nat.le_add_right ..
  have stable:=frame (pages u b M) (width b M) base m
  have keep {t : ℕ} (p : Expr) (v : Fin H→Fin G→Cell t) (valid : p.Fits w base) (src : Source p v M m) :
      Source p v M done:=fun e=>(ProtocolRAM.eval_below p _ m done valid (fun j lo=>stable j (.inl lo))).trans (src e)
  let mOp:=(tables u b M base (firstIndex r)).read tag hub
  have mSafe : DescentPackedZip.Fits (tables u b M base (firstIndex r)) tag hub b 1 M out w:=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ low te,ProtocolRAMGeneratedWrite.fits_mono _ low he,
      bank_room _ _ _ _ _ (bounds ..) le_rfl space,bank_room _ _ _ _ _ (bounds ..) le_rfl space,
      congrArg Page.bits (first_page u b M r 0),congrArg Page.bits (first_page u b M r 1)⟩
  have mFit : mOp.Fits w out:=⟨mSafe.apply,mSafe.right,mSafe.shift,mSafe.left⟩
  have mStatic:=binary_mounted (mode (b:=b) r) M (pages u b M) (width b M) base m
    (bounds u b M) (ix (firstIndex r)) (first_page u b M r)
  have mSrc:=read_data _ _ _ out mSafe (mode r) (by simp [mode]) done mStatic tx hx (keep _ _ te ts) (keep _ _ he hs)
  have vSafe : DescentPackedZip.Fits (tables u b M base (lastIndex f)) mOp chunk 2 b M out w:=
    ⟨mFit,ProtocolRAMGeneratedWrite.fits_mono _ low ce,
      bank_room _ _ _ _ _ (bounds ..) le_rfl space,bank_room _ _ _ _ _ (bounds ..) le_rfl space,
      congrArg Page.bits (last_page u b M f 0),congrArg Page.bits (last_page u b M f 1)⟩
  have vStatic:=binary_mounted (part u f (b:=b)) M (pages u b M) (width b M) base m
    (bounds u b M) (ix (lastIndex f)) (last_page u b M f)
  exact ⟨⟨vSafe.apply,vSafe.right,vSafe.shift,vSafe.left⟩,read_data _ _ _ out vSafe (part u f)
    (none_part ..) done vStatic _ cx mSrc (keep _ _ ce cs)⟩

end
end Hierarchy.DescentResetOperandSlices

end OAI
