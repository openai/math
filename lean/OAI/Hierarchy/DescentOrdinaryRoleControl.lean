import OAI.Hierarchy.DescentScalarRoleCounts
import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentSharedCableSerial

namespace OAI
/-! # The mounted ordinary scalar population and requested-address controls -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleControl
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  base : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  walks : ℕ
  blocks : ℕ
  nodes : ℕ
  roleBits : ℕ
  countBits : ℕ
  sites : ℕ

namespace Layout
variable (L : Layout)
abbrev donors := L.walks*L.blocks
abbrev nameBits := DescentSharedCableNames.Packed.bits L.sites
abbrev chunkBits := Nat.clog 2 (chunks L.groups L.lanes+1)
abbrev count := 1+(L.donors*2+L.sites)
def width := max ((L.roleBits*L.nodes)*L.lanes)
  (max ((L.countBits*L.donors+L.countBits)*L.lanes) L.chunkBits)
def volume := L.count*2^L.width
def outBase := L.base+L.volume
def rows := L.hosts*chunks L.groups L.lanes
def outBits := Nat.clog 2 (L.rows+1)
def result : Bank := ⟨L.outBase,L.outBits⟩
def endAddress := L.outBase+2^L.outBits

def askWord (l : Fin L.sites) (chunk : ℕ) : Cell (L.nameBits*L.lanes) :=
  encode L.nameBits L.lanes (fun i=>if chunk*L.lanes+i.val<L.groups
    then DescentSharedCableNames.Packed.token (some l) else 0)

def pages : Fin L.count→ROM.Page :=
  Fin.addCases (fun _=>RoleCounts.page L.roleBits L.nodes L.countBits L.lanes)
    (Fin.addCases (fun n=>
      let js : Fin L.donors × Fin 2:=finProdFinEquiv.symm n
      ROM.binary (Gather.setField (d:=L.countBits) js.1) L.lanes js.2)
      (fun l=>⟨L.chunkBits,fun i=>(L.askWord l i.val).val⟩))

def dictIndex : Fin L.count := Fin.castAdd _ (0:Fin 1)
def pair (j : Fin L.donors) (s : Fin 2) : Fin L.count :=
  Fin.natAdd 1 (Fin.castAdd L.sites (finProdFinEquiv (j,s)))
def askIndex (l : Fin L.sites) : Fin L.count := Fin.natAdd 1 (Fin.natAdd (L.donors*2) l)
def dictionary := ROM.bank L.pages L.width L.base L.dictIndex
def tables (j : Fin L.donors) := ROM.joined L.pages L.width L.base (L.pair j)
def ask (l : Fin L.sites) := ROM.bank L.pages L.width L.base (L.askIndex l)
def want (P : Ports L.walks) (l : Fin L.sites) : Expr := .lookup (L.ask l) (.lookup P.chunks .row)
def gather (P : Ports L.walks) (old : Fin L.blocks→Bank) : Expr :=
  Gather.assembly L.tables (RoleCounts.expr P old L.dictionary L.hosts)
def counts : Expr := .lookup L.result .row

@[simp] theorem dict_page : L.pages L.dictIndex=RoleCounts.page L.roleBits L.nodes L.countBits L.lanes :=
  by simp [pages,dictIndex]
@[simp] theorem pair_page (j : Fin L.donors) (s : Fin 2) :
    L.pages (L.pair j s)=ROM.binary (Gather.setField (d:=L.countBits) j) L.lanes s :=
  by simp only [pages,pair,Fin.addCases_right,Fin.addCases_left,Equiv.symm_apply_apply]
@[simp] theorem ask_page (l : Fin L.sites) :
    L.pages (L.askIndex l)=⟨L.chunkBits,fun i=>(L.askWord l i.val).val⟩ :=
  by simp [pages,askIndex]

theorem page_bound (j : Fin L.count) : (L.pages j).bits≤L.width := by
  induction j using Fin.addCases with
  | left j =>
    simp only [pages,Fin.addCases_left]
    exact Nat.le_max_left ((L.roleBits*L.nodes)*L.lanes)
      (max ((L.countBits*L.donors+L.countBits)*L.lanes) L.chunkBits)
  | right j =>
    induction j using Fin.addCases with
    | left js =>
      obtain ⟨⟨i,s⟩,rfl⟩:=finProdFinEquiv.surjective js
      have e : (L.countBits*L.donors+L.countBits)*L.lanes≤L.width :=
        (Nat.le_max_left ..).trans (Nat.le_max_right ..)
      change (L.pages (L.pair i s)).bits≤_
      rw [L.pair_page]
      fin_cases s
      · exact (Nat.mul_le_mul_right _ (Nat.le_add_right ..)).trans e
      · exact e
    | right l =>
      change (L.pages (L.askIndex l)).bits≤_
      rw [L.ask_page]
      exact (Nat.le_max_right ..).trans (Nat.le_max_right ..)

def staticMem {w} (m : Memory w) := ROM.after L.pages L.width L.base m
def program (w) (P : Ports L.walks) (old : Fin L.blocks→Bank) :=
  (ROM.mount L.pages L.width w L.base).seq (scan w L.outBase L.rows (L.gather P old))
def output {w} (P : Ports L.walks) (old : Fin L.blocks→Bank) (m : Memory w) :=
  image L.outBase L.rows (L.gather P old) (L.staticMem m)
def ticks (P : Ports L.walks) (old : Fin L.blocks→Bank) :=
  (4+10*L.volume)+(4+L.rows*(2*(L.gather P old).work+4))

theorem bank_fits {w} (limit : L.endAddress<2^w) (j : Fin L.count) :
    (ROM.bank L.pages L.width L.base j).Fits w L.outBase :=
  ROM.bank_room _ _ _ _ _ (L.page_bound j) le_rfl ((Nat.le_add_right ..).trans_lt limit)

theorem result_size : L.rows≤L.result.size :=
  (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)

theorem result_fit {w end_} (limit : end_ <2^w) (earlier : L.endAddress≤end_) :
    L.result.Fits w end_ := by
  have contains : L.result.base+L.result.size≤end_:=earlier
  exact ⟨Nat.two_pow_pos _,
    (Nat.le_add_left ..).trans_lt (contains.trans_lt limit),contains⟩

theorem field_room {w} (P : Ports L.walks) (old : Fin L.blocks→Bank)
    (access : ∀b,Accessible P (old b) L.hosts L.groups L.lanes w L.outBase)
    (limit : L.endAddress<2^w) :
    Gather.Bounds (w:=w) (d:=L.countBits) (M:=L.lanes) L.tables
      (RoleCounts.expr P old L.dictionary L.hosts) L.outBase := by
  intro j
  let z:=finProdFinEquiv.symm j
  have remote:=peer_fits P (old z.2) L.outBase (access _) z.1
  refine ⟨⟨L.bank_fits limit L.dictIndex,remote⟩,L.bank_fits limit _,L.bank_fits limit _,?_,?_⟩
  · exact congrArg ROM.Page.bits (L.pair_page j 0)
  · exact congrArg ROM.Page.bits (L.pair_page j 1)

theorem any {w} (P : Ports L.walks) (old : Fin L.blocks→Bank) (m : Memory w)
    (access : ∀b,Accessible P (old b) L.hosts L.groups L.lanes w L.outBase)
    (limit : L.endAddress<2^w) :
    (L.program w P old).Exec m (L.output P old m) (L.ticks P old) ∧
    CheapCode (L.program w P old) ∧
    DescentStaticWordColumn.names (L.program w P old)=15*(L.volume+1)+11+4*(L.gather P old).work ∧
    ∀a,a<L.base ∨ L.endAddress≤a → L.output P old m a=m a := by
  have initial:=ROM.run L.pages L.width L.base m ((Nat.le_add_right ..).trans_lt limit)
  have safe:=Gather.fits L.tables _ _ (L.field_room P old access limit) (List.finRange L.donors)
  have cover:=Nat.add_le_add_left L.result_size L.outBase
  have pass : (scan w L.outBase L.rows (L.gather P old)).Exec
      (L.staticMem m) (L.output P old m) (4+L.rows*(2*(L.gather P old).work+4)) := by
    intro labels regs slots machine
    exact scan_exec L.outBase L.rows (L.gather P old) (L.staticMem m) safe
      (cover.trans_lt limit) machine
  refine ⟨?_,?_,?_,?_⟩
  · intro labels regs slots machine
    exact Procedure.Exec.then initial.1 (@pass) machine
  · intro labels regs slots pc reg pub exit i
    exact cheap_seq (A:=ROM.mount L.pages L.width w L.base)
      (B:=scan w L.outBase L.rows (L.gather P old))
      (ROM.cheap L.pages L.width w L.base) (scan_cheap w L.outBase L.rows (L.gather P old))
      pc reg pub exit i
  · rw [program,DescentStaticWordColumn.names_seq,initial.2,DescentStaticWordColumn.names_scan]
    dsimp only [volume]
    omega
  · intro a away
    have between : L.base≤L.outBase:=Nat.le_add_right ..
    have bottom : L.outBase+L.rows≤L.endAddress:=cover
    have top : L.outBase≤L.endAddress:=Nat.le_add_right ..
    exact (ProtocolRAMGeneratedWrite.frame_image L.outBase L.rows _ _ a
      (away.imp (fun h=>h.trans_le between) (fun h=>bottom.trans h))).trans
      (ROM.frame _ _ _ m a (away.imp_right (fun h=>top.trans h)))

end Layout
end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleControl

end OAI
