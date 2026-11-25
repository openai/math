import OAI.Hierarchy.DescentResetFieldAssembler

namespace OAI
/-! # Native two-table evaluation of the ordinary signed metadata word -/
namespace Hierarchy.DescentOrdinarySignedMeta
open DescentResetFieldAssembler DescentSIMDLookup DescentPackedZip
open DescentPacking.PackedMatch.Local
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open private DescentPacking.PackedMatch.Local.Gather.encode_zero
  from OAI.Hierarchy.DescentPackedFieldGather
open scoped Classical Fin.CommRing
noncomputable section
/-- The native neighbor alphabet has a further local code. On a loop both endpoints
use its actual neighbor ordinal, so the two faces read that same signed cable. -/
def localWord (degree peer units : ℕ) (src dst core : Bool) : Meta :=
  let here := if src && dst then peer else degree
  ⟨true,if src then here else peer,if dst then here else peer,here,false,core,units⟩

theorem localWord_face {degree peer : ℕ} (room : peer<degree) (units : ℕ) (src dst core side : Bool) :
    face side (localWord degree peer units src dst core) = (if side then dst else src) := by
  cases src <;> cases dst <;> cases side <;> simp [localWord,face,Nat.ne_of_lt room]

theorem localWord_peer {degree p : ℕ} (room : p<degree) (units : ℕ) (src dst core : Bool)
    (incident : src=true ∨ dst=true) : peer (localWord degree p units src dst core)=p := by
  cases src <;> cases dst <;> simp_all [localWord,peer,opposite,Nat.ne_of_lt room]


/-- The fields are live, local source, local target, and membership in the core. -/
def flags (active src dst marked : Bool) : Cell (1*4) :=
  encode 1 4 ![(active.toNat:Cell 1),(src.toNat:Cell 1),(dst.toNat:Cell 1),(marked.toNat:Cell 1)]

def pair (b : ℕ) (p u : Cell b) : Cell (b*2) := encode b 2 ![p,u]

def format (degree b : ℕ) (flag : Cell (1*4)) (pu : Cell (b*2)) : Cell (b*7) :=
  let bit:=fun (j:Fin 4)=>decide (((encode 1 4).symm flag j).val=1)
  let word:=(encode b 2).symm pu
  if bit 0 then raw b (localWord degree (word 0).val (word 1).val (bit 1) (bit 2) (bit 3)) else 0

theorem pair_empty (b : ℕ) : pair b 0 0=0 := by
  rw [←DescentPacking.PackedMatch.Local.Gather.encode_zero b 2]
  apply congrArg (encode b 2)
  funext i; fin_cases i <;> rfl

theorem flag_empty : flags false false false false = 0 := by
  rw [←DescentPacking.PackedMatch.Local.Gather.encode_zero 1 4]
  apply congrArg (encode 1 4)
  funext i; fin_cases i <;> rfl

theorem raw_empty (b : ℕ) : raw b Meta.blank=0 := by
  rw [←DescentPacking.PackedMatch.Local.Gather.encode_zero b 7]
  apply congrArg (encode b 7)
  funext i; fin_cases i <;> rfl

theorem format_inputs (degree b : ℕ) (p u : Cell b) (active src dst marked : Bool) :
    format degree b (flags active src dst marked) (pair b p u)=
      raw b (if active then localWord degree p.val u.val src dst marked else .blank) := by
  cases active <;> cases src <;> cases dst <;> cases marked <;>
    simp [format,flags,pair,raw_empty]

theorem format_empty (degree b : ℕ) : format degree b 0 0=0 := by
  rw [←flag_empty,←pair_empty b,format_inputs]
  simp [raw_empty]

variable {H G M w out b degree : ℕ}

/-- The signed output is the actual nested expression on resident flag, peer,
and measured multiplicity columns. These are the same source predicates that the
fallback and normalized-neighbor programs issue. -/
def expression (pairBank metaBank : Tables) (flags peers units : Expr) : Expr :=
  metaBank.read flags (pairBank.read peers units)

theorem source (pairBank metaBank : Tables) (fs ps us : Expr)
    (pfit : Fits pairBank ps us b b M out w)
    (mfit : Fits metaBank fs (pairBank.read ps us) (1*4) (b*2) M out w)
    (mem : Memory w) (pstatic : Static pairBank (pair b) M mem)
    (mstatic : Static metaBank (format degree b) M mem)
    (active src dst marked : Fin H→Fin G→Bool) (p u : Fin H→Fin G→Cell b)
    (readF : Source fs (fun h j=>flags (active h j) (src h j) (dst h j) (marked h j)) M mem)
    (readP : Source ps p M mem) (readU : Source us u M mem) :
    Source (expression pairBank metaBank fs ps us) (fun h j=>raw b
      (if active h j then localWord degree (p h j).val (u h j).val
        (src h j) (dst h j) (marked h j) else .blank)) M mem := by
  have pu:=read_data pairBank ps us out pfit (pair b) (pair_empty b) mem pstatic p u readP readU
  simpa only [expression,format_inputs] using
    read_data metaBank fs (pairBank.read ps us) out mfit (format degree b) (format_empty degree b)
      mem mstatic _ _ readF pu

theorem expression_work (pairBank metaBank : Tables) (f p u : Expr) :
    (expression pairBank metaBank f p u).work=f.work+p.work+u.work+22 := by
  simp only [expression,DescentPackedZip.work];omega


open DescentOrdinaryAtomFieldRAM.ROM

def pages (degree b M : ℕ) : Fin (2+2)→Page :=
  Fin.addCases (binary (pair b) M) (binary (format degree b) M)

def pageBits (b M : ℕ) := ((1*4)+b*2)*M

def stop (base b M : ℕ) := base+(2+2)*2^pageBits b M

def pairTable (base degree b M : ℕ) :=
  joined (pages degree b M) (pageBits b M) base (Fin.castAdd 2)

def metaTable (base degree b M : ℕ) :=
  joined (pages degree b M) (pageBits b M) base (Fin.natAdd 2)

def mountedExpr (base degree b M : ℕ) (f p u : Expr) :=
  expression (pairTable base degree b M) (metaTable base degree b M) f p u

theorem pageFits (degree b M : ℕ) (i : Fin (2+2)) : (pages degree b M i).bits≤pageBits b M := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [pages,Fin.addCases_left]
    fin_cases j <;> change _*M≤_*M <;> apply Nat.mul_le_mul_right <;> dsimp [pageBits] <;> omega
  · intro j
    simp only [pages,Fin.addCases_right]
    fin_cases j <;> change _*M≤_*M <;> apply Nat.mul_le_mul_right <;> dsimp [pageBits] <;> omega

theorem mount_run (base degree b M w : ℕ) (m : Memory w) (room : stop base b M<2^w) :
    let pg:=pages degree b M
    let code:=mount pg (pageBits b M) w base
    let dst:=after pg (pageBits b M) base m
    code.Exec m dst (4+10*((2+2)*2^pageBits b M)) ∧ CheapCode code ∧
      DescentStaticWordColumn.names code=15*((2+2)*2^pageBits b M+1) ∧
      ∀z,z<base ∨ stop base b M≤z→dst z=m z := by
  intro pg code dst
  have hr:=DescentOrdinaryAtomFieldRAM.ROM.run pg (pageBits b M) base m room
  exact ⟨hr.1,cheap pg _ _ _,hr.2,DescentOrdinaryAtomFieldRAM.ROM.frame pg _ _ _⟩

theorem mounted {base : ℕ} (fs ps us : Expr) (mem : Memory w)
    (fitF : fs.Fits w base) (fitP : ps.Fits w base) (fitU : us.Fits w base)
    (room : stop base b M<2^w)
    (active src dst marked : Fin H→Fin G→Bool) (p u : Fin H→Fin G→Cell b)
    (readF : Source fs (fun h j=>flags (active h j) (src h j) (dst h j) (marked h j)) M mem)
    (readP : Source ps p M mem) (readU : Source us u M mem) :
    (mountedExpr base degree b M fs ps us).Fits w (stop base b M) ∧
    Source (mountedExpr base degree b M fs ps us) (fun h j=>raw b
      (if active h j then localWord degree (p h j).val (u h j).val
        (src h j) (dst h j) (marked h j) else .blank)) M
        (after (pages degree b M) (pageBits b M) base mem) := by
  let pg:=pages degree b M
  let sz:=pageBits b M
  let final:=after pg sz base mem
  have lower : base ≤ stop base b M :=Nat.le_add_right ..
  have held {d : ℕ} (e : Expr) (v : Fin H→Fin G→Cell d) (fit : e.Fits w base)
      (got : Source e v M mem) : Source e v M final :=
    fun i=>(ProtocolRAM.eval_below e _ mem final fit (fun a ha=>
      DescentOrdinaryAtomFieldRAM.ROM.frame pg sz base mem a (.inl ha))).trans (got i)
  have bankFits (j : Fin (2+2)) : (bank pg sz base j).Fits w (stop base b M):=
    bank_room pg sz base _ j (pageFits degree b M j) le_rfl room
  have pairFits : Fits (pairTable base degree b M) ps us b b M (stop base b M) w:=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ lower fitP,ProtocolRAMGeneratedWrite.fits_mono _ lower fitU,
     bankFits _,bankFits _,by rfl,
     by rfl⟩
  have joinedFits : ((pairTable base degree b M).read ps us).Fits w (stop base b M):=by
    simp [Tables.read,Expr.Fits,pairFits.left,pairFits.right,pairFits.shift,pairFits.apply]
  have nextFits : Fits (metaTable base degree b M) fs ((pairTable base degree b M).read ps us)
      (1*4) (b*2) M (stop base b M) w:=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ lower fitF,joinedFits,bankFits _,bankFits _,
     by rfl,by rfl⟩
  constructor
  · simp [mountedExpr,expression,Tables.read,Expr.Fits,nextFits.left,nextFits.shift,nextFits.apply,
      pairFits.left,pairFits.right,pairFits.shift,pairFits.apply]
  · exact source _ _ fs ps us pairFits nextFits final
      (binary_mounted (pair b) M pg sz base mem (pageFits degree b M) (Fin.castAdd 2)
        (fun j=>by fin_cases j <;> rfl))
      (binary_mounted (format degree b) M pg sz base mem (pageFits degree b M) (Fin.natAdd 2)
        (fun j=>by fin_cases j <;> rfl))
      active src dst marked p u (held fs _ fitF readF) (held ps p fitP readP) (held us u fitU readU)

end
end Hierarchy.DescentOrdinarySignedMeta

end OAI
