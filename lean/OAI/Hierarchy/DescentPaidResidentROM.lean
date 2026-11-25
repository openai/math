import OAI.Hierarchy.DescentPaidResidentCount
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Authentic printed lookup pages and execution for funded successor counts -/
namespace Hierarchy.DescentPaidResidentCount.Issue
open DescentSIMDLookup DescentPackedZip DescentPackedActorMask DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {D cap b n H G M w base : ℕ}
local notation "size" => actors D cap

def unit (D cap b n : ℕ) := max (n+n*actors D cap) (1*actors D cap+b*D)
def side (mask sum : Fin 2→Page) : Fin 2→Fin 2→Page := ![mask,sum]
def page (D cap b n M : ℕ) (j : Fin (2*2)) : Page :=
  let t : Fin 2 × Fin 2:=finProdFinEquiv.symm j
  side (binary (target n (actors D cap)) M) (binary (counted D cap b) M) t.1 t.2
def pair (i : Fin 2) (half : Fin 2) : Fin (2*2) := finProdFinEquiv (i,half)
local notation "book" => page D cap b n M
local notation "width" => unit D cap b n*M
local notation "table" i => joined book width base (pair i)

theorem mask_page (j : Fin 2) : book (pair 0 j)=binary (target n size) M j := by
  simp [page,pair,side]
theorem sum_page (j : Fin 2) : book (pair 1 j)=binary (counted D cap b) M j := by
  simp [page,pair,side]

theorem bits (i : Fin (2*2)) : (book i).bits≤width := by
  obtain ⟨⟨s,j⟩,rfl⟩:=finProdFinEquiv.surjective i
  change (book (pair s j)).bits≤width
  fin_cases s
  · change (book (pair 0 j)).bits≤width
    rw [mask_page (D:=D) (cap:=cap) (b:=b) (n:=n) (M:=M) j]
    have bound := le_max_left (n+n*size) (1*size+b*D)
    fin_cases j
    · change n*M≤width
      exact Nat.mul_le_mul_right _ ((Nat.le_add_right ..).trans bound)
    · change (n+n*size)*M≤width
      exact Nat.mul_le_mul_right _ bound
  · change (book (pair 1 j)).bits≤width
    rw [sum_page (D:=D) (cap:=cap) (b:=b) (n:=n) (M:=M) j]
    have bound := le_max_right (n+n*size) (1*size+b*D)
    fin_cases j
    · change (1*size)*M≤width
      exact Nat.mul_le_mul_right _ ((Nat.le_add_right ..).trans bound)
    · change (1*size+b*D)*M≤width
      exact Nat.mul_le_mul_right _ bound

def numWords (D cap b n M : ℕ) := 4*2^(unit D cap b n*M)

theorem bound {a₁ a₂ a₃ : ℕ} (f : Cell a₁→Cell a₂→Cell a₃) (i : Fin 2)
    (pages : ∀j,book (pair i j)=binary f M j) {out : ℕ} (apart : base+numWords D cap b n M≤out)
    (space : out<2^w) (u v : Expr) (hu : u.Fits w out) (hv : v.Fits w out) :
    DescentPackedZip.Fits (table i) u v a₁ a₂ M out w :=
  ⟨hu,hv,bank_room book width base out _ (bits _) apart space,
    bank_room book width base out _ (bits _) apart space,congrArg Page.bits (pages 0),congrArg Page.bits (pages 1)⟩

/-- The four fixed pages are initialized once per batch. Each packed row then
uses the charged counters and true old/matched actor destinations issued before
the ROM bank. Both the native running time and machine size are explicit. -/
theorem fresh (query dest count : Expr) (out : Bank) (old : Memory w)
    (qEarly : query.Fits w base) (dEarly : dest.Fits w base) (cEarly : count.Fits w base)
    (wanted : Fin H→Fin G→Cell n) (address : Fin H→Fin G→Fin size→Cell n)
    (funded : Fin H→Fin G→Fin D→Cell b) (qRead : Source query wanted M old)
    (dRead : Source dest (fun h g=>encode n _ (address h g)) M old)
    (cRead : Source count (fun h g=>encode b _ (funded h g)) M old)
    (apart : base+numWords D cap b n M≤out.base) (space : out.base+H*chunks G M<2^w) :
    let mounted:=after book width base old
    let op:=instruction (table 0) (table 1) query dest count
    let scanner:=scan w out.base (H*chunks G M) op
    let setup:=mount book width w base
    let done:=image out.base (H*chunks G M) op mounted
    (setup.seq scanner).Exec old done ((4+10*numWords D cap b n M)+(4+H*chunks G M*(2*op.work+4))) ∧
    DescentPackedColony.Reads out (fun h g=>counted D cap b (target n size (wanted h g) (encode n _ (address h g)))
      (encode b _ (funded h g))) M done ∧
    (∀i,i<base ∨ out.base+H*chunks G M≤ i→done i=old i) ∧
    DescentStaticWordColumn.names (setup.seq scanner)=
      15*(numWords D cap b n M+1)+(11+4*(query.work+dest.work+count.work+22)) ∧ CheapCode (setup.seq scanner) := by
  intro mounted op scanner setup done
  have below : out.base<2^w:=(Nat.le_add_right ..).trans_lt space
  have order : base≤out.base:=(Nat.le_add_right ..).trans apart
  have installed := DescentOrdinaryAtomFieldRAM.ROM.run book width base old (apart.trans_lt below)
  have maskFixed:=binary_mounted (target n size) M book width base old bits (pair 0) mask_page
  have sumFixed:=binary_mounted (counted D cap b) M book width base old bits (pair 1) sum_page
  have frame := DescentOrdinaryAtomFieldRAM.ROM.frame book width base old
  have hold {a : ℕ} (e : Expr) (x : Fin H→Fin G→Cell a) (fit : e.Fits w base)
      (before : Source e x M old) : Source e x M mounted := by
    intro r
    exact (ProtocolRAM.eval_below e _ old mounted fit (fun i hi=>frame i (.inl hi))).trans (before r)
  have maskRoom:=bound (target n size) 0 mask_page apart below query dest
    (ProtocolRAMGeneratedWrite.fits_mono _ order qEarly) (ProtocolRAMGeneratedWrite.fits_mono _ order dEarly)
  have maskExpr : ((table 0).read query dest).Fits w out.base:=⟨maskRoom.apply,maskRoom.right,maskRoom.shift,maskRoom.left⟩
  have sumRoom:=bound (counted D cap b) 1 sum_page apart below _ count maskExpr (ProtocolRAMGeneratedWrite.fits_mono _ order cEarly)
  obtain ⟨scanned,output,light⟩:=DescentPaidResidentCount.run (table 0) (table 1) query dest count out mounted
    maskRoom sumRoom maskFixed sumFixed wanted address funded (hold _ _ qEarly qRead) (hold _ _ dEarly dRead)
      (hold _ _ cEarly cRead) space
  refine ⟨?_,output,?_,?_,cheap_seq (cheap book width w base) light⟩
  · exact Procedure.Exec.then installed.1 scanned
  · intro i outside
    have fixed:=ProtocolRAMGeneratedWrite.frame_image out.base (H*chunks G M) op mounted i
      (by rcases outside with lt|hi <;> omega)
    exact fixed.trans (frame i (by rcases outside with lt|hi <;> change _ ∨ base+numWords D cap b n M≤ i <;> omega))
  · rw [DescentStaticWordColumn.names_seq,installed.2,DescentStaticWordColumn.names_scan]
    change _+(_+_*((table 1).read ((table 0).read query dest) count).work)=_
    rw [DescentPackedZip.work,DescentPackedZip.work]
    unfold numWords;omega

theorem half_word (fit : width≤w/2) : numWords D cap b n M≤4*2^(w/2) :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) fit)

end
end Hierarchy.DescentPaidResidentCount.Issue

end OAI
