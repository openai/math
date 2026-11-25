import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentRawCablePanel
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! Physically concatenate two packed earlier registers, retaining all written words on either side. -/
namespace Hierarchy.DescentRawCablePanel.RegisterJoin
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
open DescentOrdinaryAtomFieldRAM
variable {a b H G M w : ℕ}
def joined (x : Cell a) (y : Cell b) : Cell (a+b):=pair a b (x,y)
theorem blank (a b : ℕ) : joined (0:Cell a) (0:Cell b)=0:=by
  apply Fin.ext;change (0:Cell b).val+2^b*(0:Cell a).val=0;simp
def pages (a b M : ℕ):=ROM.binary (joined (a:=a) (b:=b)) M
def size (a b M : ℕ) :=(a+b)*M
def dataBase (a b M base : ℕ):=base+2*2^size a b M
def bank (a b H G M base : ℕ) : Bank:=⟨dataBase a b M base,Nat.clog 2 (H*chunks G M+1)⟩
def table (a b M base : ℕ) :=ROM.joined (pages a b M) (size a b M) base id
def expr (a b M base : ℕ) (left right : Expr):=(table a b M base).read left right
def phase (a b H G M w base : ℕ) (left right : Expr) : NativePhase w :=
  let e:=expr a b M base left right
  let out:=dataBase a b M base
  ⟨(ROM.mount (pages a b M) (size a b M) w base).seq (scan w out (H*chunks G M) e),
    (4+10*(2*2^size a b M))+(4+H*chunks G M*(2*e.work+4)),
    fun m=>image out (H*chunks G M) e (ROM.after (pages a b M) (size a b M) base m),
    cheap_seq (ROM.cheap _ _ _ _) (@scan_cheap _ _ _ _)⟩

private theorem widths (j : Fin 2) : ((pages a b M) j).bits≤ size a b M:=by
  fin_cases j
  · change a*M≤(a+b)*M;exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)
  · exact le_rfl

variable (a b base : ℕ) (left right : Expr) (m : Memory w) (lfit : left.Fits w base) (rfit : right.Fits w base)
variable (limit : dataBase a b M base+H*chunks G M<2^w)
local notation "out" => dataBase a b M base
local notation "t" => table a b M base
local notation "f" => joined (a:=a) (b:=b)
local notation "mid" => ROM.after (pages a b M) (size a b M) base m
local notation "e" => expr a b M base left right

include lfit rfit limit in
private theorem fit : DescentPackedZip.Fits t left right a b M out w :=by
  have sep:base≤out:=Nat.le_add_right ..
  have room:out<2^w:=(Nat.le_add_right ..).trans_lt limit
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ sep lfit,ProtocolRAMGeneratedWrite.fits_mono _ sep rfit,
    ROM.bank_room (pages a b M) (size a b M) base out 0 (widths 0) le_rfl room,
    ROM.bank_room (pages a b M) (size a b M) base out 1 (widths 1) le_rfl room,rfl,rfl⟩

include limit lfit rfit in
theorem any :
    let stage:=phase a b H G M w base left right
    stage.Runs m ∧ (∀p,p<base ∨ out+H*chunks G M≤p→stage.image m p=m p) :=by
  intro stage
  have max_:out<2^w:=(Nat.le_add_right ..).trans_lt limit
  have static:=ROM.run (pages a b M) (size a b M) base m max_
  have f₀:=fit a b base left right lfit rfit limit
  have ef : (e).Fits w out := ⟨f₀.apply,f₀.right,f₀.shift,f₀.left⟩
  refine ⟨Procedure.Exec.then static.1 (scan_exec _ _ e mid ef limit),?_⟩
  intro p cond
  have start:base≤out:=Nat.le_add_right ..
  refine (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)).trans ?_
  exact ROM.frame _ _ _ _ _ (by change p<base ∨ out≤p;omega)

include limit lfit rfit in
theorem physical (x : Fin H→Fin G→Cell a) (y : Fin H→Fin G→Cell b)
    (old : Source left x M m) (other : Source right y M m) :
    Reads (bank a b H G M base) (fun h g=>f (x h g) (y h g)) M ((phase a b H G M w base left right).image m) :=by
  have keep (p : ℕ) (lt : p<base) : mid p=m p :=ROM.frame _ _ _ _ _ (Or.inl lt)
  have sx : Source left x M mid:=fun p=>(eval_below _ _ m mid lfit keep).trans (old p)
  have sy : Source right y M mid:=fun p=>(eval_below _ _ m mid rfit keep).trans (other p)
  have static : Static t f M mid:=ROM.binary_mounted f M _ _ _ m widths id (fun _=>rfl)
  have yes:=read_data t left right out (fit a b base left right lfit rfit limit) f (blank a b) mid static x y sx sy
  intro p
  exact (ProtocolRAMGeneratedWrite.read_image _ _ e mid (row H G M p)).trans (yes p)


end
end Hierarchy.DescentRawCablePanel.RegisterJoin

end OAI
