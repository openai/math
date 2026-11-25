import OAI.Hierarchy.DescentDonorSourceQuery
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # The literal short-key selection pages for return of a source incidence rank -/
namespace Hierarchy.DescentParallelBase.SourceReturn.RAM.ROM
open DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentPackedColony DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentOrdinaryAtomFieldRAM.ROM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {P Q H G M b w base:ℕ}
local notation "T"=>P*(Q*P)
local notation "a"=>Packed.bits T
local notation "width"=>(a+b)*M

def address (i:Fin T) (j:Fin 2):Fin (T*2):=finProdFinEquiv (i,j)
def book (P Q b M:ℕ) (i:Fin ((P*(Q*P))*2)):=let p:=finProdFinEquiv.symm i;binary (choose (b:=b) p.1) M p.2
local notation "pages"=>book P Q b M
local notation "fee"=>T*2*2^width

def table (P Q b M base:ℕ) (i:Fin (P*(Q*P))):=
  joined (book P Q b M) ((Packed.bits (P*(Q*P))+b)*M) base (address i)
local notation "tables"=>table P Q b M base

@[simp] theorem at_ (i:Fin T) (j:Fin 2):pages (address i j)=binary (choose (b:=b) i) M j:=by simp [book,address]

theorem bound (i:Fin (T*2)):(pages i).bits≤width:=by
  obtain ⟨⟨j,t⟩,rfl⟩:=finProdFinEquiv.surjective i
  change (pages (address j t)).bits≤width;rw [at_];fin_cases t <;> first | exact le_rfl | exact Nat.mul_le_mul_right M (Nat.le_add_right a b)

/-- The exponents are independent of the number of old or new hosts. Their
only lane digits are the short parent coordinate and a local incidence rank. -/
theorem half_word (P Q b M w:ℕ) (short:(Packed.bits (P*(Q*P))+b)*M≤w/2):
    (P*(Q*P))*2*2^((Packed.bits (P*(Q*P))+b)*M)≤(P*(Q*P))*2*2^(w/2):=Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) short)

theorem setup (P Q b M base w:ℕ) (old:Memory w)
    (room:base+(P*(Q*P))*2*2^((Packed.bits (P*(Q*P))+b)*M)<2^w):
    let pages_:=book P Q b M
    let width_:=(Packed.bits (P*(Q*P))+b)*M
    let fee_:=(P*(Q*P))*2*2^width_
    let done:=after pages_ width_ base old
    (mount pages_ width_ w base).Exec old done (4+10*fee_) ∧
      (∀i,Static (table P Q b M base i) (choose (b:=b) i) M done) ∧
      (∀z,z<base ∨ base+fee_≤z→done z=old z) ∧ CheapCode (mount pages_ width_ w base):= by
  intro pages_ width_ fee_ done
  exact ⟨(DescentOrdinaryAtomFieldRAM.ROM.run pages_ width_ base old room).1,
    fun i=>binary_mounted _ M pages_ width_ base old bound _ (at_ i),frame pages_ width_ base old,cheap pages_ width_ w base⟩

/-- Every source lookup field is evaluated before the literal pages. Thus
authenticating it and its predecessor ports on the old memory suffices. -/
theorem fresh (R:Fin H→Fin P→Option (Fin H)) (rank:Fin Q→Fin P→Fin H→Fin G→Cell b) (q:Fin H→Fin G→Option (Fin T))
    (ports:Ports P) (bank:Fin Q→Fin P→Bank) (query:Expr) (out:Bank) (old:Memory w)
    (before:∀l r,Accessible ports (bank l r) H G M w base) (queryFits:query.Fits w base)
    (neighbors:Mounted ports R old G M) (inputs:Source query (fun v g=>Packed.token (q v g)) M old)
    (ranks:∀l r,Reads (bank l r) (rank l r) M old) (apart:base+fee≤out.base) (room:out.base+H*chunks G M<2^w):
    let printed:=mount pages width w base
    let loaded:=after pages width base old
    let f:=body tables ports bank query H
    let executed:=scan w out.base (H*chunks G M) f
    let done:=image out.base (H*chunks G M) f loaded
    (printed.seq executed).Exec old done ((4+10*fee)+(4+H*chunks G M*(2*f.work+4))) ∧ Reads out (output R rank q) M done ∧
    (∀i,i<base ∨ out.base+H*chunks G M≤ i→done i=old i) ∧ CheapCode (printed.seq executed):=by
  intro printed loaded f executed done
  have lt:out.base<2^w:=(Nat.le_add_right ..).trans_lt room
  have below:base≤out.base:=(Nat.le_add_right base fee).trans apart
  obtain ⟨install,rom,stable,cheap'⟩:=setup P Q b M base w old (apart.trans_lt lt)
  let prog (j:Fin T):=peerExpr ports (bank (parts j).2.1 (parts j).2.2) H (parts j).1
  let value (j:Fin T) (v:Fin H) (g:Fin G):=choose j (Packed.token (q v g)) (field R rank j v g)
  have fetch (j:Fin T):Source (prog j) (field R rank j) M loaded:=by
    have truth:=peerSource ports _ base (before (parts j).2.1 (parts j).2.2) R old neighbors _ (ranks (parts j).2.1 (parts j).2.2) (parts j).1
    intro p;exact (ProtocolRAM.eval_below _ _ old loaded (peer_fits ports _ base (before (parts j).2.1 (parts j).2.2) (parts j).1) (fun i hi=>stable i (.inl hi))).trans (truth p)
  have ask:Source query (fun v g=>Packed.token (q v g)) M loaded:=by
    intro p;exact (ProtocolRAM.eval_below query _ old loaded queryFits (fun i hi=>stable i (.inl hi))).trans (inputs p)
  have layout (j:Fin T):DescentPackedZip.Fits (tables j) query (prog j) a b M out.base w:=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ below queryFits,
      ProtocolRAMGeneratedWrite.fits_mono _ below (peer_fits ports _ base (before (parts j).2.1 (parts j).2.2) (parts j).1),
      bank_room pages width base out.base _ (bound _) apart lt,bank_room pages width base out.base _ (bound _) apart lt,
      congrArg Page.bits (at_ j 0),congrArg Page.bits (at_ j 1)⟩
  have final:=RAM.run_sources R rank q tables ports bank query out loaded layout rom ask fetch room
  refine ⟨Procedure.Exec.then install final.1,final.2.1,?_,cheap_seq cheap' final.2.2⟩
  intro i ends
  exact (ProtocolRAMGeneratedWrite.frame_image out.base (H*chunks G M) f loaded i (by rcases ends with l|r <;> omega)).trans (stable i (by rcases ends with l|r <;> omega))

end
end Hierarchy.DescentParallelBase.SourceReturn.RAM.ROM

end OAI
