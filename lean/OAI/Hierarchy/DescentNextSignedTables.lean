import OAI.Hierarchy.DescentNextSignedIssue
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # The eighteen shared literal pages for a signed successor window -/
namespace Hierarchy.DescentNextSignedWindow.Native.ROM
open DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentPackedColony DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentOrdinaryAtomFieldRAM.ROM DescentPacking.PackedMatch.Local
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D cap b H G M w c base : ℕ} (j:Fin (2*cap))

def width (b M : ℕ):=(b*8+b)*M

def page (D b M : ℕ) : Fin 9→Fin 2→Page :=Fin.lastCases
  (binary (fun t (_:Cell 0)=>Native.table (D:=D) (b:=b) j t) M)
  (fun (i:Fin 8)=>binary (Gather.setField (d:=b) i) M)

def address (k:Fin 9) (s:Fin 2):Fin 18:=finProdFinEquiv (k,s)

def book (D b M : ℕ) (a:Fin 18):Page:=let p:Fin 9×Fin 2:=finProdFinEquiv.symm a;page j D b M p.1 p.2

local notation "pages" => book j D b M
local notation "wd" => width b M
local notation "bank" i => joined pages wd base (address i)
def joins (D b M base:ℕ) (i:Fin 8) := joined (book j D b M) (width b M) base (address i.castSucc)
def final (D b M base:ℕ):= joined (book j D b M) (width b M) base (address (Fin.last 8))

@[simp] theorem join_at (i:Fin 8) (t:Fin 2):pages (address i.castSucc t)=binary (Gather.setField (d:=b) i) M t:=by simp only [book,address,Equiv.symm_apply_apply,page,Fin.lastCases_castSucc]
@[simp] theorem final_at (t:Fin 2):pages (address (Fin.last 8) t)=binary (fun x (_:Cell 0)=>Native.table (D:=D) (b:=b) j x) M t:=by simp only [book,address,Equiv.symm_apply_apply,page,Fin.lastCases_last]

theorem bound (a:Fin 18):(pages a).bits≤wd:=by
  obtain ⟨⟨k,s⟩,rfl⟩:=(finProdFinEquiv : Fin 9 × Fin 2 ≃ Fin 18).surjective a
  change (pages (address k s)).bits≤wd
  induction k using Fin.lastCases with
  | last=>
    rw [final_at];fin_cases s <;> change _ ≤(b*8+b)*M <;>
      simpa [binary] using Nat.mul_le_mul_right M (Nat.le_add_right (b*8) b)
  | cast k=>
    rw [join_at];fin_cases s <;> change _ ≤(b*8+b)*M <;> first
      | exact le_rfl
      | exact Nat.mul_le_mul_right M (Nat.le_add_right (b*8) b)

theorem fits {x y z t : ℕ} (fn:Cell x→Cell y→Cell z) (k:Fin 9)
    (definition_:∀s,pages (address k s)=binary fn M s) (apart:base+18*2^wd≤t) (room:t<2^w)
    (u v:Expr) (left:u.Fits w t) (right:v.Fits w t):DescentPackedZip.Fits (bank k) u v x y M t w:=
  ⟨left,right,bank_room pages wd base t _ (bound j _) apart room,bank_room pages wd base t _ (bound j _) apart room,
    congrArg Page.bits (definition_ 0),congrArg Page.bits (definition_ 1)⟩

section
local notation "fee" => 18*2^wd
local notation "js" => joins j D b M base
local notation "last" => final j D b M base

theorem fresh (field:Fin c→Fin 8→Expr) (out:Bank) (m:Memory w)
    (rows:Fin H→Fin G→Fin c→Option (Record D cap)) (target:Fin H→Fin G→Option (Stage.Live D cap))
    (early:∀a i,(field a i).Fits w base)
    (actual:∀a i,Source (field a i) (fun h g=>(fields (rows h g a) i:Cell b)) M m)
    (small:∀h g i t,fields (rows h g i) t<2^b)
    (empty:∀h g,target h g=none→∀i,(rows h g i).bind (fun r=>read r j)=none)
    (live:∀h g r,target h g=some r→∃i,(rows h g i).bind (fun u=>read u j)=some r ∧ ∀l,l≠i→(rows h g l).bind (fun u=>read u j)=none)
    (apart:base+fee≤out.base) (room:out.base+H*chunks G M<2^w):
    let printed:=mount pages wd w base
    let loaded:=after pages wd base m
    let op':=op last (fun a=>Gather.assembly js (field a))
    let code:=scan w out.base (H*chunks G M) op'
    let done:=image out.base (H*chunks G M) op' loaded
    (printed.seq code).Exec m done ((4+10*fee)+(4+H*chunks G M*(2*op'.work+4))) ∧
    DescentPackedColony.Reads out (fun h g=>DescentSignedCableCodec.encode (target h g)) M done ∧
    (∀a,a<base ∨ out.base+H*chunks G M≤a→done a=m a) ∧ CheapCode (printed.seq code):=by
  intro printed loaded op' code done
  have lt:out.base<2^w:=(Nat.le_add_right ..).trans_lt room
  have below:base≤out.base:=(Nat.le_add_right base fee).trans apart
  have mounted:=DescentOrdinaryAtomFieldRAM.ROM.run pages wd base m (apart.trans_lt lt)
  have stable:=frame pages wd base m
  have inputs (a:Fin c) (i:Fin 8):Source (field a i) (fun h g=>(fields (rows h g a) i:Cell b)) M loaded:=by
    intro p;exact (ProtocolRAM.eval_below (field a i) _ m loaded (early a i) (fun z hz=>stable z (.inl hz))).trans (actual a i p)
  have guards (a:Fin c):Gather.Bounds (d:=b) (M:=M) (w:=w) js (field a) out.base:=by
    intro i
    have held:=fits (D:=D) (base:=base) j (Gather.setField (d:=b) i) i.castSucc (join_at (D:=D) j i) apart lt (.lit 0) (field a i) trivial
      (ProtocolRAMGeneratedWrite.fits_mono (field a i) below (early a i))
    exact ⟨held.right,held.shift,held.apply,held.shiftBits,held.applyBits⟩
  have finalFit (a:Fin c):DescentPackedZip.Fits last (Gather.assembly js (field a)) (.lit 0) (b*8) 0 M out.base w:=
    fits j (fun x (_:Cell 0)=>Native.table (D:=D) (b:=b) j x) (Fin.last 8) (final_at j) apart lt _ _ (Gather.fits _ _ _ (guards a) _) trivial
  have stat (i:Fin 8):Static (js i) (Gather.setField (d:=b) i) M loaded:=binary_mounted _ M pages wd base m (bound j) _ (join_at (D:=D) j i)
  have lastStatic:Static last (fun x (_:Cell 0)=>Native.table (D:=D) (b:=b) j x) M loaded:=binary_mounted _ M pages wd base m (bound j) _ (final_at j)
  obtain ⟨cpu,read,cheap'⟩:=run_fields j js last field out loaded rows target guards stat inputs finalFit small lastStatic empty live room
  refine ⟨Procedure.Exec.then mounted.1 cpu,read,?_,cheap_seq (cheap pages wd w base) cheap'⟩
  intro a away
  have fin:=ProtocolRAMGeneratedWrite.frame_image out.base (H*chunks G M) op' loaded a (by rcases away with l|r <;> omega)
  exact fin.trans (stable a (by rcases away with l|r <;> omega))

end

private theorem collect_work (js:Fin 8→Tables) (field:Fin 8→Expr) (l:List (Fin 8)) (limit:ℕ) (small:∀i,(field i).work≤limit):
    (Gather.collect js field l).work≤1+l.length*(limit+11):=by
  induction l with
  | nil=>simp [Gather.collect,Expr.work]
  | cons i l ih=>have cost:=small i;simp only [Gather.collect,Tables.read,Expr.work,List.length_cons,Nat.succ_mul];omega

theorem operation_work (js:Fin 8→Tables) (lut:Tables) (field:Fin c→Fin 8→Expr) (lim:ℕ) (small:∀a i,(field a i).work≤lim):
    (op lut (fun a=>Gather.assembly js (field a))).work≤1+c*(14+8*(lim+11)):=by
  have one (a:Fin c):(lut.read (Gather.assembly js (field a)) (.lit 0)).work≤13+8*(lim+11):=by
    have hold:=collect_work js (field a) (List.finRange 8) lim (small a)
    rw [List.length_finRange] at hold;simp only [DescentPackedZip.work,Expr.work,Gather.assembly];omega
  have amount:=work_total (fun a=>lut.read (Gather.assembly js (field a)) (.lit 0)) _ one (List.finRange c)
  simpa only [op,List.length_finRange,show 13+8*(lim+11)+1=14+8*(lim+11) by omega] using amount

theorem table_words (b M w : ℕ) (short:width b M≤w/2):18*2^(width b M)≤18*2^(w/2):=Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) short)

end
end Hierarchy.DescentNextSignedWindow.Native.ROM

end OAI
