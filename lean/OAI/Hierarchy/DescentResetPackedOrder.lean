import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentCoarseCoordinates
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Recovering old relative order from the physically remixed binary planes -/
namespace Hierarchy.DescentPlainTerminal.PackedOrder
open DescentGL DescentColonies DescentIssuedFallbackPanel DescentSIMDLookup DescentPackedZip
open DescentPacking.PackedMatch.Local Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {m c n r w H G M : ℕ}

def plane (d : Fin m) (x : Block m) : Cell 1 := finTwoEquiv.symm (x.val.testBit d.val)

def planeCode (r : ℕ) : (Block r→Cell 1) ≃ Cell (2^r) :=
  (encode 1 (2^r)).trans (finCongr (congrArg (2^·) (Nat.one_mul (2^r))))

def panel (small : c≤ m) (L : DescentGL.Layout m) (v : Block c) (d : Fin m) :=
  planeCode (m-c) (fun x=>plane d ((rearrange L).symm (join small v x)))

def bits (r m : ℕ) := (2^r)*m

def restore (z : Cell (bits r m)) (x : Block r) : Cell m :=
  (wordBits m).symm (fun d=>finTwoEquiv
    ((planeCode r).symm ((encode (2^r) m).symm z d) x))

theorem exact_word (small : c≤ m) (L : DescentGL.Layout m) (hi : Block c) (x : Block (m-c)) :
    restore (encode (2^(m-c)) m (panel small L hi)) x=(rearrange L).symm (join small hi x) := by
  apply (wordBits m).injective
  funext d
  simp only [restore,Equiv.apply_symm_apply,Equiv.symm_apply_apply,panel,plane,Computability.VPVNP.LiveHeader.testBit_wordBits]

def cmp (i x : Block r) (z : Cell (bits r m)) : Cell n :=
  if restore z i<restore z x then 1 else 0

theorem empty_word (x : Block r) : restore (m:=m) (0 : Cell (bits r m)) x=0 := by
  have allZero (a j : ℕ) : (encode a j).symm 0=(fun _=>0) := by
    apply (encode a j).symm_apply_eq.mpr
    symm
    apply Fin.ext
    simp [encode]
  have emptyPlane : (planeCode r).symm 0=(fun _=>0) := by simpa [planeCode] using allZero 1 (2^r)
  apply (wordBits m).injective
  funext d
  calc
    _ = finTwoEquiv ((planeCode r).symm ((encode (2^r) m).symm 0 d) x) :=
      congrFun ((wordBits m).apply_symm_apply _) d
    _ = false := by rw [allZero, emptyPlane]; rfl
    _ = _ := (wordBits_zero d).symm

theorem cmp_zero (i x : Block r) : cmp (n:=n) (m:=m) i x 0=0 := by simp [cmp,empty_word]

/-- A direct unary public lookup keeps zeros on the padded lanes of the final packet. -/
def projected (rom : Bank) (e : Expr) := Expr.lookup rom e

theorem project {a b : ℕ} (rom : Bank) (e : Expr) (out : ℕ) (f : Cell a→Cell b) (zero : f 0=0)
    (m : Memory w) (x : Fin H→Fin G→Cell a) (fits : rom.Fits w out) (size : rom.bits=a*M)
    (image : ∀key:Cell (a*M),m (rom.base+key.val)=((DescentSIMDLookup.table f key).val:Word w))
    (source : Source e x M m) : Source (projected rom e) (fun h g=>f (x h g)) M m := by
  intro p
  have h : (data x p).val<rom.size:=by simp [Bank.size,size]
  have vals : DescentSIMDLookup.table f (data x p)=data (fun h g=>f (x h g)) p := by
    unfold DescentSIMDLookup.table data
    apply congrArg (encode b M)
    funext j
    by_cases live : p.2.val*M+j.val<G <;> simp [live,zero]
  change rom.read m (e.eval m _)=_
  rw [source p,Bank.read,Fin.val_cast_of_lt (h.trans fits.2.1),Nat.mod_eq_of_lt h,image,vals]

/-- Each source plane stores one bit per original block, readdressed by the
actual inverse GL transform, in the original bit order. -/
theorem order_field (small : c≤ m) (L : DescentGL.Layout m) (T : Fin m→Tables) (field : Fin m→Expr)
    (i x : Block (m-c)) (out : ℕ) (rom : Bank) (mem : Memory w)
    (bounds : Gather.Bounds (w:=w) (d:=2^(m-c)) (M:=M) T field out)
    (tables : ∀j,Static (T j) (Gather.setField (d:=2^(m-c)) j) M mem)
    (read : ∀j,Source (field j) (fun (_ : Fin H) hi=>panel small L hi j) M mem)
    (room : rom.Fits w out) (size : rom.bits=bits (m-c) m*M)
    (dict : ∀k:Cell (bits (m-c) m*M),mem (rom.base+k.val)=((DescentSIMDLookup.table (M:=M) (cmp (n:=n) (m:=m) i x) k).val:Word w)) :
    Source (projected rom (Gather.assembly T field))
      (fun (_ : Fin H) hi=>if (rearrange L).symm (join small hi i)<(rearrange L).symm (join small hi x)
        then (1:Cell n) else 0) M mem := by
  have raw:=Gather.collected T field out bounds mem tables (fun (_:Fin H) hi j=>panel small L hi j) read (List.finRange m)
  simp only [List.mem_finRange,ite_true] at raw
  have projected:=project rom (Gather.assembly T field) out (cmp (n:=n) (m:=m) i x) (cmp_zero i x) mem
    (fun (_:Fin H) hi=>encode (2^(m-c)) m (panel small L hi)) room size dict raw
  simpa only [cmp,exact_word] using projected

end
end Hierarchy.DescentPlainTerminal.PackedOrder

end OAI
