import OAI.Hierarchy.DescentGLPackedResetFrame
import OAI.Hierarchy.DescentResetStemRankRAM

namespace OAI
/-! # One shared previous-group identifier plane through the selected GL reset -/
namespace Hierarchy.DescentResetStemGroupPlane
open DescentGLPacked DescentGLPacked.BankImage DescentGL DescentColonies DescentGLNielsen DescentSIMDLookup
open DescentIssuedFallbackPanel DescentResetStemCompactOrder
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open ThreeFlat.Routing
open scoped Classical Fin.CommRing
noncomputable section
variable {m k groups w : ℕ}

theorem groups_fit (digits : Block m≃Fin groups×Block k) : groups≤2^m := by
  let inj : Fin groups→Block m:=fun g=>digits.symm (g,0)
  have one : Function.Injective inj:=fun g h eqn=>congrArg Prod.fst (digits.symm.injective eqn)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective inj one

def value (digits : Block m≃Fin groups×Block k) (_ : Fin 1) (z : Block m) : Cell m :=
  ⟨(digits z).1.val,(digits z).1.isLt.trans_le (groups_fit digits)⟩

def source (digits : Block m≃Fin groups×Block k) (j : ℕ) :=
  if h : j<2^m then (digits ⟨j,h⟩).1.val else 0

private theorem row_index {r : ℕ} (p : Row 1 r 1) : (row 1 r 1 p).val=p.2.val := by
  simp [row,finProdFinEquiv_apply_val]

private theorem one_data {r b : ℕ} (x : Fin 1→Fin r→Cell b) (p : Row 1 r 1) (hj : p.2.val<r) :
    (data x p).val=(x p.1 ⟨p.2.val,hj⟩).val := by
  have small : (data x p).val<2^b:=by simpa using (data x p).isLt
  let contents : Fin 1→Cell b:=fun i=>
    if ok : p.2.val*1+i.val<r then x p.1 ⟨_,ok⟩ else 0
  have bit:=digit_encode contents (0:Fin 1)
  change digit b 0 (data x p).val=(contents 0).val at bit
  simpa [contents,digit,Nat.mod_eq_of_lt small,hj] using bit

/-- Shared immutable group input. Exactly one full word is initialized for
each previous block, once over the whole reset independently of host count. -/
theorem seed (digits : Block m≃Fin groups×Block k) (base : ℕ) (mem : Memory w) (room : base+2^m<2^w) :
    let newMem:=DescentStaticWordColumn.image base (source digits) mem (2^m)
    (DescentStaticWordColumn.program w base (source digits) (2^m)).Exec mem newMem (4+10*2^m) ∧
      Dense (h:=m) (l:=0) base (value digits) newMem ∧
      ∀a,a<base ∨ base+2^m≤a→newMem a=mem a := by
  intro newMem
  refine ⟨DescentStaticWordColumn.mount base (2^m) (source digits) mem room,?_,
    DescentStaticWordColumn.frame base (2^m) (source digits) mem⟩
  intro p
  have hj : p.2.val<2^m := by simpa [chunks,poolBatchCount] using p.2.isLt
  change DescentStaticWordColumn.image base (source digits) mem (2^m)
    (base + (row 1 (2^m) 1 p).val) = ((data (value digits) p).val : Word w)
  rw [row_index (r:=2^m) p,DescentStaticWordColumn.read _ _ _ _ hj,one_data _ _ hj]
  simp [source,hj,value]

/-- Load the actual measured matrix code from the active selector and shuffle
the shared plane. Every site's donor now reads its original group from this
same resident plane, including all incoming and outgoing old stem rows. -/
theorem run {N : ℕ} (digits : Block m≃Fin groups×Block k) (C : Chart) (sizes : Size C 1 m 0 m w)
    (T : DescentGLControlCode.Tables) (name : DescentGL.Layout m↪Fin N) (key : Expr)
    (basis : DescentGL.Layout m) (mem : Memory w)
    (ks : DescentGLControlCode.fits T key w C.flags)
    (off : DescentGLControlCode.Count m≤T.offsets.size)
    (area : DescentGLControlCode.Count m*N≤T.switches.size)
    (stat : DescentGLControlCode.installed T name mem)
    (observed : ∀i : Fin (DescentGLControlCode.Count m),key.eval mem (i.val:Word w)=((name basis).val:Word w))
    (input : Dense (h:=m) (l:=0) C.input.base (value digits) mem)
    (old : C.input.base+C.input.size≤C.flags) (resident : C.install 1 m 0 m mem=mem) :
    let n:=(schedule m).length
    let ps:=steps (C.chosen m) 1 (2^m) 0 n
    let filled:=image C.flags n (T.expr key) mem
    let dst:=result ps filled
    let out:=((C.chosen m).bank n).base
    let machine:=(scan w C.flags n (T.expr key)).seq (program w ps)
    machine.Exec mem dst ((4+n*(2*(T.expr key).work+4))+clock ps) ∧ CheapCode machine ∧
      (∀z : Block m,dst (out+z.val)=((digits ((rearrange basis).symm z)).1.val:Word w)) ∧
      ∀a,a<C.flags ∨ C.heap m+n*C.page≤a→dst a=mem a := by
  intro n ps filled dst out machine
  obtain ⟨exec,cheap,seen,frame⟩:=reset_resident C sizes T name key basis (value digits) mem ks off area stat observed input old resident
  refine ⟨exec,cheap,?_,frame⟩
  intro z
  let addr : Row 1 (2^m) 1:=position 0 z (by decide)
  have atZ : addr.2.val=z.val:=by simp [addr,position]
  have hj : addr.2.val<2^m:=atZ.trans_lt z.isLt
  have observed:=seen addr
  change dst (out + (row 1 (2^m) 1 addr).val) =
    ((data (fun v z => value digits v ((rearrange basis).symm z)) addr).val : Word w) at observed
  rw [row_index addr,atZ,one_data _ _ hj] at observed
  simpa [value,atZ] using observed

/-- Closed sequence from initial group IDs and the measured matrix selector.
The earlier selector is below the newly seeded array, while all matrix gates
start above it. These inequalities retain every actual control/table read. -/
theorem seed_run {N : ℕ} (digits : Block m≃Fin groups×Block k) (C : Chart) (sizes : Size C 1 m 0 m w)
    (T : DescentGLControlCode.Tables) (name : DescentGL.Layout m↪Fin N) (key : Expr)
    (basis : DescentGL.Layout m) (mem : Memory w)
    (ks : DescentGLControlCode.fits T key w C.input.base)
    (off : DescentGLControlCode.Count m≤T.offsets.size) (area : DescentGLControlCode.Count m*N≤T.switches.size)
    (stat : DescentGLControlCode.installed T name mem)
    (observed : ∀i : Fin (DescentGLControlCode.Count m),key.eval mem (i.val:Word w)=((name basis).val:Word w))
    (old : C.input.base+C.input.size≤C.flags) (resident : C.install 1 m 0 m mem=mem) :
    let n:=(schedule m).length
    let primed:=DescentStaticWordColumn.image C.input.base (source digits) mem (2^m)
    let ps:=steps (C.chosen m) 1 (2^m) 0 n
    let dst:=result ps (image C.flags n (T.expr key) primed)
    let last:=((C.chosen m).bank n).base
    let machine:=(DescentStaticWordColumn.program w C.input.base (source digits) (2^m)).seq
      ((scan w C.flags n (T.expr key)).seq (program w ps))
    machine.Exec mem dst ((4+10*2^m)+((4+n*(2*(T.expr key).work+4))+clock ps)) ∧
    (∀z : Block m,dst (last+z.val)=((digits ((rearrange basis).symm z)).1.val:Word w)) ∧
    (∀{V : Type} (v : V) {c : ℕ} (fits : c≤ m) (hi : Block c) (lo : Fin (2^(m-c))),
      dst (last+(join fits hi lo).val)=((donor digits basis fits v hi lo).1.1.val:Word w)) ∧
    ∀a,a<C.input.base ∨ C.heap m+n*C.page≤a→dst a=mem a := by
  intro n primed ps dst last machine
  have heads : C.input.base≤C.flags:=(Nat.le_add_right ..).trans old
  have above : C.flags≤C.start:=(Nat.le_add_right ..).trans sizes.controls
  have startLe : C.start≤C.heap m:=Nat.le_add_right ..
  have bound:2^m≤C.input.size:=by simpa using sizes.inputSize
  have top : C.input.base+2^m<2^w :=
    (Nat.add_le_add_left bound _).trans_lt ((old.trans (above.trans (startLe.trans (Nat.le_add_right ..)))).trans_lt sizes.top)
  obtain ⟨init,held,keep⟩:=seed digits C.input.base mem top
  change ∀a, a<C.input.base ∨ C.input.base+2^m≤a → primed a=mem a at keep
  have ksf : DescentGLControlCode.fits T key w C.flags:=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ heads ks.1,⟨ks.2.1.1,ks.2.1.2.1,ks.2.1.2.2.trans heads⟩,
      ⟨ks.2.2.1,ks.2.2.2.1,ks.2.2.2.2.trans heads⟩⟩
  have stamps : C.install 1 m 0 m primed=primed:=by
    apply stamped
    intro s i
    have low : C.input.base+2^m≤addr C (s,i):=(Nat.add_le_add_left bound _).trans
      (old.trans (above.trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))))
    exact (keep _ (.inr low)).trans ((congrFun resident (addr C (s,i))).symm.trans
      (at_slot C 1 m 0 m mem s i))
  have fixed : DescentGLControlCode.installed T name primed:=by
    constructor
    · intro i
      rw [keep _ (.inl ((Nat.add_lt_add_left (i.isLt.trans_le off) _).trans_le ks.2.1.2.2))]
      exact stat.1 i
    · intro i
      rw [keep _ (.inl ((Nat.add_lt_add_left (i.isLt.trans_le area) _).trans_le ks.2.2.2.2))]
      exact stat.2 i
  have keys i:=(ProtocolRAM.eval_below key _ mem primed ks.1 (fun a ha=>keep _ (.inl ha))).trans (observed i)
  obtain ⟨native,_,read,framed⟩:=run digits C sizes T name key basis primed ksf off area fixed keys held old stamps
  refine ⟨init.then native,read,fun {_} v {_} fits hi lo=>read (join fits hi lo),?_⟩
  intro a away
  rcases away with h|h
  · exact (framed _ (.inl (h.trans_le heads))).trans (keep _ (.inl h))
  · exact (framed _ (.inr h)).trans (keep _ (.inr ((Nat.add_le_add_left bound _).trans
      (old.trans (above.trans (startLe.trans ((Nat.le_add_right ..).trans h)))))))

/-- No term of this scalar-plane invoice is multiplied by the host count. -/
theorem clock_bound (C : Chart) (T : DescentGLControlCode.Tables) (key : Expr) :
    let n:=(schedule m).length
    let work:=(T.expr key).work
    (4+10*2^m)+((4+n*(2*work+4))+clock (steps (C.chosen m) 1 (2^m) 0 n)) ≤
      (4+10*2^m)+((4+(3*m*m)*(2*work+4))+(4+(3*m*m)*(4+2^m*224))) := by
  intro n work
  have cap : n≤3*m*m:=DescentGLNielsen.length_le m
  have run:=tariff (C.chosen m) 1 m 0 n
  simp only [Nat.one_mul] at run
  exact Nat.add_le_add_left (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ cap) 4)
    (run.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ cap) 4))) _

end
end Hierarchy.DescentResetStemGroupPlane

end OAI
