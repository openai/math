import OAI.Hierarchy.DescentSubwordHeader
import OAI.Hierarchy.DescentGLPackedScale

namespace OAI
/-! # Complete measured repacking from a wide dyadic bank to a narrower one -/
namespace Hierarchy.DescentSIMDLookup.Subwords
open DescentPackedColony.Phase.Arena ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G K R M w a : ℕ}

def destination (base a H G R M : ℕ) := base+4*(1+H*chunks G M+R*stride a R M)
def finish (base a H G R M : ℕ) := destination base a H G R M+H*chunks G M

private theorem rounded (s : ℕ) : 2^(Nat.clog 2 s)≤2*(s+1) := by
  cases eq:Nat.clog 2 s with
  | zero=>simp; omega
  | succ i=>
    have bound:=Nat.pow_lt_of_lt_clog (show i<Nat.clog 2 s by omega)
    rw [pow_succ]
    omega

theorem geometry (base : ℕ) (input : Bank) (source : input.Fits w base) (inputSize : H*chunks G (R*M) ≤ input.size)
    (fits : finish base a H G R M<2^w) : Room (chart base a H G R M) input a H G R M w (destination base a H G R M) := by
  let T:=chart base a H G R M
  let N:=H*chunks G M
  let out:=destination base a H G R M
  have lower:base≤out:=by dsimp [out,destination];omega
  have small:out+N<2^w:=fits
  have shape (B : Bank) (inside : B.base+B.size≤out) : B.Fits w out :=
    ⟨Nat.two_pow_pos _,by omega,inside⟩
  have rm:=rounded N
  have rd:=rounded (R*stride a R M)
  refine ⟨shape _ ?_,Nat.le_pow_clog (by decide) _,shape _ ?_,Nat.le_pow_clog (by decide) _,
    ⟨source.1,source.2.1,source.2.2.trans lower⟩,inputSize,shape _ ?_,Nat.le_pow_clog (by decide) _,small⟩ <;>
    dsimp [T,chart,Bank.size,out,destination,N] at * <;> omega

theorem saved (base : ℕ) (input : Bank) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M)
    (X : Fin H→Fin G→Cell a) (mem : Memory w)
    (source : input.Fits w base) (inputSize : H*chunks G (R*M) ≤ input.size)
    (words : ∀p : Row H G (R*M),mem (input.base+(row H G (R*M) p).val)=((data X p).val:Word w))
    (fits : finish base a H G R M<2^w) :
    let T:=chart base a H G R M
    let count:=H*chunks G M
    let I:=literals (w:=w) base H a size ratio pos
    let out:=destination base a H G R M
    let program:=I.program.seq (scan w out count (term T input))
    ∃dst,program.Exec mem dst ((4+10*I.length)+(4+count*(2*(term T input).work+4))) ∧
      CheapCode program ∧ (∀p : Row H G M,dst (out+(row H G M p).val)=((data X p).val:Word w)) ∧
      ∀z,z<base ∨ finish base a H G R M≤z→dst z=mem z := by
  let I:=literals (w:=w) base H a size ratio pos
  let T:=chart base a H G R M
  let N:=H*chunks G M
  let out:=destination base a H G R M
  have endOld:endAt base a H G R M≤out:=by dsimp [endAt,out,destination];omega
  have lower:base≤out:=by dsimp [out,destination];omega
  have small:out+N<2^w:=fits
  have smallI : I.low+I.length<2^w := by
    rw [show I.low=base from rfl,length_eq]
    dsimp [endAt] at endOld;omega
  obtain ⟨emit,rom,keep⟩:=I.issue mem smallI
  have live (p : Row H G (R*M)) :
      I.output mem (input.base+(row H G (R*M) p).val)=((data X p).val:Word w) := by
    apply (keep _ (.inl ?_)).trans (words p)
    have before:=source.2.2
    exact (Nat.add_lt_add_left ((row H G (R*M) p).isLt.trans_le inputSize) _).trans_le before
  have controls:=geometry (a:=a) base input source inputSize fits
  obtain ⟨exec,cheap,read,frame⟩:=run T input out controls size ratio pos X (I.output mem)
    (actual base H a size ratio pos _ rom) live
  refine ⟨_,emit.then exec,cheap_seq I.hardware.1 cheap,read,?_⟩
  intro z bound
  rcases bound with low|high
  · exact (frame _ (.inl (low.trans_le lower))).trans (keep _ (.inl low))
  · exact (frame _ (.inr high)).trans (keep _ (.inr (endOld.trans (by change out≤z;change out+N≤z at high;omega))))

theorem invoice (base H a : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) (input : Bank) :
    let T:=chart base a H G R M
    let count:=H*chunks G M
    let I:=literals (w:=w) base H a size ratio pos
    (4+10*I.length)+(4+count*(2*(term T input).work+4))≤
      8+128*count+10*(R*stride a R M) := by
  dsimp only
  rw [length_eq]
  simp only [term,Expr.work]
  omega

theorem dictionary_budget (a payload r e : ℕ) (reserve : r+a*(2^r*2^e)≤payload/2) :
    2^r*stride a (2^r) (2^e)≤2^(payload/2) := by
  unfold stride
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide) reserve

end
end Hierarchy.DescentSIMDLookup.Subwords

end OAI
