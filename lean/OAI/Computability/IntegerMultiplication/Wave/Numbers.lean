import OAI.Computability.IntegerMultiplication.Wave.Chart
import OAI.Computability.IntegerMultiplication.Curtain.Scanner

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Wave
open Param Scale Halo Strip Dims Adic Code Bits Axon Cap Loom Staff Brief Carry Echo
-- Trace exact binary labels general purpose
abbrev ink (x:Fin 2) : Bool:=decide (x.val=1)
abbrev recolor := List.map ink
theorem recolorE : Easy recolor := (Easy.finite ink).mapping
private theorem spectral (x:Raw 2):
    Bits.value (recolor x) = Adic.code x:= by
  induction x with
  | nil=>rfl
  | cons a l ih=>
    change digit (ink a)+2*Bits.value (recolor l)=a.val+2*Adic.code l
    rw [ih]; congr 1; fin_cases a <;> decide
variable {I:Type}{r:Regime I}{A:I→Type}
noncomputable section
variable (s:(i:I)→Series (A i))(k:I→ℕ)
variable (v:∀ i,(s i).count=2^k i)(h:Realizes r k)
include v h
abbrev markNum(i:I): A i→Bits.Word:=
  fun a=> Bits.short (k i) (((s i).index a).val)
theorem marks :
    Strip.Trace r s (fun i a=>send (markNum s k i a)) := by
  let t i : Adopt (s i) (line 2 (k i)):=
    (((s i).native.thenDo (Halo.reels (v i))).thenDo (noir (k i)).back)
  have u:= (Curtain.aims (s:=fun i=> line 2 (k i)) (fun i x=>least x) (Curtain.issues k h) recolor recolorE.poly).via t
  suffices q: (fun i=> (fun a=>send (recolor (least a))) ∘ (t i).cast)=fun i a=> send (markNum s k i a) by rw [← q]; exact u
  funext i a; apply congrArg send
  apply Bits.word_inject
  · rw [markNum,Bits.short_length]
    simp only [recolor,List.length_map,length']
  · rw [markNum,Bits.value_short,spectral]
    have p : ((s i).index a).val<2^k i := by rw [← v i]; exact ((s i).index a).isLt
    rw [Nat.mod_eq_of_lt p]
    let b := (t i).cast a
    change Adic.number b=((s i).index a).val
    rw [← Axon.bright]
    change ((noir (k i)).cast b).val=_
    change ((noir (k i)).cast ((noir (k i)).cast.symm _)).val=_
    rw [Equiv.apply_symm_apply]; rfl

variable (n:I→ℕ)(a:(i:I)→Direction (n i))
abbrev α(i:I):=Person (Echo.criterion (n i)) true (a i)
abbrev ν(i):=Scale.P (n i)
variable  (Q:(i:I)→α n a i→Tree)(q: Strip.Trace r (X0 n a true) Q)
omit h v
variable (H:Realizes r (fun i=>(a i).val))(g:Guide r n)(w:∀ i,Season (n i))
variable (j:I→Bits.Word)(J:r.Has j)
variable (L:∀ i,Bits.value (j i)= Cap.coefficient (modulus (n i)) (a i))

abbrev PiScale:= onboard r Q q.meter
variable (R:Figure (PiScale n a Q q) (fun i:Sigma (α n a)=>((X0 n a true i.1).index i.2).val))

-- arbitrary prefix element. show wheel computable
include H g w J L R
theorem driver :
    Figure (PiScale n a Q q) (fun i:Sigma (α n a)=>wheel (criterion (n i.1)) (a i.1) (modulus (n i.1)) i.2) := by
  let l:= Sigma.fst (β:=α n a)
  let D:= Sigma (α n a)
  let m:=n ∘ l
  let b:=(fun (i:D)=>a i.1)
  let F:=PiScale n a Q q
  have aM (v:I→Tree)(z:r.Small v):F.Small (v ∘ l):=onboard_small _ _ _ z
  have g' : Guide F m:= by
    obtain ⟨c,x,e⟩:=g
    -- c figure, actually nested?
    exact ⟨c ∘ l,aM (send ∘ c) x,fun i=>e _⟩
  have H':Realizes F (fun i:D=>(b i).val):=aM (fun i=> send (Code.tally (a i).val)) H
  let w':∀ i,Season (m i):=fun i=>w _ -- Function.comp Prop? w type forall, not function ?
  have U : Figure F (fun i=>Cap.coefficient (modulus (m i)) (b i)):=⟨j ∘ l,aM (send ∘ j) J,fun i=> L _⟩
  have X: Figure F (fun i=>Well.axio m b i * afterS (criterion (m i)) true (b i)):= (side_ m b g' H').multiplied
    ((chart m w' b true g' H').2)
  -- compute ((prefixIndex)*X)
  let T:D→ℕ:=fun i=> ((X0 n a true i.1).index i.2).val*(Well.axio m b i*afterS (criterion (m i)) true (b i))
  have V : Figure F T:=R.multiplied X
  let s:=Param.lanes ∘ m; let N:=g'.spread m
  unfold wheel Atoll.leanValue
  apply U.multiplied
  apply (Cap.lists s N _ _).2
  let A:=Across s
  let root(k:A):=k.1
  let r':= signal s N
  have G:= g'.abroad m N
  have V': Figure r' (T ∘ root):= Garden.ferryF s N V
  have I:=floor_ s N
  let a' : (i:A)→Direction ((m ∘ root) i):=fun k=>k.2
  have B := (chart (m ∘ root) (fun i=>w _ ) a' true G I).2
  let x (k:A):= ((Crown (criterion (m k.1)) (b k.1) k.1.2) k.2).val
  have z : Figure r' x:=by
    unfold x
    simp_rw [crownV]
    exact (V'.quotients B).modded (G.length_ (m ∘ root) I)
  have p:Figure r' (fun k:A=>Cap.base (modulus (m k.1)) k.2):=
    base_ (m ∘ root) a' G I false
  exact (z.multiplied p).variant (.natural 0) (I.below (landing s N _ H'))

end
end Wave

end IntegerMultiplication
end Computability
end OAI
