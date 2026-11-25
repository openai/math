import OAI.Hierarchy.TaggedWideLeafBanks
import OAI.Hierarchy.TaggedWideLeafFactors
import OAI.Hierarchy.TaggedWideOutputPlane
import OAI.Hierarchy.TaggedWideReportedFiniteSums

namespace OAI
/-! # One workspace contraction for all positive, private and site wires -/

noncomputable section
namespace Hierarchy.Tagged.WideStack.Leaf
open ThreeFlat Routing
open ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open scoped Classical BigOperators
set_option maxHeartbeats 1000000

variable {F : Type*} [Field F] {T : Type} [Fintype T] {N groups ports lanes view w m : ℕ}
    (key : T ↪ ℕ×ℕ) (raw : Fin N→ProtocolRAMEmit.Row) (positive : Fin N→Prop) (stage : Fin N→ℕ)
private abbrev planePort (groups ports view : ℕ) := (Fin groups × Fin ports) × Fin view

private abbrev printedWidth (directory : T ↪ ℕ×ℕ) (wordWidth : ℕ) (t : T) : ℕ :=
  ⌈dyadic (directory t).2*wordWidth⌉₊

private abbrev packedPort (directory : T ↪ ℕ×ℕ) (groups ports lanes wordWidth : ℕ) :=
  OutputData T (Fin groups) ports lanes (printedWidth directory wordWidth)

private abbrev retainedLabels (groups w m : ℕ) :=
  Lanes (n:=fun _ : T=>N) (fun _ : T=>groups) (fun t=>(key t).2)
    (fun t=>atScale positive stage (key t).1 raw) w m

variable (s : ∀t,Installed F groups ports lanes w m (key t).2 (atScale positive stage (key t).1 raw))
    (cap : {i : Fin N // ¬positive i}→ℕ)

def publicLabels (a : (i:Fin N)→Fin (2^(raw i).width)) :
    retainedLabels key raw positive stage groups w m :=
  expandedLabels (n:=fun _ : T=>N) (fun _ : T=>groups) (fun t=>(key t).2)
    (fun t=>atScale positive stage (key t).1 raw) w m (fun t=>(s t).unique)
    (fun p=>let q := edgeBit key (fun _ : T=>groups) raw positive stage w m p
            (a q.1.val).val.testBit q.2.val)

def freeLabels (a : (i:Fin N)→Fin (2^(raw i).width)) : PrivatePorts cap :=
  privateEncode (fun e : {i : Fin N // ¬positive i}=>(raw e.val).width) cap (fun e j=>(a e.val).val.testBit j.val)

def decoded (x : packedPort key groups ports lanes w→Bool) : planePort groups ports view→Bool :=
  fun p=>positivePlane (printedWidth key w) x p.1 p.2.val

def decoder : BitNetwork F (Fintype.card ((packedPort key groups ports lanes w)⊕(planePort groups ports view))) :=
  outputNet (printedWidth key w) Prod.fst (fun p : planePort groups ports view=>p.2.val)
    (Sum.inr : planePort groups ports view→packedPort key groups ports lanes w⊕planePort groups ports view) Sum.inl

def privateWeight (y : PrivatePorts cap) : F :=
  ∏e,if ∀j : Fin (cap e),j.val<(raw e.val).width→y false e j=y true e j then 1 else 0

private theorem sum_agree {X : Type*} {a b : Fintype X} {f g : X→F} (same : ∀x,f x=g x) :
    (@Finset.univ X a).sum f = (@Finset.univ X b).sum g := by
  cases Subsingleton.elim a b
  exact Finset.sum_congr rfl fun x _=>same x

private theorem guard_choice {A : Type*} {p : Prop} {d d' : Decidable p} {x y : A} :
    @ite A p d x y = @ite A p d' x y := by
  cases Subsingleton.elim d d'
  rfl

private theorem decoder_sum (x : packedPort key groups ports lanes w→Bool)
    (f : (planePort groups ports view→Bool)→F) (planes : Fintype (planePort groups ports view→Bool)) :
    sumWith planes (fun p=>TypedWiring.value (decoder key) (Sum.elim x p)*f p)=f (decoded key x) := by
  have actual := output_contract (printedWidth key w) Prod.fst (fun p : planePort groups ports view=>p.2.val)
    (id : packedPort key groups ports lanes w→packedPort key groups ports lanes w) x f
  refine (sum_agree ?_).trans actual
  intro p
  rfl

variable {H : Type} [Fintype H]

/-- Every summand on the left is the product of the actual closed positive
cuts, their zero tests, both private endpoint guards, the physical OR plane
and the remaining signed site network. Its value is the original row-word
sum with just the chronological site data still open. -/
theorem contract_reported (hw : 0<w) (room : ∀e,(raw e.val).width≤cap e)
    (cover : ∀i,positive i→0<(raw i).width→
      ∃t,key t=(stage i,widthIndex m ((raw i).width/(w:ℝ))) ∧ (raw i).group<groups)
    (cut : T→(Pin (banks s) cap H (planePort groups ports view)→Bool)→F)
    (padding privateGate plane site : ((Pin (banks s) cap H (planePort groups ports view))→Bool)→F)
    (cuts : ∀ z y h p i,cut i (write (banks s) cap z y h p)=(banks s i).settings.close (z i))
    (pad : ∀ z y h p,padding (write (banks s) cap z y h p)=if supported (banks s) (active s) z then 1 else 0)
    (free : ∀ z y h p,privateGate (write (banks s) cap z y h p)=
      (if EndsPadded (fun e : {i : Fin N // ¬positive i}=>(raw e.val).width) cap y then privateWeight raw positive cap y else 0))
    (planeValue : ∀ z y h p,plane (write (banks s) cap z y h p)=
      TypedWiring.value (decoder (F:=F) (groups:=groups) (ports:=ports) (lanes:=lanes)
        (view:=view) (w:=w) key) (Sum.elim (voltage (banks s) z) p)) :
    (∑ d : (Pin (banks s) cap H (planePort groups ports view))→Bool,(∏i,cut i d)*(padding d*(privateGate d*(plane d*site d)))) =
      ∑ a : (i:Fin N)→Fin (2^(raw i).width),∑ h : H→Bool,
        let z := placed (banks s) (publicLabels key raw positive stage s a)
        let y := freeLabels raw positive cap a
        site (write (banks s) cap z y h (decoded key (voltage (banks s) z))) := by
  let lengths (e : {i : Fin N // ¬positive i}) := (raw e.val).width
  let labels : Fintype (retainedLabels key raw positive stage groups w m) := inferInstance
  let portsEnum : Fintype (PrivatePorts cap) := inferInstance
  let histories : Fintype (H→Bool) := inferInstance
  let planes : Fintype (planePort groups ports view→Bool) := inferInstance
  let siteSum (a : retainedLabels key raw positive stage groups w m) (y : PrivatePorts cap) :=
    sumWith histories (fun h=>site (write (banks s) cap (placed (banks s) a) y h
      (decoded key (voltage (banks s) (placed (banks s) a)))))
  have closed := close_factors (banks s) cap (active s)
    (EndsPadded lengths cap) (privateWeight (F:=F) raw positive cap)
    (fun z=>decoded key (voltage (banks s) z))
    (fun z p=>TypedWiring.value (decoder (F:=F) key) (Sum.elim (voltage (banks s) z) p))
    cut padding privateGate plane site cuts pad free planeValue
    inferInstance labels portsEnum histories planes
    (fun z f=>decoder_sum key (voltage (banks s) z) f planes)
  have regrouped := reported_bonds_fintypes (fun _ : T=>groups) w m key raw positive stage hw
    (fun t=>(s t).unique) cap room cover siteSum labels portsEnum inferInstance
  refine closed.trans (Eq.trans ?_ regrouped)
  apply Finset.sum_congr rfl
  intro a _
  exact guard_choice

end Hierarchy.Tagged.WideStack.Leaf

end
end OAI
