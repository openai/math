import OAI.Hierarchy.TaggedShorterSlotWidthNative
import OAI.Hierarchy.TaggedShorterReportAdvice

namespace OAI
/-! # Original selected report widths published at the installed data ports -/

noncomputable section
namespace Hierarchy.TaggedShorterSlotWidth
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat RAM RAM.DescriptorExpr RAM.PhysicalProcedure
open ProtocolRAM ProtocolRAMReportedPorts TaggedShorterReportedPublish TaggedShorterReportAdvice
open TaggedShorterEmitMachine TaggedShorterScatter
open scoped Classical Fin.CommRing
variable {N groups D W : ℕ}

/-- The additional address directory is public and occupies one word per group. -/
def originStore (rom groups base D : ℕ) (source : Memory W) : Memory W :=
  fillSegment rom groups (fun a=>((base+2*(a-rom)*D : ℕ):Word W)) source

theorem originStore_frame (rom groups base D : ℕ) (source : Memory W) (a : ℕ)
    (away : a<rom ∨ rom+groups≤a) : originStore rom groups base D source a=source a := by
  simp [originStore,fillSegment,show ¬(rom≤a ∧ a<rom+groups) by omega]

theorem originStore_read (rom bits base D : ℕ) (source : Memory W) (small : groups≤2^bits)
    (wide : groups≤2^W) (g : Fin groups) :
    (⟨rom,bits⟩ : Bank).read (originStore rom groups base D source) (g.val:Word W)=
      ((base+2*g.val*D : ℕ):Word W) := by
  change originStore rom groups base D source (rom+(g.val:Word W).val%2^bits)=_
  rw [Fin.val_cast_of_lt (g.isLt.trans_le wide),Nat.mod_eq_of_lt (g.isLt.trans_le small)]
  simp [originStore,fillSegment,g.isLt]

/-- The common ordinal identifies the exact originally reported row whose immutable
width is copied. Multiple transport pieces of one report have the same raw width. -/
def reportWidth (rows : Fin N→Row) (w menu γ : ℕ)
    (distinct : Function.Injective fun i=>(rows i).link)
    (u : Occurrence (size (groups:=groups) rows w menu γ)) : ℕ :=
  (rows ((common rows w menu γ u.1.val distinct).symm u.2).1.val).width

theorem reported_live (rows : Fin N→Row) (w menu γ : ℕ)
    (distinct : Function.Injective fun i=>(rows i).link)
    (pl : ∀g : Fin groups,Bool → Fin (size rows w menu γ g) ↪ Fin D) (g : Fin groups)
    (b : Bool) (u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val) :
    value pl (reportWidth rows w menu γ distinct) (g,b,pl g b (common rows w menu γ g.val distinct u)) =
      (rows u.1.val).width := by
  rw [value_live pl _ (⟨g,common rows w menu γ g.val distinct u⟩ : Occurrence _) b]
  simp [reportWidth]

theorem publish_report_at_live {B M board w menu cap rom bits base src sink γ : ℕ}
    (mem : Memory W) (rows : Fin N→Row)
    (width group rank left right origins : Bank) (cr : Fin N→ℕ) (lr : Bool → Fin N→ℕ)
    (dyn : Dynamic rows mem width group rank left right cr lr)
    (pub : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M board w menu cap j x)
    (origin : ∀g : Fin groups,origins.read mem (g.val:Word W)=((base+2*g.val*D : ℕ):Word W))
    (gFit : ∀i,0<pieces rows w i → (rows i).group<groups) (distinct : Function.Injective fun i=>(rows i).link)
    (copied : ∀i,pieces rows w i≤cap)
    (pl : ∀g : Fin groups,Bool → Fin (size rows w menu γ g) ↪ Fin D)
    (located : ∀ b (g : Fin groups) (u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val),
      (pl g b (common rows w menu γ g.val distinct u)).val=lr b u.1.val+u.2.val)
    (tableCap : 10*(N*cap)≤2^bits) (widthFit : ∀i,(rows i).width<2^bits) (wide : 2^bits≤2^W)
    (menuFits : menu<2^W) (typeFits : γ ≤ menu) (small : 2<2^W) (slotFits : cap<2^W)
    (ordered : base+2*groups*D≤ src) (room : src+10*(N*cap)<2^W) (sinkLow : sink<src)
    (apart : ∀x : Slot groups D,sink≠index base x)
    (input : (term (tables rom bits width group rank left right) origins D γ sink).Fits W src)
    (low : (term (tables rom bits width group rank left right) origins D γ sink).Fits W base) :
    let A := tables rom bits width group rank left right
    ∃ out, (procedure W base groups D src (N*cap) γ sink A origins).Exec mem out
        ((4+6*(2*groups*D))+(8+4130*(N*cap))) ∧
      (∀x : Slot groups D,out (index base x)=(value pl (reportWidth rows w menu γ distinct) x:Word W)) ∧
      ∀t, (t<base ∨ base+2*groups*D≤t) → (t<src ∨ src+10*(N*cap)≤t) → t≠sink → out t=mem t := by
  intro A
  let choose := selectedLive rows w menu γ cap gFit distinct
  let raw := reportWidth (groups:=groups) rows w menu γ distinct
  apply exec pl raw choose (selectedLive_covers rows w menu γ cap gFit distinct copied) mem A origins
    base src γ sink ordered room sinkLow apart input low
  intro s j k
  obtain ⟨⟨i,z⟩,rfl⟩ := finProdFinEquiv.surjective s
  let s := finProdFinEquiv (i,z)
  let actual := TaggedShorterBudget.widthIndex menu ((rows i).width/(w:ℝ))
  have inputs : Source A mem (atWord s j k) i.val z.val (finProdFinEquiv (j,k)).val (rows i).width
      (rows i).group actual (pieces rows w i) (cr i) (lr false i) (lr true i) := by
    simpa only [s,Equiv.symm_apply_apply] using source mem rows width group rank left right cr lr dyn pub
      tableCap widthFit wide menuFits (fun i=>(copied i).trans_lt slotFits) s j k
  have semantics := term_read A origins D γ sink base i.val z.val (rows i).width (rows i).group actual
    (pieces rows w i) (cr i) (lr false i) (lr true i) mem (atWord s j k) j k inputs
    (fun h => origin ⟨(rows i).group,gFit i (Nat.zero_lt_of_lt h.2)⟩) (typeFits.trans_lt menuFits) (z.isLt.trans slotFits) small
    (ordinal (W:=W) s j k (tableCap.trans wide)).2.2.2
  by_cases on : actual=γ ∧ z.val<pieces rows w i
  · let g : Fin groups := ⟨(rows i).group,gFit i (Nat.zero_lt_of_lt on.2)⟩
    let u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val := ⟨⟨i,rfl,on.1⟩,⟨z.val,on.2⟩⟩
    let o : Occurrence (size (groups:=groups) rows w menu γ) := ⟨g,common rows w menu γ g.val distinct u⟩
    have live : TaggedShorterBudget.widthIndex menu ((rows i).width/(w:ℝ))=γ ∧ z.val<pieces rows w i := on
    have chosen : choose s=some o := by
      simp only [choose,s,selectedLive,Equiv.symm_apply_apply]
      simp [selectPair,live,o,u,g]
    have equal : raw o=(rows i).width := by simp [raw,reportWidth,o,u]
    have loc := located (side j) g u
    have atSide : (if side j then lr true i else lr false i)=lr (side j) i := by cases side j <;> rfl
    simp only [ite_eq_left on,atSide] at semantics
    change choose (finProdFinEquiv (i,z))=some o at chosen
    simp only [record,Equiv.symm_apply_apply,chosen]
    change (term A origins D γ sink).eval mem (atWord s j k)=if k.val=0 then
      ((slotAddress base D (rows i).group (side j) (pl g (side j) (common rows w menu γ g.val distinct u)).val:ℕ):Word W)
      else (raw o:Word W)
    rw [equal,loc]
    exact semantics
  · have absent : ¬ (TaggedShorterBudget.widthIndex menu ((rows i).width/(w:ℝ))=γ ∧ z.val<pieces rows w i) := on
    have chosen : choose s=none := by
      simp only [choose,s,selectedLive,Equiv.symm_apply_apply]
      simp [selectPair,absent]
    change choose (finProdFinEquiv (i,z))=none at chosen
    simp only [record,Equiv.symm_apply_apply,chosen]
    change (term A origins D γ sink).eval mem (atWord s j k)=(if k.val=0 then (sink:Word W) else 0)
    rw [ite_eq_right on] at semantics
    exact semantics

theorem publish_report_at {B M board w menu cap rom bits base src sink γ : ℕ}
    (mem : Memory W) (rows : Fin N→Row)
    (width group rank left right origins : Bank) (cr : Fin N→ℕ) (lr : Bool → Fin N→ℕ)
    (dyn : Dynamic rows mem width group rank left right cr lr)
    (pub : ∀ j : Fin 13,∀ x : ℕ,x<2^bits → (bank rom bits j).read mem (x:Word W)=
      words groups D B M board w menu cap j x)
    (origin : ∀g : Fin groups,origins.read mem (g.val:Word W)=((base+2*g.val*D : ℕ):Word W))
    (gFit : ∀i,(rows i).group<groups) (distinct : Function.Injective fun i=>(rows i).link)
    (copied : ∀i,pieces rows w i≤cap)
    (pl : ∀g : Fin groups,Bool → Fin (size rows w menu γ g) ↪ Fin D)
    (located : ∀ b (g : Fin groups) (u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val),
      (pl g b (common rows w menu γ g.val distinct u)).val=lr b u.1.val+u.2.val)
    (tableCap : 10*(N*cap)≤2^bits) (widthFit : ∀i,(rows i).width<2^bits) (wide : 2^bits≤2^W)
    (menuFits : menu<2^W) (typeFits : γ ≤ menu) (small : 2<2^W) (slotFits : cap<2^W)
    (ordered : base+2*groups*D≤ src) (room : src+10*(N*cap)<2^W) (sinkLow : sink<src)
    (apart : ∀x : Slot groups D,sink≠index base x)
    (input : (term (tables rom bits width group rank left right) origins D γ sink).Fits W src)
    (low : (term (tables rom bits width group rank left right) origins D γ sink).Fits W base) :
    let A := tables rom bits width group rank left right
    ∃ out, (procedure W base groups D src (N*cap) γ sink A origins).Exec mem out
        ((4+6*(2*groups*D))+(8+4130*(N*cap))) ∧
      (∀x : Slot groups D,out (index base x)=(value pl (reportWidth rows w menu γ distinct) x:Word W)) ∧
      ∀t, (t<base ∨ base+2*groups*D≤t) → (t<src ∨ src+10*(N*cap)≤t) → t≠sink → out t=mem t :=
  publish_report_at_live mem rows width group rank left right origins cr lr dyn pub origin
    (fun i _=>gFit i) distinct copied pl located tableCap widthFit wide menuFits typeFits small slotFits
    ordered room sinkLow apart input low

end Hierarchy.TaggedShorterSlotWidth

end
end OAI
