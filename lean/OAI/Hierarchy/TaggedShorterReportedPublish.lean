import OAI.Hierarchy.TaggedShorterPaddedScatter
import OAI.Hierarchy.TaggedShorterEmitMachine
import OAI.Hierarchy.ProtocolRAMReportOrdinal

namespace OAI
/-! # Transfer of native emitted report, prefix, and board words to the shorter call bank -/

noncomputable section
namespace Hierarchy.TaggedShorterReportedPublish
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat Routing CallPool RAM RAM.PhysicalProcedure
open TaggedShorterGroups TaggedShorterScatter TaggedShorterEmitMachine
open ProtocolRAMReportedPorts ProtocolRAMPortRanks
open scoped Classical BigOperators Fin.CommRing

variable {N groups D B M W : ℕ}

def size (rows : Fin N → Row) (w m γ : ℕ) (g : Fin groups) := count rows w m γ g.val

/-- The ordinal directory visits every originally possible row and each of its fixed
transport slots. Zero-width records and the tail of shorter rows use the sink address. -/
def selectPair (rows : Fin N → Row) (w m γ cap : ℕ) (gFit : ∀i,0<pieces rows w i → (rows i).group<groups)
    (distinct : Function.Injective fun i=>(rows i).link) (p : Fin N × Fin cap) :
    Option (Occurrence (size (groups:=groups) rows w m γ)) :=
  let i := p.1
  let z := p.2
  if h : TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ))=γ ∧ z.val<pieces rows w i then
    some ⟨⟨(rows i).group,gFit i (Nat.zero_lt_of_lt h.2)⟩,common rows w m γ (rows i).group distinct
      ⟨⟨i,rfl,h.1⟩,⟨z.val,h.2⟩⟩⟩
  else none

def selectedLive (rows : Fin N → Row) (w m γ cap : ℕ) (gFit : ∀i,0<pieces rows w i → (rows i).group<groups)
    (distinct : Function.Injective fun i=>(rows i).link) (s : Fin (N*cap)) :
    Option (Occurrence (size (groups:=groups) rows w m γ)) :=
  selectPair rows w m γ cap gFit distinct (finProdFinEquiv.symm s)

def selected (rows : Fin N → Row) (w m γ cap : ℕ) (gFit : ∀i,(rows i).group<groups)
    (distinct : Function.Injective fun i=>(rows i).link) (s : Fin (N*cap)) :
    Option (Occurrence (size (groups:=groups) rows w m γ)) :=
  selectedLive rows w m γ cap (fun i _=>gFit i) distinct s

theorem selectedLive_covers (rows : Fin N → Row) (w m γ cap : ℕ) (gFit : ∀i,0<pieces rows w i → (rows i).group<groups)
    (distinct : Function.Injective fun i=>(rows i).link) (fits : ∀i,pieces rows w i≤cap)
    (u : Occurrence (size (groups:=groups) rows w m γ)) :
    ∃ s, selectedLive rows w m γ cap gFit distinct s = some u := by
  obtain ⟨⟨g,hg⟩,v⟩ := u
  obtain ⟨⟨⟨i,groupEq,classEq⟩,z⟩,rfl⟩ := (common rows w m γ g distinct).surjective v
  subst g
  let zz : Fin cap := ⟨z.val,z.isLt.trans_le (fits i)⟩
  refine ⟨finProdFinEquiv (i,zz),?_⟩
  rw [selectedLive,Equiv.symm_apply_apply]
  simp [selectPair,zz,classEq,show z.val<pieces rows w i from z.isLt]

theorem selected_covers (rows : Fin N → Row) (w m γ cap : ℕ) (gFit : ∀i,(rows i).group<groups)
    (distinct : Function.Injective fun i=>(rows i).link) (fits : ∀i,pieces rows w i≤cap)
    (u : Occurrence (size (groups:=groups) rows w m γ)) :
    ∃ s, selected rows w m γ cap gFit distinct s = some u :=
  selectedLive_covers rows w m γ cap (fun i _=>gFit i) distinct fits u

def bases (C D base : ℕ) (i : Fin C) : Fin 5 → Word W :=
  let l := (i.val*2)*D
  let r := (i.val*2+1)*D
  ![(base+i.val:ℕ),(base+C+l:ℕ),(base+C+C*2*D+l:ℕ),(base+C+r:ℕ),(base+C+C*2*D+r:ℕ)]

theorem base_occ (C D base : ℕ) (room : base+(C+2*(C*2*D))≤2^W) (i : Fin C) :
    (bases C D base i) 0 = layout C D base room (.inl i) := by
  apply Fin.ext
  change ((base+i.val:ℕ):Word W).val=base+i.val
  exact Fin.val_cast_of_lt (by have := i.isLt;omega)

private theorem layout_lt (C D base : ℕ) (fit : base+(C+2*(C*2*D))≤2^W)
    (tag side : Bool) (i : Fin C) (x : Fin D) :
    base+C+tag.toNat*(C*2*D)+(i.val*2+side.toNat)*D+x.val<2^W := by
  have small : (i.val*2+side.toNat)*D+x.val < C*2*D := by
    have next : i.val*2+side.toNat+1 ≤ C*2 := by have := i.isLt;cases side <;> simp at *; omega
    have h := Nat.mul_le_mul_right D next
    rw [Nat.add_mul,Nat.one_mul] at h
    have := x.isLt
    omega
  cases tag <;> simp at * <;> omega

theorem base_cell (C D base : ℕ) (room : base+(C+2*(C*2*D))≤2^W)
    (tag side : Bool) (i : Fin C) (x : Fin D) :
    (bases C D base i) (if side then (if tag then 4 else 3) else (if tag then 2 else 1))+
      (x.val:Word W) = layout C D base room (.inr (tag,(i,side),x)) := by
  have bound := layout_lt C D base room tag side i x
  cases tag <;> cases side <;>
    apply Fin.ext <;>
    simp [bases,layout,fieldIndex,finProdFinEquiv_apply_val,finTwoEquiv,
      ← Nat.cast_add,Nat.add_assoc,Nat.mul_comm,Nat.add_comm,Nat.add_left_comm] at * <;>
    exact Nat.mod_eq_of_lt bound

/-- At the installed layout these ten CPU result words are the five physical writes.
The individual endpoint ranks may differ. The identifier is always the common rank modulo B. -/
theorem record_words {G : Type} [Fintype G] (c : G→ℕ) (bound : ∀g,c g≤D) (hb : 0<B)
    (place : ∀g,Bool → Fin (c g) ↪ Fin D) (u : Occurrence c) (base : ℕ)
    (room : let C := capacity G D B M; base+(C+2*(C*2*D))≤2^W)
    (j : Fin 5) (tag : Fin 2) :
    let C := capacity G D B M
    let i := candidate (M:=M) c bound hb u
    let f := liveField (M:=M) c bound hb place u j
    recordWords (bases C D base i) ((place u.1 false u.2).val:Word W)
      ((place u.1 true u.2).val:Word W) ((u.2.val%B:ℕ):Word W) (finProdFinEquiv (j,tag)) =
        (if tag.val=0 then layout C D base room f.1 else (f.2:Word W)) := by
  intro C i f
  have occ := base_occ C D base room i
  have slot := fun t b => base_cell C D base room t b i (place u.1 b u.2)
  fin_cases j <;> fin_cases tag <;>
    first | rfl | exact occ | exact slot false false | exact slot true false |
      exact slot false true | exact slot true true

/-- Address equations for public directories. They are independent of the controller's
selector and of both endpoints of the row. -/
structure Directory (A : Tables) (mem : Memory W) (base : ℕ) (groups D B M : ℕ) : Prop where
  origin : ∀ g : Fin groups,A.groupBase.read mem (g.val:Word W)=
    ((g.val*poolBatchCount D B:ℕ):Word W)
  quotient : ∀ r : Fin D,A.quotient.read mem (r.val:Word W)=((r.val/B:ℕ):Word W)
  remainder : ∀ r : Fin D,A.remainder.read mem (r.val:Word W)=((r.val%B:ℕ):Word W)
  pointers : ∀ (g : Fin groups) (k : Fin (poolBatchCount D B)) (j : Fin 5),
    (A.pointer j).read mem ((g.val*poolBatchCount D B+k.val : ℕ):Word W) =
      (bases (capacity (Fin groups) D B M) D base (board (Fin groups) D B M ⟨g,k⟩)) j

def directory_at (A : Tables) (mem : Memory W) (base : ℕ) (c : Fin groups → ℕ)
    (bound : ∀g,c g≤D) (hb : 0<B) (h : Directory A mem base groups D B M)
    (u : Occurrence c) :
    Addresses A mem u.1.val u.2.val B
      (bases (capacity (Fin groups) D B M) D base (candidate c bound hb u)) := by
  let b := batchAddress B bound (batchIndex hb u.1 u.2)
  let r := Fin.castLE (bound u.1) u.2
  exact ⟨u.1.val*poolBatchCount D B,h.origin u.1,h.quotient r,h.remainder r,
    fun j=>h.pointers u.1 b.2 j⟩

def atWord {R : ℕ} (s : Fin R) (j : Fin 5) (k : Fin 2) : Word W :=
  ((2*(finProdFinEquiv (s,j)).val+k.val:ℕ):Word W)

/-- The selectors and numeric ranks below are precisely those of the native report
and the three native prefix passes. The only scratch destinations of an inactive
original slot are discarded here. -/
theorem selected_words_at_live (A : Tables) (mem : Memory W) (rows : Fin N→Row) (w m γ cap sink base : ℕ)
    (gFit : ∀i,0<pieces rows w i → (rows i).group<groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w m γ g≤D) (hb : 0<B)
    (room : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤2^W)
    (dir : Directory A mem base groups D B M) (small : 10≤2^W) (classFits : γ<2^W)
    (zFit : cap≤2^W) (cr : Fin N → ℕ) (lr : Bool → Fin N → ℕ)
    (cn : ∀ (g : Fin groups) (i : InGroup rows w m γ g.val),cr i.val =
      «prefix» (slotCount rows w m γ g.val) (fun j=>(rows j.val).link) i)
    (pl : ∀ g : Fin groups,Bool → Fin (size rows w m γ g) ↪ Fin D)
    (located : ∀ b (g : Fin groups) (v : ProtocolRAMReportedPorts.Unit rows w m γ g.val),
      (pl g b (common rows w m γ g.val distinct v)).val=lr b v.1.val+v.2.val)
    (s : Fin (N*cap)) (j : Fin 5) (k : Fin 2)
    (source : let i := (finProdFinEquiv.symm s).1
      let z := (finProdFinEquiv.symm s).2
      Source A mem (atWord s j k) i.val z.val (finProdFinEquiv (j,k)).val (rows i).width
        (rows i).group (TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ)))
        (pieces rows w i) (cr i) (lr false i) (lr true i))
    (parity : (BinaryOp.bitAnd.eval (atWord (W:=W) s j k) 1).val=k.val) :
    let C := capacity (Fin groups) D B M
    let c := size (groups:=groups) rows w m γ
    let sel := selectedLive rows w m γ cap gFit distinct
    let es := paddedRecord c bound hb pl (layout C D base room) (sink:Word W) sel (finProdFinEquiv (s,j))
    (term A γ sink).eval mem (atWord s j k) = if k.val=0 then es.1 else es.2 := by
  intro C c sel es
  obtain ⟨⟨i,z⟩,rfl⟩ := finProdFinEquiv.surjective s
  let s := finProdFinEquiv (i,z)
  let actual := TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ))
  have src : Source A mem (atWord s j k) i.val z.val (finProdFinEquiv (j,k)).val (rows i).width
      (rows i).group actual (pieces rows w i) (cr i) (lr false i) (lr true i) := by
    simpa only [Equiv.symm_apply_apply] using source
  have digit : (finProdFinEquiv (j,k)).val%2=k.val := by
    change (k.val+2*j.val)%2=k.val
    simp [Nat.add_mod,Nat.mod_eq_of_lt k.isLt]
  by_cases h : actual=γ ∧ z.val<pieces rows w i
  · let g : Fin groups := ⟨(rows i).group,gFit i (Nat.zero_lt_of_lt h.2)⟩
    let q : InGroup rows w m γ g.val := ⟨i,rfl,h.1⟩
    let v : ProtocolRAMReportedPorts.Unit rows w m γ g.val := ⟨q,⟨z.val,h.2⟩⟩
    let u : Occurrence c := ⟨g,common rows w m γ g.val distinct v⟩
    have chosen : sel s=some u := by
      change selectPair rows w m γ cap gFit distinct (finProdFinEquiv.symm (finProdFinEquiv (i,z)))=some u
      rw [Equiv.symm_apply_apply]
      have cls : TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ))=γ := h.1
      simp [selectPair,cls,h.2,u,g,v,q]
    have name : u.2.val=cr i+z.val := congrArg (·+z.val) (cn g q).symm
    have address (b : Bool) : (pl u.1 b u.2).val=lr b i+z.val :=
      located b g v
    let ptr : Fin 5 → Word W := bases C D base (candidate (M:=M) c bound hb u)
    have dst : Addresses A mem g.val (cr i+z.val) B ptr := by
      rw [←name]
      exact directory_at A mem base c bound hb dir u
    have live := term_live A mem (atWord s j k) i.val z.val (rows i).width g.val γ (pieces rows w i)
      (cr i) (lr false i) (lr true i) B sink (finProdFinEquiv (j,k)) ptr
      (h.1 ▸ src) dst small classFits h.2 (z.isLt.trans_le zFit)
    have packed := record_words c bound hb pl u base room j k
    simp only [address,name] at packed
    exact live.trans (by simpa [es,paddedRecord,chosen,ptr,s] using packed)
  · have absent : ¬ (TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ))=γ ∧ z.val<pieces rows w i) := h
    have empty : sel s=none := by
      change selectPair rows w m γ cap gFit distinct (finProdFinEquiv.symm (finProdFinEquiv (i,z)))=none
      rw [Equiv.symm_apply_apply]
      simp [selectPair,absent]
    have silent := term_idle A mem (atWord s j k) i.val z.val (finProdFinEquiv (j,k)).val
      (rows i).width (rows i).group γ actual (pieces rows w i) (cr i) (lr false i) (lr true i)
      sink src ((not_and_or.mp h).imp_right Nat.le_of_not_gt) classFits (z.isLt.trans_le zFit)
      (by simpa only [digit] using parity)
    simpa [es,paddedRecord,empty,s,digit] using silent

theorem selected_words_at (A : Tables) (mem : Memory W) (rows : Fin N→Row) (w m γ cap sink base : ℕ)
    (gFit : ∀i,(rows i).group<groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w m γ g≤D) (hb : 0<B)
    (room : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤2^W)
    (dir : Directory A mem base groups D B M) (small : 10≤2^W) (classFits : γ<2^W)
    (zFit : cap≤2^W) (cr : Fin N → ℕ) (lr : Bool → Fin N → ℕ)
    (cn : ∀ (g : Fin groups) (i : InGroup rows w m γ g.val),cr i.val =
      «prefix» (slotCount rows w m γ g.val) (fun j=>(rows j.val).link) i)
    (pl : ∀ g : Fin groups,Bool → Fin (size rows w m γ g) ↪ Fin D)
    (located : ∀ b (g : Fin groups) (v : ProtocolRAMReportedPorts.Unit rows w m γ g.val),
      (pl g b (common rows w m γ g.val distinct v)).val=lr b v.1.val+v.2.val)
    (s : Fin (N*cap)) (j : Fin 5) (k : Fin 2)
    (source : let i := (finProdFinEquiv.symm s).1
      let z := (finProdFinEquiv.symm s).2
      Source A mem (atWord s j k) i.val z.val (finProdFinEquiv (j,k)).val (rows i).width
        (rows i).group (TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ)))
        (pieces rows w i) (cr i) (lr false i) (lr true i))
    (parity : (BinaryOp.bitAnd.eval (atWord (W:=W) s j k) 1).val=k.val) :
    let C := capacity (Fin groups) D B M
    let c := size (groups:=groups) rows w m γ
    let sel := selected rows w m γ cap gFit distinct
    let es := paddedRecord c bound hb pl (layout C D base room) (sink:Word W) sel (finProdFinEquiv (s,j))
    (term A γ sink).eval mem (atWord s j k) = if k.val=0 then es.1 else es.2 :=
  selected_words_at_live A mem rows w m γ cap sink base (fun i _=>gFit i) distinct bound hb room
    dir small classFits zFit cr lr cn pl located s j k source parity

theorem selected_words (A : Tables) (mem : Memory W) (rows : Fin N→Row) (w m γ cap sink base : ℕ)
    (gFit : ∀i,(rows i).group<groups) (distinct : Function.Injective fun i=>(rows i).link)
    (bound : ∀g : Fin groups,size rows w m γ g≤D) (hb : 0<B)
    (room : let C := capacity (Fin groups) D B M; base+(C+2*(C*2*D))≤2^W)
    (dir : Directory A mem base groups D B M) (small : 10≤2^W) (classFits : γ<2^W)
    (zFit : cap≤2^W) (cr : Fin N → ℕ) (lr : Bool → Fin N → ℕ)
    (cn : ∀ (g : Fin groups) (i : InGroup rows w m γ g.val),cr i.val =
      «prefix» (slotCount rows w m γ g.val) (fun j=>(rows j.val).link) i)
    (lo : ∀ b (g : Fin groups) (i : InGroup rows w m γ g.val),lr b i.val =
      «prefix» (slotCount rows w m γ g.val) (fun j=>bySite (sideSite rows b) j.val) i)
    (s : Fin (N*cap)) (j : Fin 5) (k : Fin 2)
    (source : let i := (finProdFinEquiv.symm s).1
      let z := (finProdFinEquiv.symm s).2
      Source A mem (atWord s j k) i.val z.val (finProdFinEquiv (j,k)).val (rows i).width
        (rows i).group (TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ)))
        (pieces rows w i) (cr i) (lr false i) (lr true i))
    (parity : (BinaryOp.bitAnd.eval (atWord (W:=W) s j k) 1).val=k.val) :
    let C := capacity (Fin groups) D B M
    let c := size (groups:=groups) rows w m γ
    let pl : ∀g : Fin groups,Bool → Fin (c g) ↪ Fin D := fun g => place rows w m γ g.val distinct (bound g)
    let sel := selected rows w m γ cap gFit distinct
    let es := paddedRecord c bound hb pl (layout C D base room) (sink:Word W) sel (finProdFinEquiv (s,j))
    (term A γ sink).eval mem (atWord s j k) = if k.val=0 then es.1 else es.2 := by
  apply selected_words_at A mem rows w m γ cap sink base gFit distinct bound hb room dir small
    classFits zFit cr lr cn (fun g => place rows w m γ g.val distinct (bound g)) _ s j k source parity
  intro b g v
  exact (read_place rows w m γ g.val distinct (bound g) b v).trans
    (congrArg (·+v.2.val) (lo b g v.1).symm)

/-- The report-word theorem feeds one fixed executable. The native gather overwrites
its private tape and the replay writes only board fields and the single sink. -/
theorem publish_framed {G : Type} [Fintype G] {R n : ℕ} (c : G → ℕ) (bound : ∀g,c g≤D)
    (hb : 0<B) (hw : B≤2^n) (place : ∀g,Bool → Fin (c g) ↪ Fin D)
    (A : Tables) (γ src sink base : ℕ) (select : Fin R → Option (Occurrence c))
    (m : Memory W) (layoutFit : let C := capacity G D B M; base+(C+2*(C*2*D))≤2^W)
    (cover : ∀u,∃s,select s=some u) (inputs : (term A γ sink).Fits W src)
    (tape : src+10*R<2^W)
    (before : base+(capacity G D B M+2*(capacity G D B M*2*D))≤ src) (sinkBefore : sink<src)
    (separate : ∀ f, (sink:Word W)≠layout (capacity G D B M) D base layoutFit f)
    (clear : ∀ f, m (layout (capacity G D B M) D base layoutFit f).val=0)
    (words : ∀ (s : Fin R) (j : Fin 5) (k : Fin 2),
      let e := paddedRecord c bound hb place (layout (capacity G D B M) D base layoutFit)
        (sink:Word W) select (finProdFinEquiv (s,j))
      (term A γ sink).eval m (atWord s j k)=(if k.val=0 then e.1 else e.2)) :
    ∃ out, (procedure W src R γ sink A).Exec m out (8+16230*R) ∧
      (∀ t, t<base → t≠sink → out t=m t) ∧
      ∀ f, out (layout (capacity G D B M) D base layoutFit f).val =
        (contents c bound hb hw place f : Word W) := by
  let C := capacity G D B M
  let addr := layout C D base layoutFit
  let es := paddedTape c bound hb place addr (sink:Word W) select
  let filled := ProtocolRAM.image src (10*R) (term A γ sink) m
  have ln : es.length=R*5 := List.length_ofFn
  have small (f : Field C D) : (addr f).val<src := by
    change base+(fieldIndex C D f).val<src
    have := (fieldIndex C D f).isLt
    have boardEnd : base+(C+2*(C*2*D))≤ src := before
    omega
  have safe : EffectStream.Safe src es := by
    intro av hav
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hav
    obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective k
    cases choose : select s with
    | none => exact Or.inl (by simpa [paddedRecord,choose,Fin.val_cast_of_lt (show sink<2^W by omega)] using sinkBefore)
    | some u => exact Or.inl (by simpa [paddedRecord,choose] using small (liveField c bound hb place u j).1)
  have read : ∀ i : Fin es.length,
      (term A γ sink).eval m ((2*i.val:ℕ):Word W)=(es.get i).1 ∧
      (term A γ sink).eval m ((2*i.val+1:ℕ):Word W)=(es.get i).2 := by
    intro i
    obtain ⟨⟨s,j⟩,hi⟩ := finProdFinEquiv.surjective (Fin.cast ln i)
    have eqn : (finProdFinEquiv (s,j)).val=i.val := congrArg Fin.val hi
    have atIndex : es.get i=paddedRecord c bound hb place addr (sink:Word W) select (finProdFinEquiv (s,j)) := by
      let row := paddedRecord c bound hb place addr (sink:Word W) select
      let i' : Fin (List.ofFn row).length := ⟨i.val,by rw [List.length_ofFn];exact (Fin.cast ln i).isLt⟩
      refine (List.get_ofFn row i').trans (congrArg row ?_)
      exact Fin.ext ((Fin.val_cast _ _).trans eqn.symm)
    rw [atIndex]
    exact ⟨by simpa [atWord,eqn] using words s j 0,by simpa [atWord,eqn] using words s j 1⟩
  have run : (procedure W src R γ sink A).Exec m (after filled (EffectStream.events es))
      ((4+(10*R)*(2*(term A γ sink).work+4))+(4+6*(5*R))) :=
    TaggedShorterEmitMachine.exec A src R γ sink m inputs tape es (by omega) read safe
  have timing : (4+(10*R)*(2*(term A γ sink).work+4))+(4+6*(5*R))=8+16230*R := by
    rw [term_work]
    omega
  rw [timing] at run
  refine ⟨_,run,?_,?_⟩
  · intro t lt ne
    have low : t<src := by omega
    have old : filled t=m t := by simp [filled,ProtocolRAM.image,fillSegment,not_le.mpr low]
    apply EffectStream.after_at es filled t (m t) _ (Or.inl old)
    intro av hav eqn
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hav
    obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective k
    cases chosen : select s with
    | none =>
      have same : sink=t := by simpa [paddedRecord,chosen,Fin.val_cast_of_lt (show sink<2^W by omega)] using eqn
      exact (ne same.symm).elim
    | some u =>
      let f := (liveField (M:=M) c bound hb place u j).1
      have same : (addr f).val=t := by simpa [paddedRecord,chosen,f] using eqn
      change base+(fieldIndex C D f).val=t at same
      omega
  exact padded_reads c bound hb place addr (sink:Word W) hw select cover separate filled
    (fun f => by
      change ProtocolRAM.image src (10*R) (term A γ sink) m (addr f).val=0
      simpa only [ProtocolRAM.image,fillSegment,not_le.mpr (small f),false_and,ite_false] using clear f)

theorem publish {G : Type} [Fintype G] {R n : ℕ} (c : G → ℕ) (bound : ∀g,c g≤D)
    (hb : 0<B) (hw : B≤2^n) (place : ∀g,Bool → Fin (c g) ↪ Fin D)
    (A : Tables) (γ src sink base : ℕ) (select : Fin R → Option (Occurrence c))
    (m : Memory W) (layoutFit : let C := capacity G D B M; base+(C+2*(C*2*D))≤2^W)
    (cover : ∀u,∃s,select s=some u) (inputs : (term A γ sink).Fits W src)
    (tape : src+10*R<2^W)
    (before : base+(capacity G D B M+2*(capacity G D B M*2*D))≤ src) (sinkBefore : sink<src)
    (separate : ∀ f, (sink:Word W)≠layout (capacity G D B M) D base layoutFit f)
    (clear : ∀ f, m (layout (capacity G D B M) D base layoutFit f).val=0)
    (words : ∀ (s : Fin R) (j : Fin 5) (k : Fin 2),
      let e := paddedRecord c bound hb place (layout (capacity G D B M) D base layoutFit)
        (sink:Word W) select (finProdFinEquiv (s,j))
      (term A γ sink).eval m (atWord s j k)=(if k.val=0 then e.1 else e.2)) :
    ∃ out, (procedure W src R γ sink A).Exec m out (8+16230*R) ∧
      ∀ f, out (layout (capacity G D B M) D base layoutFit f).val =
        (contents c bound hb hw place f : Word W) := by
  obtain ⟨out,run,_,read⟩ := publish_framed c bound hb hw place A γ src sink base select m layoutFit cover inputs tape before sinkBefore separate clear words
  exact ⟨out,run,read⟩

def clearedProcedure (W board fields src R γ sink : ℕ) (A : Tables) : Procedure W :=
  (ProtocolRAM.scan W board fields (.lit 0)).seq (procedure W src R γ sink A)

private theorem clearScansCheap (W base n src rows count : ℕ) (e : ProtocolRAM.Expr) :
    ProtocolRAM.CheapCode ((ProtocolRAM.scan W base n (.lit 0)).seq
      ((ProtocolRAM.scan W src rows e).seq (EffectSeed.scatter W src count))) :=
  @ProtocolRAM.cheap_seq W (ProtocolRAM.scan W base n (.lit 0))
    ((ProtocolRAM.scan W src rows e).seq (EffectSeed.scatter W src count))
    (ProtocolRAM.scan_cheap W base n (.lit 0)) (scanReplay_cheap W src rows count e)

theorem clearedProcedure_cheap (W board fields src R γ sink : ℕ) (A : Tables) :
    ProtocolRAM.CheapCode (clearedProcedure W board fields src R γ sink A) :=
  @clearScansCheap W board fields src (10*R) (5*R) (term A γ sink)

theorem clearedProcedure_size (W board fields src R γ sink : ℕ) (A : Tables) :
    let p := clearedProcedure W board fields src R γ sink A
    p.labels=2450 ∧ p.registers=822 ∧ p.slots=2 := by
  obtain ⟨el,er,es⟩ := procedure_size A W src R γ sink
  obtain ⟨cl,cr,cs⟩ := ProtocolRAM.scan_size W board fields (.lit 0)
  change _+_=2450 ∧ _+_=822 ∧ _+_=2
  simp [cl,cr,cs,el,er,es,ProtocolRAM.Expr.work]

/-- Clear a fresh dense physical board with native writes before replay. A frame below the
board preserves every rank, advice read, and emitted descriptor consumed by the publisher. -/
theorem publish_cleared_framed_stored {G : Type} [Fintype G] {R n : ℕ} (c : G → ℕ) (bound : ∀g,c g≤D)
    (hb : 0<B) (hw : B≤2^n) (place : ∀g,Bool → Fin (c g) ↪ Fin D)
    (A : Tables) (γ src sink base : ℕ) (choose : Fin R → Option (Occurrence c))
    (m : Memory W) (layoutFit : let C := capacity G D B M; base+(C+2*(C*2*D))≤2^W)
    (cover : ∀u,∃s,choose s=some u) (inputs : (term A γ sink).Fits W src)
    (low : (term A γ sink).Fits W base) (tape : src+10*R<2^W)
    (before : base+(capacity G D B M+2*(capacity G D B M*2*D))≤ src) (sinkBefore : sink<src)
    (separate : ∀ f, (sink:Word W)≠layout (capacity G D B M) D base layoutFit f)
    (_one : 1<2^W) (_batchFits : B≤2^W)
    (words : ∀ (s : Fin R) (j : Fin 5) (k : Fin 2),
      let e := paddedRecord c bound hb place (layout (capacity G D B M) D base layoutFit)
        (sink:Word W) choose (finProdFinEquiv (s,j))
      (term A γ sink).eval m (atWord s j k)=(if k.val=0 then e.1 else e.2)) :
    let C := capacity G D B M
    let fields := C+2*(C*2*D)
    let addr := layout C D base layoutFit
    ∃ out, (clearedProcedure W base fields src R γ sink A).Exec m out
      ((4+6*fields)+(8+16230*R)) ∧
      (∀ a, a<base → a≠sink → out a=m a) ∧
      ∀ f, out (addr f).val=(contents c bound hb hw place f : Word W) := by
  intro C fields addr
  let erased := ProtocolRAM.image base fields (.lit 0) m
  have small : base+fields<2^W := by
    have hi : base+fields≤ src := before
    omega
  have run : (ProtocolRAM.scan W base fields (.lit 0)).Exec m erased (4+6*fields) := by
    have time : 4+fields*(2*ProtocolRAM.Expr.work (.lit 0)+4)=4+6*fields := by
      simp [ProtocolRAM.Expr.work,Nat.mul_comm]
    rw [←time]
    intro P X K machine pc reg pub exit installed publicData cfg raw start eq
    exact ProtocolRAM.scan_exec base fields (.lit 0) m trivial small machine pc reg pub exit installed publicData cfg raw start eq
  have same t (h : t<base) : erased t=m t := by
    simp [erased,ProtocolRAM.image,fillSegment,not_le.mpr h]
  have zero (f : Field C D) : erased (addr f).val=0 := by
    change erased (base+(fieldIndex C D f).val)=0
    have h := (fieldIndex C D f).isLt
    simp [erased,ProtocolRAM.image,fillSegment,fields,ProtocolRAM.Expr.eval,h]
  have eqv s j k := ProtocolRAM.eval_below (term A γ sink) (atWord (R:=R) s j k) m erased low same
  obtain ⟨out,exec,frame,read⟩ := publish_framed c bound hb hw place A γ src sink base choose erased layoutFit
    cover inputs tape before sinkBefore separate zero (fun s j k=>(eqv s j k).trans (words s j k))
  refine ⟨out,?_,fun a h ne => (frame a h ne).trans (same a h),read⟩
  intro P R' K M pc reg pub exit installed publicData cfg mem start eq
  exact Procedure.Exec.then run exec M pc reg pub exit installed publicData cfg mem start eq

theorem publish_cleared_framed {G : Type} [Fintype G] {R n : ℕ} (c : G → ℕ) (bound : ∀g,c g≤D)
    (hb : 0<B) (hw : B≤2^n) (place : ∀g,Bool → Fin (c g) ↪ Fin D)
    (A : Tables) (γ src sink base : ℕ) (choose : Fin R → Option (Occurrence c))
    (m : Memory W) (layoutFit : let C := capacity G D B M; base+(C+2*(C*2*D))≤2^W)
    (cover : ∀u,∃s,choose s=some u) (inputs : (term A γ sink).Fits W src)
    (low : (term A γ sink).Fits W base) (tape : src+10*R<2^W)
    (before : base+(capacity G D B M+2*(capacity G D B M*2*D))≤ src) (sinkBefore : sink<src)
    (separate : ∀ f, (sink:Word W)≠layout (capacity G D B M) D base layoutFit f)
    (one : 1<2^W) (batchFits : B≤2^W)
    (words : ∀ (s : Fin R) (j : Fin 5) (k : Fin 2),
      let e := paddedRecord c bound hb place (layout (capacity G D B M) D base layoutFit)
        (sink:Word W) choose (finProdFinEquiv (s,j))
      (term A γ sink).eval m (atWord s j k)=(if k.val=0 then e.1 else e.2)) :
    let C := capacity G D B M
    let fields := C+2*(C*2*D)
    let addr := layout C D base layoutFit
    ∃ out, (clearedProcedure W base fields src R γ sink A).Exec m out
      ((4+6*fields)+(8+16230*R)) ∧
      (∀ a, a<base → a≠sink → out a=m a) ∧
      (∀ i,decide ((out (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
      (∀ sb x,decide ((out (addr (.inr (false,sb,x))).val).val≠0)=groupMask c bound B M place sb x) ∧
      (∀ sb x,wordBits n (((out (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
        groupID c bound M hb hw place sb x) := by
  intro C fields addr
  obtain ⟨out,run,frame,stored⟩ := publish_cleared_framed_stored c bound hb hw place A γ src sink base choose
    m layoutFit cover inputs low tape before sinkBefore separate one batchFits words
  exact ⟨out,run,frame,decode_words c bound hb hw place addr out one batchFits stored⟩

theorem publish_cleared {G : Type} [Fintype G] {R n : ℕ} (c : G → ℕ) (bound : ∀g,c g≤D)
    (hb : 0<B) (hw : B≤2^n) (place : ∀g,Bool → Fin (c g) ↪ Fin D)
    (A : Tables) (γ src sink base : ℕ) (choose : Fin R → Option (Occurrence c))
    (m : Memory W) (layoutFit : let C := capacity G D B M; base+(C+2*(C*2*D))≤2^W)
    (cover : ∀u,∃s,choose s=some u) (inputs : (term A γ sink).Fits W src)
    (low : (term A γ sink).Fits W base) (tape : src+10*R<2^W)
    (before : base+(capacity G D B M+2*(capacity G D B M*2*D))≤ src) (sinkBefore : sink<src)
    (separate : ∀ f, (sink:Word W)≠layout (capacity G D B M) D base layoutFit f)
    (one : 1<2^W) (batchFits : B≤2^W)
    (words : ∀ (s : Fin R) (j : Fin 5) (k : Fin 2),
      let e := paddedRecord c bound hb place (layout (capacity G D B M) D base layoutFit)
        (sink:Word W) choose (finProdFinEquiv (s,j))
      (term A γ sink).eval m (atWord s j k)=(if k.val=0 then e.1 else e.2)) :
    let C := capacity G D B M
    let fields := C+2*(C*2*D)
    let addr := layout C D base layoutFit
    ∃ out, (clearedProcedure W base fields src R γ sink A).Exec m out
      ((4+6*fields)+(8+16230*R)) ∧
      (∀ i,decide ((out (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
      (∀ sb x,decide ((out (addr (.inr (false,sb,x))).val).val≠0)=groupMask c bound B M place sb x) ∧
      (∀ sb x,wordBits n (((out (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
        groupID c bound M hb hw place sb x) := by
  obtain ⟨out,run,_,read⟩ := publish_cleared_framed c bound hb hw place A γ src sink base choose m layoutFit cover inputs low tape before sinkBefore separate one batchFits words
  exact ⟨out,run,read⟩

end Hierarchy.TaggedShorterReportedPublish

end
end OAI
