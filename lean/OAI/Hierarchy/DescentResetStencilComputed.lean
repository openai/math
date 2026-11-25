import OAI.Hierarchy.DescentResetStencilLayout

namespace OAI
/-! # Complete packing and execution of the reset stencil from its native primitive words -/
namespace Hierarchy.DescentPlainTerminal.Suffix.Stencil
open DescentColonies DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image DescentPacking.PackedMatch.Local
open DescentGL DescentColonies DescentPackedColony DescentPackedColony.Phase DescentIssuedFallbackPanel
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w out : ℕ} (C : ReaderTables.Chart) {q : ℕ}

structure Operands (P : Inputs C.m C.c q) (w : ℕ) : Prop where
  header : ∀j,(P.header j).Fits w C.origin
  ports : ∀j s,(P.portHeader j s).Fits w C.origin
  weights : P.weights.Fits w C.origin
  flows : ∀j,(P.flows j).Fits w C.origin
  splits : P.splits.Fits w C.origin
  planes : ∀d,(P.planes d).Fits w C.origin

def lastChart (q t : ℕ) : Layout.Chart:=⟨C.stop,C.r,q,C.n,t,C.H,2^C.c,C.M⟩

def reader (w : ℕ) := (C.image (w:=w)).program.seq C.planes.program
def setup (q t f B Y w : ℕ) :=
  let S:=lastChart C q t
  (reader C w).seq ((S.gathers (w:=w)).program.seq (S.literals f B Y).program)

def program (P : Inputs C.m C.c q) (t f B Y w : ℕ) :=
  let S:=lastChart C q t
  (setup C q t f B Y w).seq (execute S.tabs (C.inputs P).field S.banks S.out C.H (2^C.c) C.M w)

def time (P : Inputs C.m C.c q) (t : ℕ) :=
  let S:=lastChart C q t
  (8+10*(C.stop-C.origin))+(8+10*(S.scratch-S.base))+cost S.tabs (C.inputs P).field C.H (2^C.c) C.M

theorem fields_fit (P : Inputs C.m C.c q) (ops : Operands C P w)
    (old : C.origin≤out) (mem : Memory w) (rom : ReadersROM (C.inputs P) C.n C.b C.M C.H w out mem) :
    ∀j,((C.inputs P).field j).Fits w out := by
  have mono (e:Expr) := ProtocolRAMGeneratedWrite.fits_mono (w:=w) e old
  intro j
  rcases j with s|((x|⟨d,x⟩)|(⟨i,x⟩|⟨j,s⟩))
  · exact ⟨⟨rom.repeatFit,mono _ (ops.header s)⟩,rom.maskFit,trivial⟩
  · exact ⟨(rom.amounts x).1,mono _ ops.weights⟩
  · exact ⟨(rom.votes d x).1,mono _ ops.splits⟩
  · exact ⟨(rom.comparisons i x).1,Gather.fits _ _ _ rom.gather (List.finRange C.m)⟩
  · cases s with
    | inl z=>exact ⟨⟨rom.repeatFit,mono _ (ops.ports j z)⟩,rom.maskFit,trivial⟩
    | inr x=>exact ⟨(rom.amounts x).1,mono _ (ops.flows j)⟩

theorem compute_packed (P : Inputs C.m C.c q) (t f B Y : ℕ) (mem : Memory w)
    (small : C.c≤C.m) (basis : DescentGL.Layout C.m)
    (head : Fin C.H→Fin 3→Cell C.n) (port : Fin C.H→Fin q→Fin 2→Cell C.n)
    (weight : Fin C.H→Block C.c→Block C.r→ℕ) (flow : Fin q→Fin C.H→Block C.c→Block C.r→ℕ)
    (rows : Block C.c→Scan.Buffer (Fin C.H) C.r) (pos : 0<C.M)
    (short : C.M*max (C.n*count C.r q) (t*2^C.r)≤w/2) (word : C.n*C.M≤w)
    (room : (lastChart C q t).endAddress<2^w) (ops : Operands C P w)
    (headWords : ∀j (p : Row C.H (2^C.c) C.M),(P.header j).eval mem ((DescentSIMDLookup.row C.H (2^C.c) C.M p).val:Word w)=(head p.1 j).val)
    (portWords : ∀j s (p : Row C.H (2^C.c) C.M),(P.portHeader j s).eval mem ((DescentSIMDLookup.row C.H (2^C.c) C.M p).val:Word w)=(port p.1 j s).val)
    (smallWeight : ∀v hi x,weight v hi x<2^C.b) (smallFlow : ∀j v hi x,flow j v hi x<2^C.b)
    (weights : Source P.weights (fun v hi=>DescentPackedColony.counts C.b (weight v hi)) C.M mem)
    (flows : ∀j,Source (P.flows j) (fun v hi=>DescentPackedColony.counts C.b (flow j v hi)) C.M mem)
    (splitWords : Source P.splits (fun v hi=>cache (rows hi) v) C.M mem)
    (planes : ∀d,Source (P.planes d) (fun (_ : Fin C.H) hi=>PackedOrder.panel small basis hi d) C.M mem) :
    let S:=lastChart C q t
    ∃dst,(program C P t f B Y w).Exec mem dst (time C P t) ∧
      (∀v hi x,digit t x.val (digit (t*2^C.r) (lane hi pos).val
        (dst (S.out+(DescentSIMDLookup.row C.H (2^C.c) C.M (position v hi pos)).val)).val)=
        ((Stencil.word (physical small basis head port weight flow rows v hi) f B Y x:ℕ):Cell t).val) ∧
      (∀a<C.origin,dst a=mem a) ∧ (∀a,S.endAddress≤a→dst a=mem a) ∧
      (∀i x : Block C.r, (((C.inputs P).field (.inr (.inr (.inl (i,x))))).Fits w S.endAddress) ∧
        Source ((C.inputs P).field (.inr (.inr (.inl (i,x)))))
        (fun (_:Fin C.H) (hi:Block C.c)=>if (rearrange basis).symm (join small hi i)<(rearrange basis).symm (join small hi x)
          then (1:Cell C.n) else 0) C.M dst) ∧
      ∀p : Row C.H (2^C.c) C.M,dst (S.out+(DescentSIMDLookup.row _ _ _ p).val)=
        ((data (fun v hi=>encode t (2^C.r) (fun x=>(Stencil.word (physical small basis head port weight flow rows v hi) f B Y x:Cell t))) p).val:Word w) := by
  let S:=lastChart C q t
  have before:=C.before_planes.trans C.plane_le
  have floor:C.stop≤S.scratch:=by
    change S.base≤S.scratch
    exact ((Nat.le_add_right S.base _).trans (Nat.le_add_right S.table _)).trans (Nat.le_add_right S.mask _)
  have inside:C.stop<2^w:=by change S.endAddress<2^w at room;dsimp [Layout.Chart.endAddress,Layout.Chart.out] at room;omega
  let mm:=(C.planes (w:=w)).output (C.image.output mem)
  obtain ⟨install,rom,keep,_⟩:=C.issue_readers P C.stop mem le_rfl inside word
    (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ before (ops.planes j))
  have old (e:Expr) (p:Word w) (fit:e.Fits w C.origin) :=
    eval_below e p mem mm fit (fun z hz=>keep z (Or.inl hz))
  have fields:=source_slots small basis (C.inputs P) head port weight flow rows C.stop mm rom
    (fun j p=>(old _ _ (ops.header j)).trans (headWords j p))
    (fun j s p=>(old _ _ (ops.ports j s)).trans (portWords j s p)) smallWeight smallFlow
    (fun p=>(old _ _ ops.weights).trans (weights p))
    (fun j p=>(old _ _ (ops.flows j)).trans (flows j p))
    (fun p=>(old _ _ ops.splits).trans (splitWords p))
    (fun j p=>(old _ _ (ops.planes j)).trans (planes j p))
  let after:=(S.literals (w:=w) f B Y).output (S.gathers.output mm)
  obtain ⟨mount,tabs,lookup,kept,_⟩:=S.issued f B Y mm room
  have live:=fields_fit C P ops before mm rom
  have supplied (s : Slot C.r q) : Source ((C.inputs P).field s)
      (fun v hi=>physical small basis head port weight flow rows v hi s) C.M after :=
    fun p=>(eval_below _ _ mm after (live s) (fun z hz=>kept z (Or.inl hz))).trans (fields s p)
  obtain ⟨fit,dataRoom,dictionary,mask⟩:=S.fit room short
  obtain ⟨dst,run,found,low,high,allWords⟩:=returned_words C.r q C.n t f B Y S.tabs (C.inputs P).field S.banks S.out after _
    pos fit (S.gather_bounds _ (fun s=>ProtocolRAMGeneratedWrite.fits_mono _ floor (live s)) room) dataRoom
    tabs supplied lookup dictionary mask
  refine ⟨dst,@Procedure.Exec.then w _ _ mem after dst _ _
    (@Procedure.Exec.then w _ _ mem mm after _ _ (@install) (@mount)) (@run),found,?_,?_,?_,allWords⟩
  · intro a ha
    exact (low a (ha.trans_le (before.trans floor))).trans ((kept a (Or.inl (ha.trans_le before))).trans (keep a (Or.inl ha)))
  · intro a ha
    have land:S.scratch≤S.endAddress:=by dsimp [Layout.Chart.endAddress,Layout.Chart.out];omega
    exact (high a ha).trans ((kept a (Or.inr (land.trans ha))).trans (keep a (Or.inr (floor.trans (land.trans ha)))))
  · intro i x
    let s : Slot C.r q:=.inr (.inr (.inl (i,x)))
    have land:S.scratch≤S.endAddress:=by dsimp [Layout.Chart.endAddress,Layout.Chart.out];omega
    refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ (floor.trans land) (live s),?_⟩
    intro p
    have same:=eval_below ((C.inputs P).field s)
      ((DescentSIMDLookup.row C.H (2^C.c) C.M p).val : Word w) after dst
      (ProtocolRAMGeneratedWrite.fits_mono _ floor (live s)) low
    exact same.trans (supplied s p)

theorem compute (P : Inputs C.m C.c q) (t f B Y : ℕ) (mem : Memory w)
    (small : C.c≤C.m) (basis : DescentGL.Layout C.m)
    (head : Fin C.H→Fin 3→Cell C.n) (port : Fin C.H→Fin q→Fin 2→Cell C.n)
    (weight : Fin C.H→Block C.c→Block C.r→ℕ) (flow : Fin q→Fin C.H→Block C.c→Block C.r→ℕ)
    (rows : Block C.c→Scan.Buffer (Fin C.H) C.r) (pos : 0<C.M)
    (short : C.M*max (C.n*count C.r q) (t*2^C.r)≤w/2) (word : C.n*C.M≤w)
    (room : (lastChart C q t).endAddress<2^w) (ops : Operands C P w)
    (headWords : ∀j (p : Row C.H (2^C.c) C.M),(P.header j).eval mem ((DescentSIMDLookup.row C.H (2^C.c) C.M p).val:Word w)=(head p.1 j).val)
    (portWords : ∀j s (p : Row C.H (2^C.c) C.M),(P.portHeader j s).eval mem ((DescentSIMDLookup.row C.H (2^C.c) C.M p).val:Word w)=(port p.1 j s).val)
    (smallWeight : ∀v hi x,weight v hi x<2^C.b) (smallFlow : ∀j v hi x,flow j v hi x<2^C.b)
    (weights : Source P.weights (fun v hi=>DescentPackedColony.counts C.b (weight v hi)) C.M mem)
    (flows : ∀j,Source (P.flows j) (fun v hi=>DescentPackedColony.counts C.b (flow j v hi)) C.M mem)
    (splitWords : Source P.splits (fun v hi=>cache (rows hi) v) C.M mem)
    (planes : ∀d,Source (P.planes d) (fun (_ : Fin C.H) hi=>PackedOrder.panel small basis hi d) C.M mem) :
    let S:=lastChart C q t
    ∃dst,(program C P t f B Y w).Exec mem dst (time C P t) ∧
      (∀v hi x,digit t x.val (digit (t*2^C.r) (lane hi pos).val
        (dst (S.out+(DescentSIMDLookup.row C.H (2^C.c) C.M (position v hi pos)).val)).val)=
        ((Stencil.word (physical small basis head port weight flow rows v hi) f B Y x:ℕ):Cell t).val) ∧
      (∀a<C.origin,dst a=mem a) ∧ ∀a,S.endAddress≤a→dst a=mem a := by
  obtain ⟨dst,exe,read,lo,hi,_⟩:=compute_packed C P t f B Y mem small basis head port weight flow rows pos short word room ops
    headWords portWords smallWeight smallFlow weights flows splitWords planes
  exact ⟨dst,exe,read,lo,hi⟩

end
end Hierarchy.DescentPlainTerminal.Suffix.Stencil

end OAI
