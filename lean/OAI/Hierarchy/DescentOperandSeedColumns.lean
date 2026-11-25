import OAI.Hierarchy.DescentSeedOperandStamp
import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentOperandSeedPublication
import OAI.Hierarchy.DescentOperandColumnProgram
import OAI.Hierarchy.DescentSeedSignedBroadcast

namespace OAI
/-! # Physically issuing all seven fields of the original stamped seed operand -/
namespace Hierarchy.DescentOperandStateBanks.Seed.Columns
open DescentPackedSeed DescentSeedRoot DescentInitialHost DescentKernelHistory DescentColonies DescentSIMDLookup
open DescentSeedSignedBroadcast DescentDyadicSpan DescentPackedColony
open Computability.BorderVNP.Crossing DescentSixParty ThreeFlat Routing Catalyst Diagonal
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F J : Type} [_root_.Field F] [Fintype J] [DecidableEq J] {k n G d R s w M b : ℕ}
  (X : Approximation F k n) (name : J≃Fin G) (digits : Fin R≃J×Block d)

def order (N : ℕ) : ((Vertex X ×Fin 3)×(Fin N×Field)) ≃ Fin (count X*(N*7)) :=
  ((Seed.order X).prodCongr finProdFinEquiv).trans finProdFinEquiv

def instructions (N b copy : ℕ) (i : ℕ) : Expr :=
  if ok:i<count X*(N*7) then
    let p:=(order X N).symm ⟨i,ok⟩
    sources d G M copy (maskBase copy d G M) (varies X p.1.1 p.1.2 p.2.2)
      (scalar X p.1.1 p.1.2 p.2.1.val 0 p.2.2:Cell b)
  else .lit 0

def sequence (N b d G M copy : ℕ) :=
  let size:=CopyOrdinal.words d G M
  DescentPackedFlowBatch.passes (first copy d G M) size size (instructions (d:=d) (G:=G) (M:=M) X N b copy) 0 (count X*(N*7))

omit [_root_.Field F] [Fintype J] [DecidableEq J] in
theorem fields {w : ℕ} (N b copy : ℕ) (m : Memory w) (wideEnough : b*M≤w)
    (room : first copy d G M+(count X*(N*7))*CopyOrdinal.words d G M<2^w)
    (copies : ∀p : Row (2^d) G M,m (copy+(row _ _ _ p).val)=
      ((DescentSIMDLookup.data (CopyOrdinal.field (b:=b) name digits) p).val : Computability.VPVNP.BurstRAM.Word w))
    (_ready : copy+CopyOrdinal.words d G M<2^w) :
    let rows:=CopyOrdinal.words d G M
    let base:=maskBase copy d G M
    let out:=first copy d G M
    let pages:=count X*(N*7)
    let load:=DescentStaticWordColumn.program w base (maskValue d G M b) rows
    let maskImage:=DescentStaticWordColumn.image base (maskValue d G M b) m rows
    let ps:=sequence X N b d G M copy
    let finished:=result ps maskImage
    (load.seq (ProtocolRAM.program w ps)).Exec m finished (4+10*rows+clock ps) ∧
    (∀(v : Vertex X) (a : Fin 3) (g : Fin N) (f : Field) (p : Row (2^d) G M),
      finished (out+(order X N ((v,a),(g,f))).val*rows+(row _ _ _ p).val)=
        ((DescentSIMDLookup.data (fun s j=>(scalar X v a g.val (digits.symm (name.symm j,s)).val f:Cell b)) p).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    (∀addr,addr<copy ∨ out+pages*rows≤addr → finished addr=m addr) ∧
    clock ps≤4+pages*(4+rows*30) := by
  intro rows base out pages load maskImage ps finished
  have firstFit : out<2^w := (Nat.le_add_right ..).trans_lt room
  have before : copy+rows≤base:=Nat.add_le_add_left (span_ge _) _
  have masks : base+rows≤out:=Nat.add_le_add_left (span_ge _) _
  have edge : copy≤base:=(Nat.le_add_right ..).trans before
  have get (p : Row (2^d) G M) : maskImage (base+(row _ _ _ p).val)=(maskWord b M G p.2.val:Computability.VPVNP.BurstRAM.Word w) := by
    have within : (row (2^d) G M p).val < CopyOrdinal.words d G M :=
      (row (2^d) G M p).isLt
    refine (DescentStaticWordColumn.read base rows (maskValue d G M b) m within).trans ?_
    unfold maskValue
    rw [dite_eq_left within]
    change (maskWord b M G (((row (2^d) G M).symm (row (2^d) G M p)).2.val) :
      Computability.VPVNP.BurstRAM.Word w) = _
    rw [Equiv.symm_apply_apply]
  have copyKeep (p : Row (2^d) G M) : maskImage (copy+(row _ _ _ p).val)=
      ((DescentSIMDLookup.data (CopyOrdinal.field (b:=b) name digits) p).val:Computability.VPVNP.BurstRAM.Word w) := by
    apply Eq.trans (DescentStaticWordColumn.frame base rows (maskValue d G M b) m
      (copy+(row _ _ _ p).val) (.inl (lt_of_lt_of_le (Nat.add_lt_add_left (row _ _ _ p).isLt _) before)))
    exact copies p
  have fits (start : ℕ) (ok : start + span rows ≤ out) : (wordAt start rows 0).Fits w out := by
    change (0 < span rows ∧ span rows < 2^w ∧ start + 0*rows + span rows ≤ out) ∧ True
    simp only [Nat.zero_mul, Nat.add_zero]
    exact ⟨⟨span_pos _, (Nat.le_add_left ..).trans_lt (ok.trans_lt firstFit), ok⟩, trivial⟩
  have left := fits copy (show base ≤ out from (Nat.le_add_right ..).trans masks)
  have right := fits base (show out ≤ out from le_rfl)
  let op:=instructions (d:=d) (G:=G) (M:=M) X N b copy
  have fit (j : ℕ) (_ : j<pages) : (op j).Fits w out := by
    dsimp only [op,instructions,sources]
    split
    · split <;> first | exact left | exact ⟨trivial,right⟩
    · trivial
  obtain ⟨run,read,low⟩:=DescentPackedFlowBatch.execute out rows rows pages op maskImage fit room le_rfl
  refine ⟨?_,?_,?_,?_⟩
  · have mounted : load.Exec m maskImage (4+10*rows) :=
      DescentStaticWordColumn.mount base rows (maskValue d G M b) m (masks.trans_lt firstFit)
    intro labels regs keys machine
    exact Procedure.Exec.then (A:=load) (B:=ProtocolRAM.program w ps)
      (a:=m) (b:=maskImage) (c:=finished) mounted run machine
  · intro v a g f p
    let idx:=order X N ((v,a),(g,f))
    have atRow:=read idx (row _ _ _ p)
    dsimp only [op,instructions,idx] at atRow
    rw [dite_eq_left idx.isLt,Equiv.symm_apply_apply] at atRow
    refine atRow.trans ((eval_source name digits copy base maskImage _ _ wideEnough (by omega) copyKeep get p).trans ?_)
    apply congrArg (fun table : Block d → Fin G → Cell b =>
      ((DescentSIMDLookup.data table p).val : Computability.VPVNP.BurstRAM.Word w))
    funext s j
    have value := congrArg (fun x : ℕ => (x : Cell b))
      (split X v a g.val (digits.symm (name.symm j,s)).val f)
    cases h : varies X v a f <;> simpa [h, CopyOrdinal.field] using value.symm
  · intro addr off
    have rawKeep: maskImage addr=m addr := DescentStaticWordColumn.frame base rows (maskValue d G M b) m addr (by rcases off with lo|hi <;> omega)
    rcases off with lo|hi
    · exact (low _ (by omega)).trans rawKeep
    · exact (DescentPackedFlowBatch.above out rows rows op maskImage 0 pages addr le_rfl (by simpa using hi)).trans rawKeep
  · have cost (j : ℕ) (_ : j<pages) : (op j).work≤13 := by
      dsimp only [op,instructions,sources]
      split <;> try split <;> first
        | exact (by decide : 7 ≤ 13)
        | exact (by decide : 9 ≤ 13)
    exact DescentPackedFlowBatch.tariff out rows rows pages op 13 cost


def initialProgram (w base N b M : ℕ) :=
  let copy:=stampStart X base
  let rows:=CopyOrdinal.words d G M
  (stampProgram X name digits w base M b).seq
    ((DescentStaticWordColumn.program w (maskBase copy d G M) (maskValue d G M b) rows).seq
      (ProtocolRAM.program w (sequence X N b d G M copy)))

def initialMem (base N b M : ℕ) (m : Memory w) :=
  let copy:=stampStart X base
  result (sequence X N b d G M copy)
    (DescentStaticWordColumn.image (maskBase copy d G M) (maskValue d G M b)
      (stampImage X name digits base M b m) (CopyOrdinal.words d G M))

def initialEnd (base N d G M : ℕ) :=
  first (stampStart X base) d G M+(count X*(N*7))*CopyOrdinal.words d G M

def initialTicks (base N b d G M : ℕ) :=
  let rows:=CopyOrdinal.words d G M
  (4+10*Signed.size X+(4+10*count X)+(4+10*rows))+
    (4+10*rows+clock (sequence X N b d G M (stampStart X base)))

omit [Fintype J] [DecidableEq J] [_root_.Field F] in
/-- Install the physical copy stamp and all operand pages on the same memory.
Every initial memory gets the same measured execution. -/
theorem initial (base N b M : ℕ) (m : Memory w) (wideEnough : b*M≤w)
    (room : initialEnd X base N d G M<2^w) :
    let copy:=stampStart X base
    let rows:=CopyOrdinal.words d G M
    let out:=first copy d G M
    let final:=initialMem X name digits base N b M m
    (initialProgram X name digits w base N b M).Exec m final (initialTicks X base N b d G M) ∧
    (∀(v : Vertex X) (a : Fin 3) (g : Fin N) (f : Field) (p : Row (2^d) G M),
      final (out+(order X N ((v,a),(g,f))).val*rows+(row _ _ _ p).val)=
        ((DescentSIMDLookup.data (fun s j=>(scalar X v a g.val (digits.symm (name.symm j,s)).val f:Cell b)) p).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    (∀addr,addr<base ∨ initialEnd X base N d G M≤addr → final addr=m addr) ∧
    initialTicks X base N b d G M ≤ (4+10*Signed.size X+(4+10*count X)+(4+10*rows))+
      (4+10*rows+(4+(count X*(N*7))*(4+rows*30))) := by
  intro copy rows out final
  have early : base≤copy:=by dsimp [copy,stampStart];omega
  have mid : copy+rows≤out:=by
    have enough:=span_ge rows
    change copy+rows≤copy+span rows+span rows
    omega
  have «until» : out≤ initialEnd X base N d G M:= Nat.le_add_right ..
  have clean:=stamp_run (b:=b) (M:=M) X name digits base m (mid.trans_lt («until».trans_lt room))
  have installed := CopyOrdinal.issued (M:=M) (b:=b) name digits copy (Seed.image X base m)
    (mid.trans_lt («until».trans_lt room))
  obtain ⟨run,read,frame,price⟩:=fields X name digits N b copy (stampImage X name digits base M b m)
    wideEnough room installed.2.2.1 (mid.trans_lt («until».trans_lt room))
  refine ⟨?_,read,?_,Nat.add_le_add_left (Nat.add_le_add_left price _) _⟩
  · intro labels regs slots machine
    exact Procedure.Exec.then clean.1 (@run) machine
  intro addr off
  exact (frame addr (off.imp (fun lo=>lo.trans_le early) id)).trans
    (clean.2 addr (off.imp id (fun hi=>mid.trans («until».trans hi))))

/-- The registered node's actual leg and aligned chunk index select this page. -/
theorem original_scalar (c : (initialGroup X R s).Choice) (j : Fin R) (v : Vertex X)
    (u : (initialRecipe X R s c ⟨j,v⟩).Node) (i : Fin ((initialRecipe X R s c ⟨j,v⟩).arity u))
    (g : ℕ) (f : Field) :
    scalar X v (Fin.castLE (DescentBundleHistory.initial_arity X R s c ⟨j,v⟩ u) i) g j.val f =
      (originalAt X v (leg X v (Fin.cast (recipe_arity X c j v u) i)) j.val g).fields ⟨0,1,1⟩ f := by
  let slot := Fin.castLE (DescentBundleHistory.initial_arity X R s c ⟨j,v⟩ u) i
  have live : slot.val<legArity X v :=
    lt_of_lt_of_eq i.isLt (recipe_arity X c j v u)
  have sameIndex : (⟨slot.val,live⟩ : Fin (legArity X v)) =
      Fin.cast (recipe_arity X c j v u) i := Fin.ext rfl
  change scalar X v slot g j.val f = _
  simp only [scalar,leg?,dite_eq_left live,Option.elim_some,sameIndex]


omit [_root_.Field F] [Fintype J] [DecidableEq J] in
theorem hardware (w base N b M : ℕ) :
    let cpu:=initialProgram X name digits w base N b M
    let rows:=CopyOrdinal.words d G M
    CheapCode cpu ∧ DescentStaticWordColumn.names cpu ≤
      15*(Signed.size X+1)+15*(count X+1)+2*(15*(rows+1))+15+(count X*(N*7))*63 := by
  intro cpu rows
  let copy:=stampStart X base
  let I:=CopyOrdinal.shelf name digits w copy b M
  have len : I.length=rows:=by simp [I,CopyOrdinal.shelf,DescentPackedColony.Phase.Arena.Image.length,rows]
  have work (j : ℕ) (_ : 0≤j) (inside : j<0+count X*(N*7)) :
      (instructions (d:=d) (G:=G) (M:=M) X N b copy j).work≤13 := by
    have live : j < count X*(N*7) := by simpa only [Nat.zero_add] using inside
    simp only [instructions,dite_eq_left live,sources]
    split <;> first
      | exact (by decide : 7 ≤ 13)
      | exact (by decide : 9 ≤ 13)
  constructor
  · exact cheap_seq (cheap_seq (cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@DescentStaticWordColumn.cheap _ _ _ _)) I.hardware.1)
      (cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@ProtocolRAM.program_cheap _ _))
  · have end_ : DescentStaticWordColumn.names (ProtocolRAM.program w (sequence X N b d G M copy))
        ≤ 15+(count X*(N*7))*63 :=
      DescentPackedFlowBatch.program_bound (w:=w) (base:=first copy d G M) rows rows 0
        (count X*(N*7)) (instructions (d:=d) (G:=G) (M:=M) X N b copy) 13 work
    unfold cpu initialProgram stampProgram issue
    simp only [DescentStaticWordColumn.names_seq,Signed.program_names,DescentStaticWordColumn.names_mount]
    change 15*(Signed.size X+1)+15*(count X+1)+DescentStaticWordColumn.names I.program+
      (15*(rows+1)+DescentStaticWordColumn.names (ProtocolRAM.program w (sequence X N b d G M copy)))≤_
    rw [I.hardware.2,len]
    omega

end
end Hierarchy.DescentOperandStateBanks.Seed.Columns

end OAI
