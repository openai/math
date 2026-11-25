import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentResetStemHostRender
import OAI.Hierarchy.DescentOperandPairBook
import OAI.Hierarchy.DescentResetOriginalSlots
import OAI.Hierarchy.DescentResetStemIssuedWindows

namespace OAI
/-! # Issuing every real stem word at its final rectangular original-parent address -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetSourceTicketRAM DescentResetSourceTicketCompare
open DescentSIMDLookup DescentGL DescentResetStemCompactOrder DescentIssuedFallbackPanel
open scoped Classical BigOperators Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "priorWorld" => W.granular B.count (z*G.b) B.fit
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "U" => Fintype.card input.V
local notation "H" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "okCode" => fun t=>((T).codeLegal t).2
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Kind" => (Bool×(priorWorld).graph.Edge) ⊕ ((Z).Fallback ⊕ ((R).Contact ⊕ PrivateOccurrence B))
local notation "Short" => DescentResetCompactParent.Word H r Y L (A).cap slots pcCap

local notation "tape" => (Z).nativeResetEdges T vertex birth


local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fitBlock" => B.frame.enough.trans (Nat.sub_le ..)
local notation "previous" => input.order.trans Fin.valEmbedding
local notation "groupTable" => fun u : Host=>groupDomain digits B.frame.basis fitBlock (B.frame.host.symm (receiverRoot B u).1) (receiverRoot B u).2
local notation "halo" => fun u : Host=>hostDomain A input.vertex (B.frame.host.symm (receiverRoot B u).1)

open DescentIssuedFallbackPanel DescentResetStemWord
local notation "coarseFit" => (T).commonDepth
local notation "Slot" => Block (S.groupWidth k tail i+k-coarseFit)×Fin (2*(A).cap)
local notation "actor" u => B.frame.host.symm (receiverRoot B u).1
local notation "short" u => (receiverRoot B u).2
local notation "siteNames" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount i)) (input.vertex.trans Fin.valEmbedding))

open DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "ng" => S.groupCount (i+1)
local notation "X" => 2^k
local notation "J" => stemsCount B
local notation "K" => totalLocal B
local notation "count₀" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
variable {N field b M Wd : ℕ}
def stemShelf : Fin J↪Fin K := Fin.castLEEmb (Nat.le_add_right _ _)
def stemTag (q : Fin J) := (DescentResetStemPackedIssue.ordinal count₀ (A).cap).symm q
theorem stem_shelf_number (q : Fin J) : stemIndex B (stemTag B q).1 (stemTag B q).2=stemShelf B q := by
  apply Fin.ext
  exact congrArg (fun p : Fin J=>p.val) ((DescentResetStemPackedIssue.ordinal count₀ (A).cap).apply_symm_apply q)

def stemLaws (field b : ℕ) : DescentOperandPairBook.Laws 6 field b :=
  DescentResetStemWord.withHost (A).degree k r Y L (A).cap slots pcCap b

theorem stemLaws_zero (field b : ℕ) (s : Bool) : stemLaws B field b s (fun _=>0)=0 := by
  unfold stemLaws withHost
  apply inactive
  simp [truthful]

def stemOperands (field b M book : ℕ) (src : Fin X→Fin J→Fin 6→Expr) (n : Fin (X*J)) :=
  let t:=finProdFinEquiv.symm n
  DescentOperandPairBook.expr (stemLaws B field b) M book (stemTag B t.2).1 (src t.1 t.2)

def stemOriginalPasses (field b M N book original : ℕ) (src : Fin X→Fin J→Fin 6→Expr) :=
  DescentResetOriginalSlots.passes (stemShelf B) original (N*chunks ng M) (stemOperands B field b M book src)

def originalStemPhase (field b M N Wd book original : ℕ) (src : Fin X→Fin J→Fin 6→Expr)
    (_old : ∀x j t,(src x j t).Fits Wd book)
    (header : book+DescentOperandPairBook.words 6 field M≤original)
    (space : DescentResetOriginalSlots.finish original (N*chunks ng M) X K<2^Wd) :
    Chronology.NativePhase Wd :=
  let laws:=stemLaws B field b
  let ps:=stemOriginalPasses B field b M N book original src
  ⟨(DescentOperandPairBook.program laws M Wd book).seq (ProtocolRAM.program Wd ps),
   (4+10*DescentOperandPairBook.words 6 field M)+clock ps,
   fun mem=>result ps (DescentOperandPairBook.memory laws M book mem),
   cheap_seq (DescentOperandPairBook.mounted laws M book (fun _=>(0:Word Wd))
      (header.trans_lt ((Nat.le_add_right ..).trans_lt space))).2.2.2.2 (program_cheap _ _)⟩

theorem original_stems_any (field b M N book original : ℕ) (src : Fin X→Fin J→Fin 6→Expr)
    (old : ∀x j t,(src x j t).Fits Wd book)
    (header : book+DescentOperandPairBook.words 6 field M≤original)
    (space : DescentResetOriginalSlots.finish original (N*chunks ng M) X K<2^Wd) (m₀ : Memory Wd) :
    (originalStemPhase B field b M N Wd book original src old header space).Runs m₀ := by
  let f:=stemLaws B field b
  have room:=header.trans_lt ((Nat.le_add_right original _).trans_lt space)
  have fit (n : Fin (X*J)) : (stemOperands B field b M book src n).Fits Wd original :=
    ProtocolRAMGeneratedWrite.fits_mono _ header (DescentOperandPairBook.expr_fits f _ book _ (old _ _) room)
  obtain ⟨mount,_,_,_,_⟩:=DescentOperandPairBook.mounted f M book m₀ room
  intro P R₀ K₀ machine
  exact Procedure.Exec.then mount (program_exec _ _ (DescentResetOriginalSlots.safe (stemShelf B) original _ _ fit space)) machine

theorem original_stems_price (field b M N Wd book original time : ℕ) (src : Fin X→Fin J→Fin 6→Expr)
    (old : ∀x j t,(src x j t).Fits Wd book) (budget : ∀x j t,(src x j t).work≤time)
    (header : book+DescentOperandPairBook.words 6 field M≤original)
    (space : DescentResetOriginalSlots.finish original (N*chunks ng M) X K<2^Wd) :
    let F:=originalStemPhase B field b M N Wd book original src old header space
    let t:=14+6*(time+11)
    F.ticks≤(4+10*DescentOperandPairBook.words 6 field M)+4+(X*J)*(4+(N*chunks ng M)*(2*t+4)) ∧
    DescentStaticWordColumn.names F.program≤15*(DescentOperandPairBook.words 6 field M+1)+15+(X*J)*(11+4*t) := by
  intro F t
  let ps:=stemOriginalPasses B field b M N book original src
  let rows:=N*chunks ng M
  have known (p : Pass) (hp : p∈ps) : p.rows=rows ∧ p.term.work≤t := by
    obtain ⟨n,_,rfl⟩:=List.mem_map.mp hp
    exact ⟨rfl,DescentOperandPairBook.expr_work _ _ _ _ _ time (budget _ _)⟩
  have series (xs : List Pass) (bounded : ∀p∈xs,p.rows=rows ∧ p.term.work≤t) :
      clock xs≤4+xs.length*(4+rows*(2*t+4)) ∧
      DescentStaticWordColumn.names (ProtocolRAM.program Wd xs)≤15+xs.length*(11+4*t) := by
    induction xs with
    | nil =>
      rw [ProtocolRAM.program,DescentStaticWordColumn.names_scan];exact ⟨by simp [clock],by simp [Expr.work]⟩
    | cons p xs ih =>
      have ht:=bounded p (.head _)
      obtain ⟨cost,names⟩:=ih (fun p hp=>bounded p (.tail _ hp))
      have c : p.clock≤4+rows*(2*t+4):=by
        simp only [Pass.clock,ht.1]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ht.2) 4)) 4
      have a : DescentStaticWordColumn.names (p.procedure Wd)≤11+4*t:=by
        rw [Pass.procedure,DescentStaticWordColumn.names_scan]
        omega
      constructor
      · change p.clock + clock xs ≤ _
        refine (Nat.add_le_add c cost).trans_eq ?_
        rw [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
      · rw [ProtocolRAM.program,DescentStaticWordColumn.names_seq]
        refine (Nat.add_le_add a names).trans_eq ?_
        rw [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
  obtain ⟨cost,names⟩:=series ps known
  have len : ps.length=X*J:=by simp [ps,stemOriginalPasses,DescentResetOriginalSlots.passes]
  rw [len] at cost names
  refine ⟨(Nat.add_le_add_left cost _).trans_eq (Nat.add_assoc _ _ _).symm,?_⟩
  change DescentStaticWordColumn.names ((DescentOperandPairBook.program _ M Wd book).seq (ProtocolRAM.program Wd ps))≤_
  rw [DescentStaticWordColumn.names_seq]
  have installed : DescentStaticWordColumn.names (DescentOperandPairBook.program (stemLaws B field b) M Wd book)=
      15*(DescentOperandPairBook.words 6 field M+1):= DescentStaticWordColumn.names_mount ..
  rw [installed]
  exact (Nat.add_le_add_left names _).trans_eq (by omega)

theorem original_stems (receivers : Fin N→Option B.next.V) (book original : ℕ)
    (src : Fin X→Fin J→Fin 6→Expr) (val : Fin X→Fin J→Fin N→Fin ng→Fin 6→Cell field)
    (m₀ : Memory Wd) (old : ∀x j i,(src x j i).Fits Wd book)
    (dataAt : ∀x j i,Source (src x j i) (fun h g=>val x j h g i) M m₀)
    (observed : ∀x j,StemInputs B receivers x (stemTag B j).1 (stemTag B j).2 (val x j))
    (hostRoom : (A).degree+1<2^field) (header : book+DescentOperandPairBook.words 6 field M≤original)
    (space : DescentResetOriginalSlots.finish original (N*chunks ng M) X K<2^Wd) :
    let install:=DescentOperandPairBook.program (stemLaws B field b) M Wd book
    let mounted:=DescentOperandPairBook.memory (stemLaws B field b) M book m₀
    let ps:=stemOriginalPasses B field b M N book original src
    let prog:=install.seq (ProtocolRAM.program Wd ps)
    let final:=result ps mounted
    prog.Exec m₀ final ((4+10*DescentOperandPairBook.words 6 field M)+clock ps) ∧ CheapCode prog ∧
    (∀x : Fin X,∀j : Fin J,∀p : Row N ng M,final
      (DescentResetOriginalSlots.offset original (N*chunks ng M) K x.val (stemShelf B j).val+
       (row N ng M p).val)=((data (fun v g=>(actualParentNumber B receivers x (stemShelf B j) v g:Cell b)) p).val:Word Wd)) ∧
    (∀x : Fin X,∀j : Fin K, J≤j.val→∀p : Fin (N*chunks ng M),
      final (DescentResetOriginalSlots.offset original (N*chunks ng M) K x.val j.val+p.val)=
        m₀ (DescentResetOriginalSlots.offset original (N*chunks ng M) K x.val j.val+p.val)) ∧
    ∀addr,addr<book ∨ DescentResetOriginalSlots.finish original (N*chunks ng M) X K≤addr→final addr=m₀ addr := by
  intro install mounted ps prog final
  let laws:=stemLaws B field b
  let ops:=stemOperands B field b M book src
  let top:=DescentResetOriginalSlots.finish original (N*chunks ng M) X K
  have oldEnd:original≤top:=Nat.le_add_right ..
  have room:=header.trans_lt (oldEnd.trans_lt space)
  obtain ⟨mount,_,_,keep,cheap⟩:=DescentOperandPairBook.mounted laws M book m₀ room
  have issued (x : Fin X) (j : Fin J) :
      (ops (finProdFinEquiv (x,j))).Fits Wd original ∧
      Source (ops (finProdFinEquiv (x,j))) (fun v g=>(actualParentNumber B receivers x (stemShelf B j) v g:Cell b)) M mounted:=by
    let s:=(stemTag B j).1
    have found:=DescentOperandPairBook.issued laws (stemLaws_zero B field b) s book (src x j) m₀ (val x j)
      (old x j) (dataAt x j) room
    have point:=stem_read_number (b:=b) B receivers x s (stemTag B j).2 (val x j) (observed x j) hostRoom
    constructor
    · simpa only [ops,stemOperands,Equiv.symm_apply_apply] using ProtocolRAMGeneratedWrite.fits_mono _ header found.1
    · have numbered : (fun v g=>laws s (val x j v g)) =
          (fun v g=>(actualParentNumber B receivers x (stemShelf B j) v g:Cell b)) := by
        funext v g
        exact (point v g).trans (congrArg (fun t=>(actualParentNumber B receivers x t v g : Cell b)) (stem_shelf_number B j))
      have srcOK := found.2
      rw [numbered] at srcOK
      simpa only [ops,stemOperands,Equiv.symm_apply_apply] using srcOK
  have fits (t : Fin (X*J)) : (ops t).Fits Wd original:=by
    obtain ⟨⟨x,j⟩,rfl⟩:=finProdFinEquiv.surjective t
    exact (issued x j).1
  have safe:=DescentResetOriginalSlots.safe (stemShelf B) original _ ops fits space
  refine ⟨Procedure.Exec.then mount (program_exec _ _ safe),cheap_seq cheap (program_cheap _ _),?_,?_,?_⟩
  · intro x j p
    exact DescentResetOriginalSlots.slot_read (stemShelf B) original ops mounted x j _ (issued x j).1 (issued x j).2 p
  · intro x j hj p
    have absent (a:Fin J):stemShelf B a≠j:=by intro h;have:=a.isLt;have eqn:=congrArg Fin.val h;change a.val=j.val at eqn;omega
    have same:=DescentResetOriginalSlots.frame_slot (stemShelf B) original (N*chunks ng M) ops mounted x j absent p
    exact same.trans (keep _ (.inr (header.trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))))
  · intro addr away
    refine (DescentResetOriginalSlots.frame (stemShelf B) original (N*chunks ng M) ops mounted addr ?_).trans
      (keep _ (away.imp_right (fun h=>(header.trans oldEnd).trans h)))
    intro t
    have hit : (⟨original+(DescentResetOriginalSlots.cell (stemShelf B) t).val*
      DescentResetOriginalSlots.stride (N*chunks ng M),N*chunks ng M,ops t⟩:Pass)∈ps:=
      List.mem_map.mpr ⟨t,List.mem_finRange _,rfl⟩
    obtain ⟨lo,hi⟩:=DescentResetOriginalSlots.earlier (stemShelf B) original _ ops _ hit
    exact away.imp (fun h=>h.trans_le ((Nat.le_add_right _ _).trans (header.trans lo))) (fun h=>hi.trans h)
end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
