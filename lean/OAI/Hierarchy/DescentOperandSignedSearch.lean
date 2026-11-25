import OAI.Hierarchy.DescentOperandPriorIncidence
import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentPackedSumWords

namespace OAI
/-! # A bounded parallel search for the previous signed incidence of a packed operand -/
namespace Hierarchy.DescentOperandSignedSearch
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM
open DescentSharedCableNames DescentTerminalSignedGrainWord DescentOperandPriorIncidence
open DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentPackedSumWords
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {D cap H G M w : ℕ}

def keyBits (D cap : ℕ) := Packed.bits (D*cap*cap)
def outBits (cap : ℕ) := Packed.bits ((2*cap)*(2*cap))

def hit (D cap : ℕ) (face : Fin 2) (s : Fin (2*cap)) (q : Cell (keyBits D cap))
    (actual : Cell (DescentSignedCableCodec.width D cap)) :=
  q.val≠0 ∧ sign cap s=face ∧ project D cap actual=q

def contribution (D cap : ℕ) (face : Fin 2) (s : Fin (2*cap)) (q : Cell (keyBits D cap))
    (actual : Cell (DescentSignedCableCodec.width D cap)) : Cell (outBits cap) :=
  if hit D cap face s q actual then
    ⟨s.val+1,by
      have below : s.val+1≤2*cap:=s.isLt
      have positive : 0<2*cap:=Nat.zero_lt_of_lt s.isLt
      have sq : 2*cap≤(2*cap)*(2*cap):=Nat.le_mul_of_pos_right _ positive
      exact (below.trans sq).trans_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide : 1<2) _))⟩
  else 0

theorem clear (D cap : ℕ) (face : Fin 2) (s : Fin (2*cap)) : contribution D cap face s 0 0=0 := by
  simp [contribution,hit]

theorem mass (D cap : ℕ) (face : Fin 2) (q : Cell (keyBits D cap))
    («fields» : Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap)) :
    (∑s,(contribution D cap face s q («fields» s)).val)<2^(outBits cap) := by
  have bound (s : Fin (2*cap)) : (contribution D cap face s q («fields» s)).val≤2*cap := by
    unfold contribution;split <;> first | exact s.isLt | exact Nat.zero_le _
  calc
    _ ≤ ∑_s : Fin (2*cap),2*cap := Finset.sum_le_sum (fun s _=>bound s)
    _ = (2*cap)*(2*cap) := by simp
    _ < 2^(outBits cap) := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide : 1<2) _)

def resultCell (D cap : ℕ) (face : Fin 2) (q : Cell (keyBits D cap))
    («fields» : Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap)) : Cell (outBits cap) :=
  ⟨_,mass D cap face q «fields»⟩

theorem result_one (D cap : ℕ) (face : Fin 2) (q : Cell (keyBits D cap))
    («fields» : Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap)) (s : Fin (2*cap))
    (only : ∀i,hit D cap face i q («fields» i) ↔ i=s) : (resultCell D cap face q «fields»).val=s.val+1 := by
  change (∑i,(contribution D cap face i q («fields» i)).val)=_
  rw [Finset.sum_eq_single s]
  · simp [contribution,(only s).2 rfl]
  · intro i _ other
    have absent : ¬hit D cap face i q («fields» i) := fun h => other ((only i).1 h)
    simp [contribution, absent]
  · simp

theorem result_empty (D cap : ℕ) (face : Fin 2) (q : Cell (keyBits D cap))
    («fields» : Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap))
    (empty : ∀j,¬hit D cap face j q («fields» j)) : (resultCell D cap face q «fields»).val=0 := by
  change (∑i,(contribution D cap face i q («fields» i)).val)=0
  simp [contribution,empty]

def pages (D cap M : ℕ) (face : Fin 2) (p : Fin ((2*cap)*2)) : Page :=
  let j:=finProdFinEquiv.symm p
  binary (contribution D cap face j.1) M j.2

def slot (s : Fin (2*cap)) (f : Fin 2) : Fin ((2*cap)*2) := finProdFinEquiv (s,f)
def width (D cap M : ℕ) := (keyBits D cap+DescentSignedCableCodec.width D cap)*M
theorem layout (s : Fin (2*cap)) (f : Fin 2) (face : Fin 2) :
    pages D cap M face (slot s f)=binary (contribution D cap face s) M f := by simp [pages,slot]

theorem page_room (face : Fin 2) (p : Fin ((2*cap)*2)) : (pages D cap M face p).bits≤width D cap M := by
  obtain ⟨⟨s,f⟩,rfl⟩:=finProdFinEquiv.surjective p
  rw [show pages D cap M face (finProdFinEquiv (s,f))=binary (contribution D cap face s) M f from layout s f face]
  fin_cases f
  · exact Nat.mul_le_mul_right M (Nat.le_add_right ..)
  · exact le_rfl

def table (D cap M base : ℕ) (face : Fin 2) (s : Fin (2*cap)) :=
  joined (pages D cap M face) (width D cap M) base (slot s)

def expr (D cap M base : ℕ) (face : Fin 2) (q : Expr) (old : Fin (2*cap)→Expr) :=
  total (fun s=>(table D cap M base face s).read q (old s)) (List.finRange (2*cap))

def endROM (D cap M base : ℕ) := base+((2*cap)*2)*2^(width D cap M)

theorem run (D cap M base out : ℕ) (face : Fin 2) (q : Expr) (old : Fin (2*cap)→Expr) (m : Memory w)
    (request : Fin H→Fin G→Cell (keyBits D cap))
    (field : Fin (2*cap)→Fin H→Fin G→Cell (DescentSignedCableCodec.width D cap))
    (small : q.Fits w base) (held : ∀s,(old s).Fits w base) (requests : Source q request M m)
    (observed : ∀s,Source (old s) (field s) M m) (order : endROM D cap M base≤out) (room : out+H*chunks G M<2^w) :
    let book:=pages D cap M face
    let count:=H*chunks G M
    let span:=width D cap M
    let op:=expr D cap M base face q old
    let dst:=image out count op (after book span base m)
    ((mount book span w base).seq (scan w out count op)).Exec m dst
      ((4+10*(((2*cap)*2)*2^span))+(4+count*(2*op.work+4))) ∧
    (∀r : Row H G M,dst (out+(row H G M r).val)=((data (fun h g=>
      resultCell D cap face (request h g) (fun j=>field j h g)) r).val : Word w)) ∧
    (∀a,a<base ∨ out+count≤a → dst a=m a) ∧ CheapCode ((mount book span w base).seq (scan w out count op)) := by
  intro book count span op dst
  let dict:=after book span base m
  have high : out<2^w := (Nat.le_add_right ..).trans_lt room
  have sep : base+((2*cap)*2)*2^span≤out:=order
  have low : base≤out:=(Nat.le_add_right ..).trans sep
  have protect:=DescentOrdinaryAtomFieldRAM.ROM.frame book span base m
  have keep {z : ℕ} (e : Expr) (bd : e.Fits w base) (v : Fin H→Fin G→Cell z) (source : Source e v M m) : Source e v M dict :=
    fun r=>(eval_below e _ m dict bd (fun a ha=>protect a (.inl ha))).trans (source r)
  let T:=table D cap M base face
  have fit (s : Fin (2*cap)) : DescentPackedZip.Fits (T s) q (old s)
      (keyBits D cap) (DescentSignedCableCodec.width D cap) M out w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ low small,ProtocolRAMGeneratedWrite.fits_mono _ low (held s),
      bank_room book span base out _ (page_room face (slot s 0)) sep high,
      bank_room book span base out _ (page_room face (slot s 1)) sep high,
      congrArg Page.bits (layout (D:=D) (M:=M) s 0 face),congrArg Page.bits (layout (D:=D) (M:=M) s 1 face)⟩
  have safe (s : Fin (2*cap)) : ((T s).read q (old s)).Fits w out := by
    have f:=fit s; simp [DescentPackedZip.Tables.read,Expr.Fits,f.left,f.right,f.apply,f.shift]
  have started:=DescentOrdinaryAtomFieldRAM.ROM.run book span base m (sep.trans_lt high)
  refine ⟨Procedure.Exec.then started.1 (scan_exec out count op dict (fits_total _ safe _) room),?_,?_,
    cheap_seq (cheap book span w base) (scan_cheap w out count op)⟩
  · intro r
    have each (s : Fin (2*cap)):=DescentPackedZip.read_data (T s) q (old s) out (fit s) (contribution D cap face s)
      (clear D cap face s) dict (binary_mounted _ M book span base m (page_room face) (slot s) (fun t=>layout s t face))
      _ _ (keep _ small _ requests) (keep _ (held s) _ (observed s)) r
    have total_:=eval_sum _ _ dict _ each (List.finRange (2*cap))
    refine (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H G M r)).trans (total_.trans ?_)
    apply congrArg (fun x : ℕ=>(x:Word w))
    rw [←List.ofFn_eq_map,List.sum_ofFn]
    simp_rw [lanes_val]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases present:r.2.val*M+j.val<G
    · simp only [dite_eq_left present,resultCell,Finset.sum_mul]
    · simp [present]
  · intro a off
    exact (ProtocolRAMGeneratedWrite.frame_image out count op dict a (by rcases off with lo|hi <;> omega)).trans
      (protect a (by rcases off with lo|hi <;> omega))

end
end Hierarchy.DescentOperandSignedSearch

end OAI
