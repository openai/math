import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentPackedColumnSum
import OAI.Hierarchy.DescentPackedSumWords
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Incoming reset grains from the previous signed windows in remixed coordinates -/
namespace Hierarchy.DescentFundedCensus.Arrivals
open DescentSIMDLookup DescentPackedZip DescentPackedColumnSum
open DescentOrdinaryAtomFieldRAM.ROM DescentColonies.SplitRAM DescentSharedCableNames
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {D cap H G L M w : ℕ}

def bit (D cap : ℕ) (x : Cell (DescentSignedCableCodec.width D cap)) : ℕ :=
  ((DescentSignedCableCodec.decode D cap x).any Stage.Live.target).toNat

theorem bit_zero : bit D cap 0=0 := by
  rw [←DescentSignedCableCodec.empty (D:=D) (cap:=cap)]
  simp [bit]

def value (D cap b L : ℕ) (x : Cell (DescentSignedCableCodec.width D cap*L)) : ℕ :=
  ∑u : Fin L,bit D cap ((encode _ L).symm x u)*(2^b)^u.val

theorem zero_value (b L : ℕ) : value D cap b L 0=0 := by
  have clear : (encode (DescentSignedCableCodec.width D cap) L).symm 0=fun _=>0:=by
    apply (encode (DescentSignedCableCodec.width D cap) L).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change 0 = (finFunctionFinEquiv (fun _ : Fin L=>(0 : Cell (DescentSignedCableCodec.width D cap)))).val
    simp []
  simp [value,clear,bit_zero]

def pages (D cap b L M : ℕ) : Fin 1→Page :=
  fun _=>⟨(DescentSignedCableCodec.width D cap*L)*M,piece (b*L) (value D cap b L)⟩
def length (D cap L M : ℕ) := 2^((DescentSignedCableCodec.width D cap*L)*M)
def roof (base D cap L M : ℕ) := base+length D cap L M
def flags (base D cap _b L M : ℕ) : Bank :=⟨base,(DescentSignedCableCodec.width D cap*L)*M⟩
def expr (base D cap b L M : ℕ) (signed : Fin (2*cap)→Expr) :=
  total (fun j=>Expr.lookup (flags base D cap b L M) (signed j)) (List.finRange (2*cap))

def count (signed : Fin (2*cap)→Fin H→Fin G→Fin L→Cell (DescentSignedCableCodec.width D cap)) (h : Fin H) (g : Fin G) (l : Fin L) :=
  ∑j,bit D cap (signed j h g l)

theorem count_le (signed : Fin (2*cap)→Fin H→Fin G→Fin L→Cell (DescentSignedCableCodec.width D cap)) (h : Fin H) (g : Fin G) (l : Fin L) :
    count (D:=D) signed h g l ≤ 2*cap := by
  unfold count
  calc
    _ ≤ ∑ _j : Fin (2*cap),(1 : ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      exact Bool.toNat_le _
    _ = _ := by simp

theorem summed (b : ℕ) (signed : Fin (2*cap)→Fin L→Cell (DescentSignedCableCodec.width D cap))
    (small : ∀l,(∑j,bit D cap (signed j l))<2^b) :
    (∑j,value D cap b L (encode (DescentSignedCableCodec.width D cap) L (signed j)))=
      (encode b L (fun l=>⟨_,small l⟩)).val := by
  unfold value
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_comm]
  change _=(finFunctionFinEquiv (fun l : Fin L=>(⟨_,small l⟩ : Cell b))).val
  rw [finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_mul]

def program (base D cap b L M w : ℕ) := mount (pages D cap b L M) ((DescentSignedCableCodec.width D cap*L)*M) w base
def memory (base D cap b L M : ℕ) (m : Memory w) := after (pages D cap b L M) ((DescentSignedCableCodec.width D cap*L)*M) base m

theorem any (base D cap b L M : ℕ) (m : Memory w) (room : roof base D cap L M<2^w) :
    (program base D cap b L M w).Exec m (memory base D cap b L M m) (4+10*length D cap L M) ∧
      CheapCode (program base D cap b L M w) ∧
      (∀a,a<base ∨ roof base D cap L M≤a→memory base D cap b L M m a=m a) ∧
      DescentStaticWordColumn.names (program base D cap b L M w)=15*(length D cap L M+1) := by
  have limits : base+1*2^(((DescentSignedCableCodec.width D cap)*L)*M)<2^w := by
    simpa only [roof,length,Nat.one_mul] using room
  obtain ⟨run,names⟩ := DescentOrdinaryAtomFieldRAM.ROM.run (pages D cap b L M) (((DescentSignedCableCodec.width D cap)*L)*M) base m limits
  rw [Nat.one_mul] at run names
  refine ⟨@run,@DescentOrdinaryAtomFieldRAM.ROM.cheap 1 (pages D cap b L M) (((DescentSignedCableCodec.width D cap)*L)*M) w base,?_,names⟩
  intro a ha
  exact DescentOrdinaryAtomFieldRAM.ROM.frame (pages D cap b L M) (((DescentSignedCableCodec.width D cap)*L)*M) base m a
    (by simpa only [roof,length,Nat.one_mul] using ha)

theorem source (base b L : ℕ) (m : Memory w) (signed : Fin (2*cap)→Expr)
    (digits : Fin (2*cap)→Fin H→Fin G→Fin L→Cell (DescentSignedCableCodec.width D cap)) (early : ∀j,(signed j).Fits w base)
    (actual : ∀j,Source (signed j) (fun h g=>encode (DescentSignedCableCodec.width D cap) L (digits j h g)) M m)
    (small : 2*cap<2^b) (space : roof base D cap L M<2^w) :
    (expr base D cap b L M signed).Fits w (roof base D cap L M) ∧ Source (expr base D cap b L M signed)
      (fun (h : Fin H) (g : Fin G)=>encode b L (fun l=>⟨_,(count_le (D:=D) digits h g l).trans_lt small⟩)) M (memory base D cap b L M m) :=by
  let dest:=memory base D cap b L M m
  let B:=flags base D cap b L M
  have ready:=any base D cap b L M m space
  have depth : 0<length D cap L M:=Nat.two_pow_pos _
  have bankReady : B.Fits w (roof base D cap L M) := ⟨depth,(Nat.le_add_left ..).trans_lt space,le_rfl⟩
  have fits j : (Expr.lookup B (signed j)).Fits w (roof base D cap L M):=
    ⟨bankReady,ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (early j)⟩
  refine ⟨fits_total _ fits _,?_⟩
  intro rowIndex
  have live (j : Fin (2*cap)) :
      (Expr.lookup B (signed j)).eval dest ((row H G M rowIndex).val:Word w)=
        (packed (b*L) (fun h g=>value D cap b L (encode (DescentSignedCableCodec.width D cap) L (digits j h g))) rowIndex:Word w) :=by
    let input (h : Fin H) (g : Fin G) := encode (DescentSignedCableCodec.width D cap) L (digits j h g)
    have got : (signed j).eval dest ((row H G M rowIndex).val:Word w) =
        ((data input rowIndex).val:Word w) :=
      (eval_below (signed j) _ m dest (early j) (fun a ha=>ready.2.2.1 a (.inl ha))).trans (actual j rowIndex)
    change B.read dest ((signed j).eval dest _)=_
    rw [got,bank_read B dest (data input rowIndex).isLt bankReady]
    have stored:=DescentOrdinaryAtomFieldRAM.ROM.read (pages D cap b L M) (((DescentSignedCableCodec.width D cap)*L)*M) base m (0 : Fin 1) le_rfl
      (data input rowIndex)
    change dest ((base+0*2^(((DescentSignedCableCodec.width D cap)*L)*M))+(data input rowIndex).val) =
      (piece (b*L) (value D cap b L) (data input rowIndex):Word w) at stored
    rw [Nat.zero_mul,Nat.add_zero] at stored
    exact stored.trans (congrArg (fun z : ℕ=>(z:Word w))
      (piece_data (width:=b*L) (value D cap b L) (zero_value (D:=D) (cap:=cap) b L) input rowIndex))
  have allRows:=DescentPackedSumWords.eval_sum _ _ dest _ live (List.finRange (2*cap))
  rw [←List.ofFn_eq_map,List.sum_ofFn,packed_sum] at allRows
  have packedRow (h : Fin H) (g : Fin G) : (∑j,value D cap b L (encode (DescentSignedCableCodec.width D cap) L (digits j h g)))=
      (encode b L (fun l=>⟨_,(count_le (D:=D) digits h g l).trans_lt small⟩)).val :=
    summed (D:=D) (cap:=cap) b (fun j=>digits j h g)
      (fun l=>(count_le (D:=D) digits h g l).trans_lt small)
  simp_rw [packedRow] at allRows
  exact allRows.trans (congrArg (fun n : ℕ=>(n:Word w))
    (packed_data (b*L) (fun h g=>encode b L
      (fun l=>⟨_,(count_le (D:=D) digits h g l).trans_lt small⟩)) rowIndex))

end
end Hierarchy.DescentFundedCensus.Arrivals

end OAI
