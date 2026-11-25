import OAI.Hierarchy.DescentPrivateMaskShape
import OAI.Hierarchy.DescentNativeBankLookup
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentResetStemProjectExpr
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentResetLocalRoster
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Extracting the original private width and both endpoint shapes in the successor pitch -/
namespace Hierarchy.DescentPrivateMaskDeck
open DescentSIMDLookup DescentPackedZip DescentResetLocalRoster DescentIssuedTerminalId
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

namespace Shape
variable (A : Shape)
/-- The original five-digit row is occupancy, two shapes, width, and the private-wire marker.
All three projected fields vanish whenever the original row is empty. -/
def scalar (slot : Fin A.cap) (field : Fin 3) (x : Cell A.panels) : Cell A.metaBits :=
  let get (j : Fin 5) := digit A.rawBits (finProdFinEquiv (slot,j)).val x.val
  if get 0=1 then get ⟨field.val+1,by omega⟩ else 0

@[simp] theorem scalar_zero (slot : Fin A.cap) (f : Fin 3) : A.scalar slot f 0=0 := by
  simp [scalar,digit]

def vector (slot : Fin A.cap) (field : Fin 3) (x : Cell (A.panels*A.oldBatch)) :=
  encode A.metaBits A.oldBatch (fun i=>A.scalar slot field ((encode A.panels A.oldBatch).symm x i))

def literal (i : ℕ) : ℕ :=
  if live : i/A.words<A.cap*3 then
    let q:=finProdFinEquiv.symm (⟨i/A.words,live⟩ : Fin (A.cap*3))
    (A.vector q.1 q.2 ⟨i%A.words,Nat.mod_lt _ (Nat.two_pow_pos _)⟩).val
  else 0

def address (base : ℕ) (s : Fin A.cap) (j : Fin 3) : Bank :=
  ⟨base+(finProdFinEquiv (s,j)).val*A.words,A.panels*A.oldBatch⟩

theorem literal_at (s : Fin A.cap) (j : Fin 3) (x : Cell (A.panels*A.oldBatch)) :
    A.literal ((finProdFinEquiv (s,j)).val*A.words+x.val)=(A.vector s j x).val := by
  have xlt : x.val<A.words:=x.isLt
  let page := finProdFinEquiv (s,j)
  have quotient : (page.val*A.words+x.val)/A.words=page.val := by
    rw [Nat.mul_comm page.val A.words,Nat.mul_add_div (Nat.zero_lt_of_lt xlt),
      Nat.div_eq_of_lt xlt,Nat.add_zero]
  change A.literal (page.val*A.words+x.val)=(A.vector s j x).val
  unfold literal
  split
  next live =>
    have index : (⟨(page.val*A.words+x.val)/A.words,live⟩ : Fin (A.cap*3))=page :=
      Fin.ext quotient
    have decoded : finProdFinEquiv.symm page=(s,j) := finProdFinEquiv.symm_apply_apply (s,j)
    rw [index,decoded]
    simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt xlt]
  next outside =>
    rw [quotient] at outside
    exact (outside page.isLt).elim

def query (base : ℕ) (s : Fin A.cap) (j : Fin 3) (input : Expr) := Expr.lookup (A.address base s j) input

def wordsPhase (w base : ℕ) : DescentSixParty.Chronology.NativePhase w :=
  ⟨DescentStaticWordColumn.program w base A.literal A.count,4+10*A.count,
    fun m=>DescentStaticWordColumn.image base A.literal m A.count,@DescentStaticWordColumn.cheap _ _ _ _⟩

theorem words_any {w : ℕ} (base : ℕ) (m : Memory w) (room : A.projected base<2^w) :
    (A.wordsPhase w base).Runs m ∧ ∀z,z<base ∨ A.projected base≤z→(A.wordsPhase w base).image m z=m z :=
  ⟨DescentStaticWordColumn.mount base A.count A.literal m room,
    fun z away => DescentStaticWordColumn.frame base A.count A.literal m z away⟩

theorem query_fits {w : ℕ} (base : ℕ) (s : Fin A.cap) (j : Fin 3) (input : Expr)
    (bound : input.Fits w (A.projected base)) (room : A.projected base<2^w) :
    (A.query base s j input).Fits w (A.projected base) := by
  have h:=Nat.mul_le_mul_right A.words (finProdFinEquiv (s,j)).isLt
  rw [Nat.succ_mul] at h
  have end_ : (A.address base s j).base+(A.address base s j).size≤A.projected base:=by
    change base+_*A.words+A.words≤base+(A.cap*3)*A.words
    omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt room),end_⟩,bound⟩

theorem query_source {w H G : ℕ} (base : ℕ) (s : Fin A.cap) (j : Fin 3) (input : Expr)
    (x : Fin H→Fin G→Cell A.panels) (m : Memory w) (small : input.Fits w base)
    (read : Source input x A.oldBatch m) (room : A.projected base<2^w) :
    Source (A.query base s j input) (fun h g=>A.scalar s j (x h g)) A.oldBatch ((A.wordsPhase w base).image m) := by
  let q:=finProdFinEquiv (s,j)
  have before:=A.words_any base m room
  have fits:=A.query_fits base s j input (ProtocolRAMGeneratedWrite.fits_mono _ (A.cuts base).1 small) room
  intro p
  let z:=data (M:=A.oldBatch) x p
  have old : input.eval ((A.wordsPhase w base).image m) _=(z.val:Word w):=
    (eval_below input _ m _ small (fun a ha=>before.2 a (.inl ha))).trans (read p)
  have loc : q.val*A.words+z.val<A.count := by
    have limit:=Nat.mul_le_mul_right A.words q.isLt
    rw [Nat.succ_mul] at limit
    exact (Nat.add_lt_add_left z.isLt _).trans_le limit
  rw [query,lookup_nat (A.address base s j) _ _ input z.val old z.isLt fits.1.2.1]
  change DescentStaticWordColumn.image base A.literal m A.count (base+q.val*A.words+z.val)=_
  rw [Nat.add_assoc,DescentStaticWordColumn.read base A.count A.literal m loc,A.literal_at s j z]
  have eqn : A.vector s j z=data (fun h g=>A.scalar s j (x h g)) p := by
    simp only [z,vector,data,Equiv.symm_apply_apply]
    apply congrArg (encode A.metaBits A.oldBatch)
    funext i
    by_cases live : p.2.val*A.oldBatch+i.val<G <;> simp [live]
  rw [eqn]


end Shape
end
end Hierarchy.DescentPrivateMaskDeck

end OAI
