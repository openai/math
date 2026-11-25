import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentSeedSignedBroadcast

namespace OAI
/-! # Shared literal broadcasting tables for the packed reset headers -/
namespace Hierarchy.DescentResetStemHeaders
open DescentSixParty.Chronology DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def rawBank (raw H j : ℕ) : Bank := ⟨raw+j*H, Nat.clog 2 H⟩
def wideBank (base b : ℕ) : Bank := ⟨base,b⟩
def actorBank (base b n : ℕ) : Bank := ⟨base+2^b, Nat.clog 2 n⟩
def maskBank (base b n : ℕ) : Bank := ⟨base+2^b+span n, Nat.clog 2 n⟩
def romSize (b n : ℕ) := 2^b+2*span n

/-- These words depend only on the public dimensions. The middle table maps a
packed row to its actor ordinal, independently of the physical descriptor. -/
def literals (H G M b i : ℕ) : ℕ :=
  let n := H*chunks G M
  if lo : i < 2^b then (DescentSeedSignedBroadcast.wide M (⟨i,lo⟩ : Cell b)).val
  else if i < 2^b+span n then
    DescentSeedSignedBroadcast.finRead (fun u : Fin n => ((row H G M).symm u).1.val) (i-2^b)
  else
    DescentSeedSignedBroadcast.finRead (fun u : Fin n => maskWord b M G ((row H G M).symm u).2.val)
      (i-(2^b+span n))

def prepare (w H G M b base : ℕ) : NativePhase w :=
  let n := romSize b (H*chunks G M)
  ⟨DescentStaticWordColumn.program w base (literals H G M b) n,4+10*n,
    fun m => DescentStaticWordColumn.image base (literals H G M b) m n,
    @DescentStaticWordColumn.cheap w base (literals H G M b) n⟩

structure TablesOK (H G M b base : ℕ) {w : ℕ} (m : Memory w) : Prop where
  word : ∀ x : Cell b, m ((wideBank base b).base+x.val) = ((DescentSeedSignedBroadcast.wide M x).val : Word w)
  actor : ∀ p : Row H G M, m ((actorBank base b (H*chunks G M)).base+(row H G M p).val) = (p.1.val : Word w)
  mask : ∀ p : Row H G M, m ((maskBank base b (H*chunks G M)).base+(row H G M p).val) =
    (maskWord b M G p.2.val : Word w)

theorem prepared (w H G M b base : ℕ) (m : Memory w) (fit : base+romSize b (H*chunks G M) < 2^w) :
    (prepare w H G M b base).Runs m ∧ TablesOK H G M b base ((prepare w H G M b base).image m) ∧
    (∀ a, a < base ∨ base+romSize b (H*chunks G M) ≤ a → (prepare w H G M b base).image m a=m a) := by
  let n := H*chunks G M
  have sn := span_ge n
  refine ⟨?_, ⟨?_, ?_, ?_⟩,
    fun a h => DescentStaticWordColumn.frame base (romSize b (H*chunks G M)) (literals H G M b) m a h⟩
  · intro P R K machine
    exact DescentStaticWordColumn.mount base (romSize b (H*chunks G M)) (literals H G M b) m fit machine
  · intro x
    have h : x.val < romSize b n := by dsimp [romSize];omega
    change DescentStaticWordColumn.image base (literals H G M b) m (romSize b n) (base+x.val)=_
    rw [DescentStaticWordColumn.read _ _ _ _ h]
    simp only [literals, dite_eq_left x.isLt]
  · intro p
    let u : Fin n := row H G M p
    have hu := u.isLt
    have loc : 2^b+u.val < romSize b n := by dsimp [romSize];omega
    change DescentStaticWordColumn.image base (literals H G M b) m (romSize b n) (base+2^b+u.val)=_
    rw [Nat.add_assoc, DescentStaticWordColumn.read _ _ _ _ loc]
    simp [literals, n, DescentSeedSignedBroadcast.finRead, u, (row H G M p).isLt,
      show ¬2^b+u.val < 2^b by omega, show 2^b+u.val < 2^b+span n by omega]
  · intro p
    let u : Fin n := row H G M p
    have hu := u.isLt
    have loc : (2^b+span n)+u.val < romSize b n := by dsimp [romSize];omega
    change DescentStaticWordColumn.image base (literals H G M b) m (romSize b n) (base+2^b+span n+u.val)=_
    rw [show base+2^b+span n+u.val = base+(2^b+span n+u.val) by omega,
      DescentStaticWordColumn.read _ _ _ _ loc]
    simp [literals, n, DescentSeedSignedBroadcast.finRead, u, (row H G M p).isLt,
      show ¬2^b+span n+u.val < 2^b by omega, show ¬2^b+span n+u.val < 2^b+span n by omega]

end
end Hierarchy.DescentResetStemHeaders

end OAI
