import OAI.Hierarchy.DescentSeedWideFlagProgram
import OAI.Hierarchy.DescentSeedPackedHeaderNumbers
import OAI.Hierarchy.DescentWideSeedHeader
import OAI.Hierarchy.DescentSeedRejectTable
import OAI.Hierarchy.DescentPackedRejectionImage
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! Seed count checks with payload-sized table keys in an independently addressed physical RAM. -/
namespace Hierarchy.DescentWideSeedFlags
open DescentInitialHost DescentSeedRoot DescentPackedSeed DescentSIMDLookup
open DescentTerminalPackedSeedFlags (predicate advice)
open Catalyst Computability.BorderVNP.Crossing Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory PrivateRAM ProtocolRAM
open ThreeFlat Routing Diagonal TraceBanks RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F A : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (R s payload bw : ℕ)

set_option quotPrecheck false
local notation "cnt" => DescentPackedSeed.rows X R s payload
local notation "lanes_" => DescentPackedSeed.multiplicity payload s
local notation "base_" => endInput X R s payload
local notation "tab" => dictionary X R s payload
local notation "src" => source X R s payload

variable (seed : Select X R s → A) (z : A → Bool)

def initial : Memory bw := initialMemory base_ fun a =>
  if a < (tab).base then initialMemory (headerWords X R s payload) (wideBase X payload bw (z ∘ seed)) a
  else (advice s lanes_ (a-(tab).base) : Word bw)

theorem lower {a : ℕ} (low : a < (tab).base) : initial X R s payload bw seed z a =
    initialMemory (headerWords X R s payload) (wideBase X payload bw (z ∘ seed)) a := by
  have inside : a < base_ := low.trans_le (Nat.le_add_right _ _)
  simp [initial,initialMemory,low,inside]

def pin (a : ℕ) (j : Fin (bw+1)) : A ⊕ Bool :=
  if a < (tab).base then
    if live : a < headerWords X R s payload then
      (wideHeaderPin X R s payload bw (⟨a,live⟩,j)).map seed id
    else .inr false
  else if a < base_ then .inr (TraceWords.bits (TraceBanks.wide (advice s lanes_ (a-(tab).base):Word bw)) j)
    else .inr false

theorem pin_at (arch : payload ≤ bw) (a : ℕ) (j : Fin (bw+1)) :
    (pin X R s payload bw seed a j).elim z id = TraceWords.bits (TraceBanks.wide (initial X R s payload bw seed z a)) j := by
  by_cases low : a < (tab).base
  · rw [lower X R s payload bw seed z low]
    by_cases live : a < headerWords X R s payload
    · have read := wide_headerPin_at X payload bw arch (z ∘ seed) (⟨a,live⟩,j)
      simp only [pin,ite_eq_left low,dite_eq_left live,initialMemory,ite_eq_left live]
      generalize wideHeaderPin X R s payload bw (⟨a,live⟩,j)=b at *
      cases b <;> exact read
    · simp [pin,low,live,initialMemory,TraceWords.bits,TraceBanks.wide]
  · by_cases inside : a < base_
    · simp [pin,initial,initialMemory,low,inside]
    · simp [pin,initial,initialMemory,low,inside,TraceWords.bits,TraceBanks.wide]

def countedAt {bw : ℕ} (m : Memory bw) := DescentPackedRejection.after (M:=lanes_) base_ (predicate s)
  (cells X (z ∘ seed)) m

theorem run (m : Memory bw) (held : ∀a < base_,m a=initial X R s payload bw seed z a)
    (wide : 2*digitsNeeded s ≤ payload) (room : base_+(cnt+1)<2^bw) :
    let o:=countedAt X R s payload seed z m
    (check X R s payload bw).Exec m o (4+(cnt+1)*66) ∧ CheapCode (check X R s payload bw) ∧
      (o (base_+cnt)=0 ↔ valid X (z ∘ seed)) ∧ ∀a,a < base_ ∨ base_+(cnt+1) ≤ a → o a=m a := by
  let f:=predicate s
  let vals:=cells X (z ∘ seed)
  have cap : cnt≤(src).size := Nat.le_pow_clog (by decide) _
  have before : (src).base+(src).size=(tab).base:=rfl
  have last : (tab).base+(tab).size=base_:=rfl
  have sf : (src).Fits bw base_:=⟨Nat.two_pow_pos _,by omega,by omega⟩
  have rf : (tab).Fits bw base_:=⟨Nat.two_pow_pos _,by omega,last.le⟩
  have data_ (i : PackedRow X R s payload) :
      m ((src).base+(row _ _ _ i).val)=((data vals i).val : Word bw) := by
    have small:=(row _ _ _ i).isLt.trans_le cap
    rw [held _ (by omega),lower X R s payload bw seed z (by omega)]
    exact wide_data_at X payload bw (z ∘ seed) i
  have table : DescentPackedRejection.Table (M:=lanes_) f tab m := by
    intro key
    have small : key.val < (tab).size:=key.isLt
    have inside : (tab).base+key.val < base_:=by omega
    have branch : ¬ (tab).base+key.val < (tab).base:=by omega
    have same : (key.val : Cell (digitsNeeded s*lanes_))=key:=Fin.ext (Fin.val_cast_of_lt key.isLt)
    rw [held _ inside]
    simp [initial,initialMemory,inside,branch,advice,same,f]
  have pos:=multiplicity_pos wide
  have zero : f 0=0:=by simp [f,predicate]
  have full:=DescentPackedRejection.exact_run src tab base_ f vals m zero pos sf rf cap rfl room data_ table
  have fits : 1<2^bw:=by omega
  have one : (1 : Word bw)≠0:=by
    intro eq
    have bad:=congrArg Fin.val eq
    simp [Nat.mod_eq_of_lt fits] at bad
  have accept : (∀v j,f (vals v j)=0) ↔ valid X (z ∘ seed) := by
    simp [f,vals,predicate,valid_iff]
  have measured:=full.2.1
  refine ⟨full.1,(DescentPackedRejection.run src tab base_ f vals m zero pos sf rf cap rfl room data_ table).2,?_,full.2.2⟩
  change DescentPackedRejection.after (M:=lanes_) base_ f vals m (base_+Fintype.card (Old X)*chunks (R*8) lanes_)=0 ↔ _
  rw [measured]
  by_cases good : valid X (z ∘ seed)
  · simp [accept.mpr good,good]
  · simp [mt accept.mp good,good,one]

end
end Hierarchy.DescentWideSeedFlags

end OAI
