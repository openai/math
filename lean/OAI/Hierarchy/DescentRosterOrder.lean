import OAI.Hierarchy.DescentContactNumbers
import OAI.Hierarchy.DescentContactCodes
import OAI.Hierarchy.DescentPackedWords
import OAI.Hierarchy.ProtocolRAMPortRanks
import Mathlib.Data.Nat.Pairing

namespace OAI
/-! # Shared host coordinates and their explicit local roster ranks -/

namespace Hierarchy.DescentRosterOrder
open DescentContactTree DescentContacts ProtocolRAMPortRanks
open scoped BigOperators Classical
noncomputable section
variable {V : Type} (host : V↪ℕ)

def optionDigit {Y : ℕ} : Option (Fin Y) ↪ ℕ where
  toFun := Option.elim' 0 (fun j=>j.val+1)
  inj' := by
    rintro (_|i) (_|j) hit
    · rfl
    · exact (Nat.noConfusion (show 0=j.val+1 from hit))
    · exact (Nat.noConfusion (show i.val+1=0 from hit))
    · exact congrArg some (Fin.ext (Nat.succ.inj hit))

def endpoint {Y : ℕ} : V×Endpoint Y↪ℕ :=
  (host.prodMap ((Nat.pairEquiv.toEmbedding.prodMap optionDigit).trans Nat.pairEquiv.toEmbedding)).trans Nat.pairEquiv.toEmbedding

variable {X : Type*} [Fintype X] (code : X↪ℕ)

def compact : X↪Fin (Fintype.card X) where
  toFun x := ((enumerate (fun _ : X=>1) code code.injective ⟨x,0⟩).cast (by simp))
  inj' := by
    intro x y eqn
    have eq':=congrArg Fin.val eqn
    change (enumerate (fun _ : X=>1) code code.injective ⟨x,0⟩).val =
      (enumerate (fun _ : X=>1) code code.injective ⟨y,0⟩).val at eq'
    exact congrArg Sigma.fst ((enumerate (fun _ : X=>1) code code.injective).injective (Fin.ext eq'))

@[simp] theorem compact_read (x : X) :
    (compact code x).val=(Finset.univ.filter fun y=>code y<code x).card := by
  change ProtocolRAMPortRanks.«prefix» (fun _ : X=>1) code x+0=_
  simp [ProtocolRAMPortRanks.«prefix»]

def directory {Z : Type*} (ord : Z↪ℕ) (roster : Finset Z) : ↥roster ↪ Node (codeHeight ↥roster) :=
  (compact ((Function.Embedding.subtype _).trans ord)).trans
    ((Fin.castLEEmb (Nat.le_pow_clog (by decide : 1<2) (Fintype.card ↥roster))).trans
      (DescentRotor.bitWord (codeHeight ↥roster)).symm.toEmbedding)

theorem directory_ord {Z : Type*} (ord : Z↪ℕ) (roster : Finset Z) (x : ↥roster) :
    (DescentRotor.bitWord (codeHeight ↥roster) (directory ord roster x)).val=
      (Finset.univ.filter (fun y : ↥roster=>ord y.val<ord x.val)).card := by
  let key := (Function.Embedding.subtype (fun z=>z∈roster)).trans ord
  let i : Fin (2^codeHeight ↥roster) := ⟨(compact key x).val,
    (compact key x).isLt.trans_le (Nat.le_pow_clog (by decide : 1<2) _)⟩
  change ((DescentRotor.bitWord (codeHeight ↥roster)) ((DescentRotor.bitWord (codeHeight ↥roster)).symm i)).val=_
  exact (congrArg Fin.val ((DescentRotor.bitWord (codeHeight ↥roster)).apply_symm_apply i)).trans <| by
    exact compact_read key x

end
end Hierarchy.DescentRosterOrder

end OAI
