import OAI.Hierarchy.DescentSeedCensusScan

import OAI.Hierarchy.DescentSeedCensusWords
import OAI.Hierarchy.DescentPackedCensusRAM

namespace OAI
/-! # A single fixed packed lookup scan writes all internal primitive seed labels -/
namespace Hierarchy.DescentPackedSeed.Primitive
open DescentSeedRoot DescentInitialHost DescentSixParty DescentPrimitivePalette DescentEpochTagKeys DescentSIMDLookup Catalyst
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {k p w s R : ℕ} (X : Approximation F k p)
local notation "H" => Fintype.card (Old X)
local notation "d" => digitsNeeded s
local notation "inputBits" => d*8
local notation "b" => roleBits s
local notation "M" => pieces w s
local notation "n" => H*chunks R M

namespace Spaced
variable {laneCount : ℕ}

theorem read_primitive {cw : ℕ} (fit : s<2^cw) (live : 0<laneCount) (c : (initialGroup X R s).Choice)
    (out : ℕ) (mem : Memory w) (wordRoom : b*laneCount≤w)
    (issued : ∀p : Row H R laneCount,mem (out+(row H R laneCount p).val)=
      ((data (fun v j=>entry s (sitePlan X v) (bundles X (selectBit X cw c) v j)) p).val:Word w))
    (v : Old X) (j : Fin R) :
    let p:=position ((Fintype.equivFin _) v) j live
    digit b (lane j live).val (mem (out+(row H R laneCount p).val)).val=((census s).store (seedRole X R c j (.inl v))).val := by
  intro p
  let z:=lane j live
  have atJ : p.2.val*laneCount+z.val=j.val:=Nat.div_add_mod' ..
  have good:=atJ.trans_lt j.isLt
  have same : (⟨_,good⟩:Fin R)=j:=Fin.ext atJ
  rw [issued p,Fin.val_cast_of_lt ((data _ p).isLt.trans_le (Nat.pow_le_pow_right (by decide) wordRoom))]
  unfold data
  rw [digit_encode,dite_eq_left good,same]
  simpa [p,position,sitePlan] using role_at X fit c v j

end Spaced

abbrev stamp (start : ℕ) (m : Memory w) := Spaced.stamp (laneCount:=M) (s:=s) (R:=R) X start m

abbrev Static (T : Tape) (m : Memory w) := Spaced.Static (laneCount:=M) (s:=s) (R:=R) X T m

theorem static_read (start src : ℕ) (prior : Memory w) :
    Static (s:=s) (R:=R) X (tape start H R M s src) (stamp (R:=R) (s:=s) X start prior) :=
  Spaced.static_read (laneCount:=M) (s:=s) (R:=R) X start src prior

theorem retained (start src : ℕ) (old : Memory w) (a : ℕ) (ha : a<start) :
    stamp (s:=s) (R:=R) X start old a=old a :=
  Spaced.retained (laneCount:=M) (s:=s) (R:=R) X start src old a ha

theorem read (T : Tape) (out : ℕ) (fit : Room T out inputBits b M H R s w) (mem : Memory w)
    (data_ : Fin H→Fin R→Cell inputBits) (haveOld : ∀p : Row H R M,mem (T.source.base+(row H R M p).val)=((data data_ p).val:Word w))
    (fixed : Static (R:=R) (s:=s) X T mem) (p : Row H R M) :
    (spread T).eval mem ((row H R M p).val:Word w)=
      ((data (fun v j=>entry s (sitePlan X v) (data_ v j)) p).val:Word w) :=
  Spaced.read X T out fit mem data_ haveOld fixed p

theorem native (start out : ℕ) (_wide : 16*d≤w) (sel : Select X R s→Bool) (mem : Memory w)
    (earlier : publicWords X+H*chunks R M ≤ start)
    (old : ∀p : Row H R M,mem (publicWords X+(row H R M p).val)=
      ((data (bundles X sel) p).val:Word w))
    (fit : Room (tape start H R M s (publicWords X)) out inputBits b M H R s w) :
    let T:=tape start H R M s (publicWords X)
    let init:=stamp (s:=s) (R:=R) X start mem
    let dst:=image out n (spread T) init
    (scan w out n (spread T)).Exec init dst (4+60*n) ∧
      (∀p : Row H R M,dst (out+(row H R M p).val)=
        ((data (fun v j=>entry s (sitePlan X v) (bundles X sel v j)) p).val:Word w)) ∧
      (∀i<out,dst i=init i) ∧ CheapCode (scan w out n (spread T)) :=
  Spaced.native X start out sel mem earlier old fit

theorem read_primitive {cw : ℕ} (fit : s<2^cw) (live : 0<M) (c : (initialGroup X R s).Choice)
    (out : ℕ) (mem : Memory w) (wordRoom : b*M≤w)
    (issued : ∀p : Row H R M,mem (out+(row H R M p).val)=
      ((data (fun v j=>entry s (sitePlan X v) (bundles X (selectBit X cw c) v j)) p).val:Word w))
    (v : Old X) (j : Fin R) :
    let p:=position ((Fintype.equivFin _) v) j live
    digit b (lane j live).val (mem (out+(row H R M p).val)).val=((census s).store (seedRole X R c j (.inl v))).val :=
  Spaced.read_primitive X fit live c out mem wordRoom issued v j

end
end Hierarchy.DescentPackedSeed.Primitive

end OAI
