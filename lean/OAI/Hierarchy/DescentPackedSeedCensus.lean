import OAI.Hierarchy.DescentSeedNativeCells
import OAI.Hierarchy.DescentPackedCensusPorts
import OAI.Hierarchy.DescentSeedWorld
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Initial packed census words from the fixed original physical graph -/

namespace Hierarchy.DescentInitialHost.PackedSeed
open DescentSixParty DescentColonies StarKeys Catalyst DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option Elab.async false

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
variable {R s : ℕ} (c : (initialGroup X R s).Choice)
local notation "W" => (initialGroup X R s).state c
local notation "N" => X.network.copyGraph
local notation "A" => markedInput X
variable {J : Type} [Fintype J] [DecidableEq J] {l : ℕ} (digits : Fin R≃J×Block l)

private theorem original_mem (j : Fin R) (e : (A).graph.Edge) :
    (⟨j, e⟩ : (W).graph.Edge) ∈ (W).core ↔ e ∈ (A).core := by
  change (⟨j, e⟩ : Σ _ : Fin R, (A).graph.Edge) ∈
    Finset.univ.sigma (fun _ : Fin R => (A).core) ↔ e ∈ (A).core
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and]

private def placeCable (g : J) (v : Site N) (x : Block l) :
    Original X v →
      PackedCensus.Out (W) (seedPos X c digits) (seedBlock X c digits) (g,v) x :=
  fun e=>⟨⟨digits.symm (g,x),e.val⟩,by
    refine ⟨⟨?_,?_⟩,?_⟩
    · change ((digits (digits.symm (g,x))).1,(A).graph.src e.val)=(g,v)
      have first : (digits (digits.symm (g, x))).1 = g :=
        congrArg (fun pair : J × Block l => pair.1) (digits.apply_symm_apply (g, x))
      exact Prod.ext first e.property.1
    · exact congrArg Prod.snd (digits.apply_symm_apply (g,x))
    · exact (original_mem X c (digits.symm (g, x)) e.val).2 e.property.2⟩

theorem outgoing (g : J) (v : Site N) (x : Block l) :
    blockMass (W).graph (seedPos X c digits) (seedBlock X c digits)
      (fun u=>((W).core.filter (fun e=>(W).graph.src e=u)).card) (g,v) x =
      Fintype.card (Original X v) := by
  rw [←PackedCensus.out_eq]
  apply Fintype.card_congr
  apply Equiv.symm
  apply Equiv.ofBijective (placeCable X c digits g v x)
  constructor
  · intro a b h
    exact Subtype.ext (congrArg (fun t=>t.val.2) h)
  · rintro ⟨⟨j,e⟩,⟨atV,atX⟩,live⟩
    change ((digits j).1,(A).graph.src e)=(g,v) at atV
    change (digits j).2=x at atX
    have old := (original_mem X c j e).1 live
    have here : (digits j).1 = g :=
      congrArg (fun pair : J × Site X.network.copyGraph => pair.1) atV
    have hj : j = digits.symm (g, x) := digits.eq_symm_apply.mpr (Prod.ext here atX)
    subst j
    exact ⟨⟨e,congrArg Prod.snd atV,old⟩,rfl⟩

theorem truthful (marked : Bool) (wire hist : ℕ) (g : J) (v : Site N) (x : Block l) :
    value X marked wire hist s v =
    if marked then blockMass (W).graph (seedPos X c digits) (seedBlock X c digits)
      (fun u=>((W).core.filter (fun e=>(W).graph.src e=u)).card) (g,v) x
    else blockMass (W).graph (seedPos X c digits) (seedBlock X c digits)
      ((W).siteUnits (seedHub X c) (seedRecords X c) wire 256 hist) (g,v) x := by
  cases marked
  · exact (seed_mass X c digits wire hist (g,v) x).symm
  · exact (outgoing X c digits g v x).symm

end
end Hierarchy.DescentInitialHost.PackedSeed

namespace Hierarchy.DescentInitialHost.PackedSeed
open DescentSixParty DescentColonies StarKeys Catalyst DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
set_option Elab.async false
noncomputable section
variable {F : Type} [Field F] {k p H L M w : ℕ} (X : Approximation F k p)
variable {R s l : ℕ} (c : (initialGroup X R s).Choice)
variable {J : Type} [Fintype J] [DecidableEq J] (digits : Fin R ≃ J × Block l)
variable (host : Site X.network.copyGraph ↪ Fin H)

def word (X : Approximation F k p) (host : Site X.network.copyGraph ↪ Fin H)
    (marked : Bool) (wire hist s b l : ℕ) (p : Row H L M) : Word w :=
  (data (fun v (_ : Fin L)=>fixedRow X host marked wire hist s b l v) p).val

def mount {count : ℕ} (base : ℕ) (f : Fin count→Word w) (m : Memory w) (addr : ℕ) : Word w :=
  if inRange : base≤addr ∧ addr<base+count then f ⟨addr-base,by omega⟩ else m addr

theorem mounted {count : ℕ} (base : ℕ) (f : Fin count→Word w) (m : Memory w) (j : Fin count) :
    mount base f m (base+j.val)=f j := by simp [mount,j.isLt]

def headerMem (X : Approximation F k p) (host : Site X.network.copyGraph ↪ Fin H)
    (wire hist s b l M L base : ℕ) (m : Memory w) : Memory w :=
  let count := H*chunks L M
  let sector := fun (marked : Bool) (i : Fin count)=>word X host marked wire hist s b l ((row H L M).symm i)
  mount (base+count) (sector true) (mount base (sector false) m)

theorem header_read (wire hist s b l base : ℕ) (m : Memory w) (flag : Bool) (p : Row H L M) :
    headerMem X host wire hist s b l M L base m
      ((if flag then base+H*chunks L M else base)+(row H L M p).val)=word X host flag wire hist s b l p := by
  have small := (row H L M p).isLt
  cases flag
  · simp only [headerMem,Bool.false_eq_true,↓reduceIte]
    rw [mount, dite_eq_right (by omega),mounted,Equiv.symm_apply_apply]
  · simp [headerMem,mounted]

theorem real_row (marked : Bool) (wire hist b : ℕ) (v : Site X.network.copyGraph) (g : J) :
    fixedRow X host marked wire hist s b l (host v) =
    encode b (2^l) (fun x=>((if marked then blockMass ((initialGroup X R s).state c).graph (seedPos X c digits) (seedBlock X c digits)
      (fun u=>(((initialGroup X R s).state c).core.filter (fun e=>((initialGroup X R s).state c).graph.src e=u)).card) (g,v) x
    else blockMass ((initialGroup X R s).state c).graph (seedPos X c digits) (seedBlock X c digits)
      (((initialGroup X R s).state c).siteUnits (seedHub X c) (seedRecords X c) wire 256 hist) (g,v) x:ℕ):Cell b)) := by
  have hv : ∃u,host u=host v := ⟨v,rfl⟩
  simp only [fixedRow,dite_eq_left hv,host.injective hv.choose_spec]
  exact congrArg (encode b (2^l)) (funext (fun x=>congrArg (fun n : ℕ=>(n:Cell b))
    (truthful X c digits marked wire hist g v x)))

/-- A padded host has no incident wires or resident records in either census sector. -/
theorem padded_row (marked : Bool) (wire hist b : ℕ) (v : Fin H)
    (empty : ¬ ∃ u, host u = v) :
    fixedRow X host marked wire hist s b l v = 0 := by
  simp only [fixedRow, dite_eq_right empty]
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin (2 ^ l) => (0 : Cell b))).val = 0
  simp []

theorem header_bits (H L w unit : ℕ) (positive : 0<unit) (wide : 2*unit≤w) :
    (2*(H*chunks L (lanes w unit)))*w≤2*(H*w+4*H*L*unit) := by
  have charge:=volume H L w unit positive wide
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left 2 charge

end
end Hierarchy.DescentInitialHost.PackedSeed

end OAI
