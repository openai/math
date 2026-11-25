import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentPhysicalOrder

namespace OAI
/-! # Stable in-word compaction of real scalar-node and operand fields -/
namespace Hierarchy.DescentPackedLocalAtoms
open DescentSIMDLookup DescentPhysicalOrder DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {W K a b M H r w : ℕ}

def present (bit : Fin W→Cell 1) := Finset.univ.filter (fun j=>bit j≠0)
def earlier (bit : Fin W→Cell 1) (j : Fin W) := ((present bit).filter (·<j)).card

theorem strict (bit : Fin W→Cell 1) {x y : Fin W} (live : bit x≠0) (before : x<y) :
    earlier bit x<earlier bit y := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (show (present bit).filter (·<x)⊆(present bit).filter (·<y) from
    fun i h=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1,(Finset.mem_filter.mp h).2.trans before⟩)).mpr
  exact ⟨x,Finset.mem_filter.mpr ⟨by simpa [present] using live,before⟩,by simp⟩

theorem earlier_inj (bit : Fin W→Cell 1) {x y : Fin W} (hx : bit x≠0) (hy : bit y≠0)
    (eqn : earlier bit x=earlier bit y) : x=y := by
  rcases lt_trichotomy x y with lt|eq|gt
  · exact ((strict bit hx lt).ne eqn).elim
  · exact eq
  · exact ((strict bit hy gt).ne eqn.symm).elim

/-- The search is over the fixed small local chart. Its output depends only
on the two short source words. -/
def field (K : ℕ) (bit : Fin W→Cell 1) (value : Fin W→Cell a) (t : Fin K) : Cell a :=
  if h : ∃j,bit j≠0 ∧ earlier bit j=t.val then value h.choose else 0

theorem field_at (bit : Fin W→Cell 1) (value : Fin W→Cell a) (j : Fin W) (alive : bit j≠0)
    (t : Fin K) (eqn : earlier bit j=t.val) : field K bit value t=value j := by
  have good : ∃i,bit i≠0 ∧ earlier bit i=t.val:=⟨j,alive,eqn⟩
  rw [field,dite_eq_left good,earlier_inj bit good.choose_spec.1 alive (good.choose_spec.2.trans eqn.symm)]

def pack (a W K : ℕ) (mask : Cell (1*W)) (raw : Cell (a*W)) : Cell (a*K) :=
  encode a K (field K ((encode 1 W).symm mask) ((encode a W).symm raw))

private theorem enc_zero (c l : ℕ) : encode c l (fun _=>0)=0 := by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin l=>(0:Cell c))).val=0
  simp []

theorem pack_zero (a W K : ℕ) : pack a W K 0 0=0 := by
  have empty : (encode 1 W).symm 0=fun _=>0 := (encode 1 W).injective (by simp [enc_zero])
  change encode a K _=0
  rw [←enc_zero a K]
  congr 1
  funext j
  simp [empty,field]

theorem true_digit {X : Type} [Fintype X] (ids : X↪Fin W) (small : Fintype.card X≤K)
    (bit : Fin W→Cell 1) (value : Fin W→Cell a) (active : ∀j,bit j≠0 ↔ ∃x,ids x=j) (u : X) :
    let index := (physical (ids.trans Fin.valEmbedding) u).castLE small
    digit a index.val (pack a W K (encode 1 W bit) (encode a W value)).val=(value (ids u)).val := by
  intro index
  have image : (present bit).filter (· < ids u)=(Finset.univ.filter (fun v=>ids v < ids u)).map ids := by
    ext j
    simp only [present,Finset.mem_filter,Finset.mem_univ,true_and,active,Finset.mem_map]
    constructor
    · rintro ⟨⟨v,rfl⟩,less⟩;exact ⟨v,less,rfl⟩
    · rintro ⟨v,less,rfl⟩;exact ⟨⟨v,rfl⟩,less⟩
  have eqn : earlier bit (ids u)=index.val := by
    rw [earlier,image,Finset.card_map]
    exact (physical_val (ids.trans Fin.valEmbedding) u).symm
  simp only [pack,Equiv.symm_apply_apply,digit_encode]
  rw [field_at bit value (ids u) ((active _).mpr ⟨_,rfl⟩) index eqn]

/-- One immutable dictionary reorders a whole local field at every resident
lane. The very same mask is used for role, arity, per-operand and width data. -/
theorem issued (T : Tables) (mask raw : Expr) (out : ℕ) (fits : DescentPackedZip.Fits T mask raw (1*W) (a*W) M out w)
    (room : out+H*chunks r M<2^w) (x : Fin H→Fin r→Cell (1*W)) (y : Fin H→Fin r→Cell (a*W)) :
    (code T mask raw out H r M w).Spec (fun m=>Static T (pack a W K) M m ∧ Source mask x M m ∧ Source raw y M m)
      (fun before after=>after=image out (H*chunks r M) (T.read mask raw) before ∧
        ∀j : Row H r M,after (out+(row H r M j).val)=((data (fun h g=>pack a W K (x h g) (y h g)) j).val:ℕ))
      (4+(H*chunks r M)*(2*(T.read mask raw).work+4)) ∧ CheapCode (code T mask raw out H r M w) :=
  DescentPackedZip.spec T mask raw out fits room _ (pack_zero ..) x y

end
end Hierarchy.DescentPackedLocalAtoms

end OAI
