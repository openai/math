import OAI.Hierarchy.ProbePayloadPlacement
import OAI.Hierarchy.TaggedShorterStageDirectory

namespace OAI
/-! # Fixed supergroup addresses for the physical ends of reported positive links -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open AdaptiveProbe TaggedShorterSupergroups
open scoped Classical BigOperators

abbrev Role (k attempts : ℕ) := ColumnLayer k ⊕ Fin attempts

/-- A color of the socket table determines the actual layer at that socket.
Every acquired long link has both endpoints on the center layer. -/
def layer {k attempts : ℕ} : Role k attempts → ColumnLayer k := Sum.elim id (fun _ => none)

def copies (k attempts : ℕ) := Fintype.card (Bool × Role k attempts)

theorem copies_eq (k attempts : ℕ) : copies k attempts=2*(1+2*k+attempts) := by
  simp [copies,Role,ColumnLayer,Fintype.card_option,Nat.mul_comm,Nat.add_comm]

private def splitSide {m : ℕ} : (Fin m ⊕ Fin m) ↪ Fin m × Bool where
  toFun := Sum.elim (fun p => (p,false)) (fun p => (p,true))
  inj' := by
    rintro (i|i) (j|j) eq <;> simp_all

variable {h W k attempts H : ℕ}

def owner (s : StageColumns h (2^W)) : AllGroups h (2^W) := ⟨s.1,s.2.1⟩

def socketPort (s : StageColumns h (2^W)) : Fin (stageAt h (2^W) s.1).span :=
  (splitSide s.2.2).1

def socketTag (s : StageColumns h (2^W)) (r : Role k attempts) : Fin (copies k attempts) :=
  Fintype.equivFin _ ((splitSide s.2.2).2,r)

def offset (s : StageColumns h (2^W)) (r : Role k attempts) :
    Fin (reserved h W (copies k attempts) (owner s)) :=
  finProdFinEquiv (socketPort s,socketTag s r)

theorem offset_val (s : StageColumns h (2^W)) (r : Role k attempts) :
    (offset s r).val=(socketTag s r).val+copies k attempts*(socketPort s).val := rfl

/-- This address exists before a term is supplied. It names a stage socket, its
physical side, and either a public horizontal layer or a specific purchase attempt. -/
def raw : StageColumns h (2^W) × Role k attempts ↪
    Σ g : AllGroups h (2^W), Fin (reserved h W (copies k attempts) g) where
  toFun x := ⟨owner x.1,offset x.1 x.2⟩
  inj' := by
    rintro ⟨⟨t,g,v⟩,r⟩ ⟨⟨t',g',v'⟩,r'⟩ eq
    have owners := congrArg Sigma.fst eq
    obtain ⟨rfl,group⟩ := Sigma.mk.inj_iff.mp owners
    have sameGroup : g=g' := eq_of_heq group
    subst g'
    have packed := eq_of_heq (Sigma.mk.inj_iff.mp eq).2
    have ports := finProdFinEquiv.injective packed
    have role := (Fintype.equivFin (Bool × Role k attempts)).injective (congrArg Prod.snd ports)
    have indexEq := congrArg Prod.fst ports
    have sideEq := congrArg Prod.fst role
    have side : v=v' := splitSide.injective (Prod.ext indexEq sideEq)
    have letter : r=r' := congrArg (fun z : Bool × Role k attempts=>z.2) role
    subst v'; subst r'; rfl

variable (dir : Directory (reserved h W (copies k attempts)) H)

def packed : StageColumns h (2^W) × Role k attempts ↪ Fin dir.groups × Fin H :=
  raw.trans dir.place

theorem packed_read (s : StageColumns h (2^W)) (r : Role k attempts) :
    packed dir (s,r)=(dir.group (owner s),dir.slot (owner s) (offset s r)) := rfl

/-- All transport subslots use the same public bin. Within the bin the physical
controller adds the subslot to the fixed scaled port address. -/
def expanded (lanes : ℕ) : (StageColumns h (2^W) × Role k attempts) × Fin lanes ↪
    Fin dir.groups × Fin (H*lanes) where
  toFun z := ((packed dir z.1).1,finProdFinEquiv ((packed dir z.1).2,z.2))
  inj' := by
    rintro ⟨p,i⟩ ⟨q,j⟩ e
    have inner := finProdFinEquiv.injective (congrArg Prod.snd e)
    have groups := congrArg Prod.fst e
    have slots := congrArg Prod.fst inner
    have laneEq := congrArg Prod.snd inner
    exact Prod.ext ((packed dir).injective (Prod.ext groups slots)) laneEq

theorem expanded_address (lanes : ℕ) (s : StageColumns h (2^W)) (r : Role k attempts) (i : Fin lanes) :
    (expanded dir lanes ((s,r),i)).2.val=(dir.base (owner s)+(offset s r).val)*lanes+i.val := by
  change i.val+lanes*(dir.base (owner s)+(offset s r).val)=_
  ac_rfl

theorem address_width (W pad h ell : ℕ) :
    2^superAddress W pad h*2^ell=(2:ℕ)^superAddress W (pad+ell) h := by
  rw [←pow_add]
  congr 1
  unfold superAddress
  omega

/-- Buying all supergroups once at port granularity, then expanding each
port into transport subslots, charges the lane count only once. -/
theorem affordable (h W k attempts ell : ℕ) :
    let pad := 2*copies k attempts
    ∃ dir : Directory (reserved h W (copies k attempts)) (2^superAddress W pad h),
      dir.groups*2^superAddress W (pad+ell) h ≤
        (2*(((2*rounds (2^W)+1)*4^(rounds (2^W)+1)*2^h)*copies k attempts)+
          2^superAddress W pad h)*2^ell := by
  intro pad
  have room : 2*copies k attempts≤2^pad := Nat.lt_two_pow_self.le
  obtain ⟨dir,price⟩ := purchase_stages h W (copies k attempts) pad room
  refine ⟨dir,?_⟩
  rw [←address_width,←Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ price

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
