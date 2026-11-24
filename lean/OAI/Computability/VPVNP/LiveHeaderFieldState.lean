import OAI.Computability.VPVNP.LiveHeaderProgramFit
import OAI.Computability.VPVNP.LiveHeaderSingleRun

/-!
# Memory invariants for the sixteen incident-field stages

Each incident field has a descriptor stage and a consumer stage. All six
nonpadding payloads occupy disjoint public ranges. An unoccupied part of
an array retains its original scratch value, including the initial zero
exponent vector at the first group.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.Fields

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderDescriptors
open ChainAssignments CutSchedule LiveHeader PrimedInputRAM

variable {w d : ℕ}

/-- Enumerate the four incident fields on the left and then the four on the right in extraction
order. -/
def key : Fin 8 → Side × Field :=
  ![(.left,.exterior),(.left,.exponents),(.left,.config),(.left,.padding),
    (.right,.exterior),(.right,.exponents),(.right,.config),(.right,.padding)]

theorem key_inj : Function.Injective key := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem key_surj : Function.Surjective key := by
  rintro ⟨side,f⟩
  cases side <;> cases f <;> decide

/-- The stage number of the descriptor computation for the given incident-field ordinal. -/
def descId (k : Fin 8) : StageId := ⟨15+2*k.val,by have := k.isLt; rw [stage_count]; omega⟩
/-- The stage number of the bounded field scan immediately following its descriptor
computation. -/
def scanId (k : Fin 8) : StageId := ⟨16+2*k.val,by have := k.isLt; rw [stage_count]; omega⟩
/-- The descriptor stage that begins the indicated remaining field, or no stage once all eight
fields have run. -/
def startId (n : ℕ) : Option StageId := if h : n < 8 then some (descId ⟨n,h⟩) else none

@[simp] theorem stage_desc (k : Fin 8) : stage (descId k) = .descriptor (key k).1 (key k).2 := by
  fin_cases k <;> rfl

@[simp] theorem stage_scan (k : Fin 8) : stage (scanId k) = .scan (key k).1 (key k).2 := by
  fin_cases k <;> rfl

@[simp] theorem next_desc (k : Fin 8) : next (descId k) = some (scanId k) := by fin_cases k <;> rfl

@[simp] theorem next_scan (k : Fin 8) : next (scanId k) = startId (k.val+1) := by fin_cases k <;> rfl

@[simp] theorem start_at (k : Fin 8) : startId k.val = some (descId k) := by
  simp [startId,k.isLt]

/-- The source offset and length of one incident field for the group's actual width, phase, and
mode. -/
def interval (s : Sizes) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (side : Side) (f : Field) :=
  let W := incidentWidth (Δ := s.delta) side g
  span (shape side W tag.code.val (firstHalfFlag g) (decide (g.val+1 = 2^s.h+1))) W s.delta s.e s.config f

theorem interval_capacity (s : Sizes) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (side : Side) (f : Field) :
    (interval s g tag side f).2 ≤ s.capacity f :=
  occupied_le_capacity s f _ (cut_width_le_capacity s _)

theorem interval_inside (s : Sizes) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (side : Side) (f : Field)
    (he : 1+s.e ≤ s.delta) (hc : 1+s.config ≤ s.delta) :
    (interval s g tag side f).1+(interval s g tag side f).2 ≤ incidentWidth (Δ := s.delta) side g :=
  span_fit he hc (shape_fit (width_ge_block (s.h+1) s.delta _)) f

/-- Scalar and packed source words surviving from the earlier header stages. -/
structure Sources (s : Sizes) (base d : ℕ) (hw : 4 ≤ w) (advice : Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (m : Memory w) : Prop where
  headers : SiteHeaders d hw advice cuts g m
  width : ∀ side, (m (widthAddr base (if side = .left then .liveLeft else .liveRight))).val =
    incidentWidth (Δ := s.delta) side g
  mode : (m (tagAddr base)).val = tag.code.val
  half : m (flagAddr base .firstHalf) = encodeBit w (firstHalfFlag g)
  firstTail : m (firstTailAddr base) = encodeBit w (decide (g.val+1 = 2^s.h+1))

/-- Addresses read by later stages may contain any value at entry. All words
except the handoff tag, the descriptors, and the actually occupied payloads
must retain that value through the field suffix. -/
def Protected (s : Sizes) (base : ℕ) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (addr : ℕ) : Prop :=
  addr ≠ base ∧ addr ≠ offsetAddr base ∧ addr ≠ countAddr base ∧
  ∀ side f, f ≠ .padding → Allocated.Outside (dest s base side f) (interval s g tag side f).2 addr

/-- All nonpadding fields with index below the cursor have been copied. The
frame retains zero in each unused part of a payload array. -/
structure Image (s : Sizes) (base : ℕ) (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1)))
    (tag : Mode.Tag) (cursor : ℕ) (before m : Memory w) : Prop where
  copies : ∀ k : Fin 8, k.val < cursor → (key k).2 ≠ .padding →
    CopiedSlice (cuts (incidentCut (key k).1 g)) (interval s g tag (key k).1 (key k).2)
      (dest s base (key k).1 (key k).2) m
  frame : ∀ addr, Protected s base g tag addr → m addr = before addr

theorem Image.initial (s : Sizes) (base : ℕ) (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1)))
    (tag : Mode.Tag) (m : Memory w) : Image s base cuts g tag 0 m m := ⟨by omega,fun _ _ => rfl⟩

/-- Physical zero padding selected by the actual descriptor shape. -/
def ValidPadding (s : Sizes) (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (side : Side) :=
  Physical.ZeroSlice (cuts (incidentCut side g)) (interval s g tag side .padding)

/-- Writing a descriptor and consuming that one field cannot change any
other payload. Only the tag and descriptor words change on handoff. -/
structure FieldEffect (s : Sizes) (base : ℕ) (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1)))
    (tag : Mode.Tag) (side : Side) (f : Field) (before m : Memory w) : Prop where
  copy : f ≠ .padding → CopiedSlice (cuts (incidentCut side g)) (interval s g tag side f) (dest s base side f) m
  frame : ∀ addr, addr ≠ base → addr ≠ offsetAddr base → addr ≠ countAddr base →
    (f = .padding ∨ Allocated.Outside (dest s base side f) (interval s g tag side f).2 addr) →
    m addr = before addr

theorem before_destination (s : Sizes) (base : ℕ) (side : Side) (f : Field) (hf : f ≠ .padding) :
    base+14 < dest s base side f := by
  have h := (dest_bounds s base side f hf).1
  dsimp [adviceBase,rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase] at h
  omega

theorem Image.advance {s : Sizes} {base : ℕ} {cuts : AllCuts s.h s.delta} {g : Fin (2^(s.h+1))}
    {tag : Mode.Tag} {before m out : Memory w} (k : Fin 8) (img : Image s base cuts g tag k.val before m)
    (step : FieldEffect s base cuts g tag (key k).1 (key k).2 m out) : Image s base cuts g tag (k.val+1) before out := by
  constructor
  · intro i hi hf
    by_cases same : i = k
    · subst i
      exact step.copy hf
    · have hi' : i.val < k.val := by have hv : i.val ≠ k.val := fun he => same (Fin.ext he); omega
      apply (img.copies i hi' hf).congr
      intro j hj
      have hbase := before_destination s base (key i).1 (key i).2 hf
      apply step.frame _ (by omega) (by unfold offsetAddr; omega) (by unfold countAddr; omega)
      by_cases hpad : (key k).2 = .padding
      · exact Or.inl hpad
      · apply Or.inr
        have hne : ((key i).1,(key i).2) ≠ ((key k).1,(key k).2) := fun eq => same (key_inj eq)
        have h₁ := interval_capacity s g tag (key i).1 (key i).2
        have h₂ := interval_capacity s g tag (key k).1 (key k).2
        rcases dest_disjoint s base hf hpad hne with left | right <;> unfold Allocated.Outside <;> omega
  · intro addr ha
    rcases ha with ⟨hb,ho,hc,other⟩
    have hs := step.frame addr hb ho hc (by
      by_cases hpad : (key k).2 = .padding
      · exact Or.inl hpad
      · exact Or.inr (other _ _ hpad))
    exact hs.trans (img.frame addr ⟨hb,ho,hc,other⟩)

theorem Sources.congr {s : Sizes} {base d : ℕ} {hw : 4 ≤ w} {advice : Bits s.advice}
    {cuts : AllCuts s.h s.delta} {g : Fin (2^(s.h+1))} {tag : Mode.Tag} {m out : Memory w}
    (old : Sources s base d hw advice cuts g tag m) (sites : 2^d ≤ base)
    (frame : ∀ addr, addr ≠ base → addr ≠ offsetAddr base → addr ≠ countAddr base →
      addr < base+14 → out addr = m addr) : Sources s base d hw advice cuts g tag out := by
  constructor
  · intro v
    have h := v.isLt
    rw [frame v.val (by omega) (by unfold offsetAddr; omega) (by unfold countAddr; omega) (by omega), old.headers v]
  · intro side
    rw [← old.width side]
    congr 1
    apply frame <;> cases side <;> dsimp [widthAddr,countAddr,offsetAddr] <;> omega
  · rw [frame,old.mode]
    all_goals dsimp [tagAddr,countAddr,offsetAddr]; omega
  · rw [frame,old.half]
    all_goals dsimp [flagAddr,countAddr,offsetAddr]; omega
  · rw [frame,old.firstTail]
    all_goals dsimp [firstTailAddr,countAddr,offsetAddr]; omega

theorem Sources.afterField {s : Sizes} {base d : ℕ} {hw : 4 ≤ w} {advice : Bits s.advice}
    {cuts : AllCuts s.h s.delta} {g : Fin (2^(s.h+1))} {tag : Mode.Tag} {m out : Memory w}
    (old : Sources s base d hw advice cuts g tag m) (sites : 2^d ≤ base)
    (side : Side) (f : Field) (effect : FieldEffect s base cuts g tag side f m out) :
    Sources s base d hw advice cuts g tag out := by
  apply old.congr sites
  intro addr hb ho hc low
  apply effect.frame _ hb ho hc
  by_cases hpad : f = .padding
  · exact Or.inl hpad
  · exact Or.inr (Or.inl (low.trans (before_destination s base side f hpad)))

end LiveHeaderProgram.Fields

end VPVNP
end Computability
end OAI
