import OAI.LinearAlgebra.SpectralBooks.SignedProgramFields
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramUnary

/-! # Unique local certificates for decoding the signed machine -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine

abbrev slotsCount (n : ℕ) := 3+n*(8+5*n)

def Table.slot {n : ℕ} (t : Table n) (frame : Fin (n+1)) (j : Fin (slotsCount n)) : Unary.Slot n :=
  (t.fields frame.val)[j.val]'(by rw [Table.length_fields]; exact j.isLt) |>.map (bounded n)

def Table.Fits {n : ℕ} (t : Table n) (frame : Fin (n+1)) : Prop :=
  ∀ v, some v ∈ t.fields frame.val → v ≤ n

private theorem emit_le_of_mem {v : ℕ} {fs : List (Option ℕ)} (h : some v ∈ fs) : v ≤ (emit fs).length := by
  induction fs with
  | nil => simp at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [ProgramCode.unary]
    · have hh := ih h
      cases a <;> simp [emit, ProgramCode.unary] at * <;> omega

theorem serialize_slot {n : ℕ} (t : Table n) (f : Fin (n+1)) (hfit : t.Fits f) :
    Unary.serialize (t.slot f) = emit (t.fields f.val) := by
  unfold Unary.serialize
  let fs := t.fields f.val
  have hlen : fs.length = slotsCount n := t.length_fields f.val
  have he : List.ofFn (t.slot f) = fs.map (Option.map (bounded n)) := by
    apply List.ext_getElem
    · simp [hlen]
    · intros; simp [Table.slot,fs]
  rw [he,List.flatMap_map]
  apply List.flatMap_congr
  rintro (_ | v) hv
  · rfl
  · simp [Unary.emit,bounded,Nat.min_eq_right (hfit v hv)]

abbrev Marks (n : ℕ) := Fin (slotsCount n+1) → Fin (n+1) → Bool
abbrev DecodeWitness (n : ℕ) := Table n × Fin (n+1) × Marks n

/-- The frame is checked by the consumed length: its header occupies
`frame+1` bits and its body occupies `frame` bits. -/
def Accepts {n : ℕ} (input : Fin n → Bool) (w : DecodeWitness n) : Prop :=
  let t := w.1
  let f := w.2.1
  let mark := w.2.2
  t.Canonical ∧ ProgramCode.WellFormed t.program ∧ t.Fits f ∧
    Unary.LocalCheck input (t.slot f) (fun i j ↦ mark i j = true) ∧
    ∀ j, mark (Fin.last _) j = true → j.val = 2*f.val+1

private theorem accept_parts {n : ℕ} {x : Fin n → Bool} {w : DecodeWitness n} (hw : Accepts x w) :
    ProgramCode.decode (List.ofFn x) = some w.1.program ∧
      w.2.1.val = (emit w.1.bodyFields).length := by
  rcases w with ⟨t,f,m⟩
  obtain ⟨_,hg,hfit,hlocal,hframe⟩ := hw
  obtain ⟨e,he,hmarks⟩ := (Unary.localCheck_iff _ _ _).mp hlocal
  have hend := hframe _ ((hmarks (Fin.last _) _).mpr rfl)
  have hlen := Unary.last_cursor he
  rw [serialize_slot t f hfit, Table.fields, emit_cons, List.length_append] at hlen
  simp only [Fin.val_zero, Nat.zero_add, ProgramCode.unary, List.length_append,
    List.length_replicate,List.length_singleton] at hlen
  change (e (Fin.last (slotsCount n))).val = 2*f.val+1 at hend
  have ff : f.val = (emit t.bodyFields).length := by omega
  have hp := (Unary.exists_trace_iff x 0 (t.slot f)).mp ⟨e,he⟩
  rw [serialize_slot t f hfit, ff, ProgramCode.emit_fields_eq_encode] at hp
  obtain ⟨payload,hpayload⟩ : ProgramCode.encode t.program <+: List.ofFn x := by simpa using hp
  exact ⟨ProgramCode.decode_eq_some_iff.mpr ⟨hg,payload,hpayload.symm⟩,ff⟩

/-- Any accepting certificate yields the program that the universal interpreter uses. -/
theorem Accepts.decode {n : ℕ} {x : Fin n → Bool} {w : DecodeWitness n} (hw : Accepts x w) :
    ProgramCode.decode (List.ofFn x) = some w.1.program := (accept_parts hw).1

private theorem exists_accepting {n : ℕ} {x : Fin n → Bool} {p : Program}
    (hp : ProgramCode.decode (List.ofFn x) = some p) : ∃ w, Accepts x w ∧ w.1.program = p := by
  let t := fromProgram n p
  have hprog := fromProgram_correct hp
  rw [List.length_ofFn] at hprog
  change t.program = p at hprog
  obtain ⟨hg,payload,hprefix⟩ := ProgramCode.decode_eq_some_iff.mp hp
  have hh : emit (t.fields (emit t.bodyFields).length) <+: List.ofFn x := by
    rw [ProgramCode.emit_fields_eq_encode,hprog]
    exact ⟨payload,hprefix.symm⟩
  have hb := hh.length_le
  rw [List.length_ofFn] at hb
  have hframe : (emit t.bodyFields).length ≤ n := by
    rw [Table.fields,emit_cons,List.length_append] at hb
    omega
  let f : Fin (n+1) := ⟨(emit t.bodyFields).length, by omega⟩
  have hfit : t.Fits f := fun _ hv ↦ (emit_le_of_mem hv).trans hb
  have hs := Unary.existsUnique_marks_iff x (t.slot f)
  rw [serialize_slot t f hfit] at hs
  obtain ⟨m,hm,_⟩ := hs.mpr hh
  refine ⟨(t,f,m),⟨?_,hprog ▸ hg,hfit,hm,?_⟩,hprog⟩
  · change t = fromProgram n t.program
    rw [hprog]
  · intro j hj
    obtain ⟨e,he,hmarks⟩ := (Unary.localCheck_iff _ _ _).mp hm
    have hlast := Unary.last_cursor he
    rw [serialize_slot t f hfit,Table.fields,emit_cons,List.length_append] at hlast
    rw [(hmarks _ _).mp hj]
    simp [ProgramCode.unary, f] at hlast ⊢
    omega

theorem accepts_unique {n : ℕ} {x : Fin n → Bool} {u v : DecodeWitness n}
    (hu : Accepts x u) (hv : Accepts x v) : u = v := by
  obtain ⟨t,f,m⟩ := u
  obtain ⟨t',f',m'⟩ := v
  obtain ⟨hp,hf⟩ := accept_parts hu
  obtain ⟨hp',hf'⟩ := accept_parts hv
  have he : t.program = t'.program := Option.some.inj (hp.symm.trans hp')
  have ht : t = t' := hu.1.trans ((congrArg (fromProgram n) he).trans hv.1.symm)
  subst t'
  have heq : f = f' := Fin.ext (hf.trans hf'.symm)
  subst f'
  have h₁ := hu.2.2.2.1
  have h₂ := hv.2.2.2.1
  obtain ⟨e,htrace,hemark⟩ := (Unary.localCheck_iff _ _ _).mp h₁
  obtain ⟨e',htrace',hemark'⟩ := (Unary.localCheck_iff _ _ _).mp h₂
  obtain rfl := Unary.trace_unique htrace htrace'
  have h : m = m' := funext₂ fun i j ↦ Bool.eq_iff_iff.mpr ((hemark i j).trans (hemark' i j).symm)
  subst m'
  rfl

/-- Every successfully decoded program contributes one parse witness, including
when the unconsumed suffix is nonempty. Invalid prefixes contribute none. -/
theorem decode_iff_unique_witness {n : ℕ} (x : Fin n → Bool) (p : Program) :
    ProgramCode.decode (List.ofFn x) = some p ↔ ∃! w, Accepts x w ∧ w.1.program = p := by
  constructor
  · intro hp
    obtain ⟨w,hw,hp'⟩ := exists_accepting hp
    exact ⟨w, ⟨hw,hp'⟩, fun _ hu ↦ accepts_unique hu.1 hw⟩
  · rintro ⟨w,⟨hw,rfl⟩,_⟩
    exact hw.decode

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
