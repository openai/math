import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMask
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskCompile

/-! # The shape-compiled mask for one chosen interchange field

The emitted constants are just the radix and the cuts. Inside the native record
stream, comparison of the selected pair depends on the two field coordinates
and is independent of the remaining slots and all three spectator tapes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Mask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  IntegerMultiplication.Port InterchangeAddress InterchangeROMAddress
  Space CommonRegisters GeneratorSyntax

abbrev parameter (b n j : ℕ) := InterchangeROMMaskCompile.numeric b n j j

noncomputable def command (b n j : ℕ) : Cmd :=
  InterchangeROMMaskCompile.compiled scanner (parameter b n j)

theorem effective {X : Type} [Primcodable X] {b n j : X → ℕ}
    (hb : Computable b) (hn : Computable n) (hj : Computable j) :
    Effective ltr (fun x => command (b x) (n x) (j x)) :=
  InterchangeROMMaskCompile.effective_numeric scanner hb hn hj hj

theorem within : ∃ R, ∀ b n j, Within R (command b n j) := by
  obtain ⟨R,h⟩ := InterchangeROMMaskCompile.uniform_registers scanner
  exact ⟨R,fun _ _ _ => h _⟩

noncomputable def maskRow {J : Type} {n b : ℕ} (ord : J ≃ Fin n)
    (P G B : Tape) (f : ℕ) (j : J) :=
  stripe (arrays ord (line b f) P G B) fun a =>
    mark (InterchangeSpectralStep.direction (number (a.2.1 j)) (number (a.2.2.2.1 j)))

private def request {J : Type} {n : ℕ} (ord : J ≃ Fin n)
    (P G B : Tape) (b f : ℕ) (j : J) : Request b where
  before := preamble ord P G (field b f) (false,j)
  between := silence ord G (field b f) (false,j) (true,j)
  after_ := appendix ord G B (field b f) (true,j)
  width := f
  recordWidth := 1
  contents _ := .atom false

private theorem solid_request {J : Type} {n b : ℕ} (ord : J ≃ Fin n) (j : J)
    (P G B : Tape) (hp : solid P) (hg : solid G) (hs : solid B) (hb : 2 ≤ b) (f : ℕ) :
    let r := request ord P G B b f j
    solid r.before ∧ solid r.between ∧ solid r.after_ := by
  have rack (s : ℕ) : solid (Rack (field b f) s) := fun k h => (source_radix _ _ _ _ h) ▸ hb
  simp only [request,preamble_false,silence_false_true,appendix_true,solid_cat,leftF,rightF]
  exact ⟨⟨hp,rack _⟩,⟨rack _,hg,rack _⟩,rack _,hs⟩

private theorem request_layout {J : Type} [DecidableEq J] {n b : ℕ} [NeZero b]
    (ord : J ≃ Fin n) (P G B : Tape) (f : ℕ) (j : J) :
    let r := request ord P G B b f j
    r.rows.count = (arrays ord (line b f) P G B).count ∧ output r = maskRow (b:=b) ord P G B f j := by
  let early : Lag.early (ranking ord) (false,j) (true,j) := .inl ⟨rfl,rfl⟩
  let ax := twoStops (p:=b) (j:=f) (P:=P) (G:=G) (B:=B) ord (false,j) (true,j) early
  refine ⟨ax.view.cost.symm,?_⟩
  dsimp only [output,request,Request.rows,stock,maskRow]
  rw [ax.view.packet]
  apply congrArg (stripe _)
  funext a
  have e := (two_use ord (false,j) (true,j) early a (a.2.1 j) (a.2.2.2.1 j)).1
  change ax.pair a = (a.2.1 j,a.2.2.2.1 j) at e
  exact congrArg (fun (p : Block b f × Block b f) => mark (InterchangeSpectralStep.direction (number p.1) (number p.2))) e

/-- The same parameter-free scanner acts on each member of a list of pivot
descriptors. Its output already has the original physical record order. -/
theorem scanner_native :
    ∃ K : ℕ, ∀ {J : Type} [DecidableEq J] {n b : ℕ} (ord : J ≃ Fin n) (j : J)
      (P G B : Tape) (_ : 2 ≤ b) (_ : solid P) (_ : solid G) (_ : solid B)
      (f : ℕ) (env : Env) (deck : Deck),
      let q := parameter b n (ord j).val
      let h := header f P G B
      let d := InterchangeROMMaskCompile.desc (q,h)
      Fits env scanner (pile 0 (send d) deck) (pile 0 (maskRow (b:=b) ord P G B f j) deck)
        (K*((arrays ord (line b f) P G B).count + (size d+1)^2+1)) := by
  obtain ⟨K,run⟩ := scanner_fits
  refine ⟨K,?_⟩
  intro J inst n b ord j P G B hb hp hg hs f env deck
  dsimp only
  let : NeZero b := ⟨by omega⟩
  let r := request ord P G B b f j
  have hrs := solid_request ord j P G B hp hg hs hb f
  have out := request_layout (b:=b) ord P G B f j
  have desc : InterchangeROMMaskCompile.desc (parameter b n (ord j).val,header f P G B) =
      InterchangeROMLeafMasksShape.descriptor r :=
    InterchangeROMMaskCompile.desc_numeric ord P G B b f j j
  rw [desc,← out.1,← out.2]
  exact run r hb hrs.1 hrs.2.1 hrs.2.2 env deck

/-- A single uniform polynomial for literal and shape setup, plus one linear
scan of the output cells. Width zero yields one field value. -/
theorem command_bounded :
    ∃ C D : ℕ, ∀ {J : Type} [DecidableEq J] {n b : ℕ} (ord : J ≃ Fin n) (j : J)
      (P G B : Tape) (_ : 2 ≤ b) (_ : solid P) (_ : solid G) (_ : solid B)
      (f : ℕ) (env : Env) (deck : Deck) (base : ℕ), DeckCap base deck →
      let q := parameter b n (ord j).val
      let h := header f P G B
      let w := C * ((arrays ord (line b f) P G B).count + (size (q,h)+1)^D + 1)
      BoundedFits env (command b n (ord j).val) (pile 0 (send h) deck)
        (pile 0 (maskRow (b:=b) ord P G B f j) deck) w (base+w) w := by
  obtain ⟨K,run⟩ := scanner_native
  obtain ⟨C,D,proj⟩ := InterchangeROMMaskCompile.compiled_bounded scanner K 2
  exact ⟨C,D, fun ord j P G B hb hp hg hs f env deck base hd =>
    proj _ _ _ _ env deck base hd (run ord j P G B hb hp hg hs f env deck)⟩

end InterchangeROMRepair.Physical.Mask

end NearSquareRoot
end Computability
end OAI
