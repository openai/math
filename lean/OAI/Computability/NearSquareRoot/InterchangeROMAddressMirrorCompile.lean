import OAI.Computability.NearSquareRoot.InterchangeROMAddressMirrorNative
import OAI.Computability.NearSquareRoot.InterchangeROMAddressEffective

/-! # Effective specialization of a physical native field reversal -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMMirror

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Loom
  IntegerMultiplication.Adic NearSquareRoot.Space
  NearSquareRoot.InterchangeROMAddress CommonRegisters RegisterWitness GeneratorSyntax

/-- Install a unary location literal beside the parent header, project it to
three physical shapes, and pass the outstanding stream through untouched. -/
def selectHeader (core : Cmd) (place : Location) : Cmd :=
  splitRoot 0 (fun _ => .pass)
    (((Task.prepare 0 (send place)).join ((pack 0).join core)).join (pack 0))

def projectTime (K d : ℕ) (place : Location) (h : Header) :=
  5*size place + K*(size (place,h)+1)^d + 20

private theorem exists_projector :
    ∃ core : Cmd, ∃ K d : ℕ, ∀ (place : Location) (h : Header) stream env deck,
      Fits env (selectHeader core place) (pile 0 (.fork (send h) stream) deck)
        (pile 0 (.fork (send (projection (place,h))) stream) deck) (projectTime K d place h) := by
  obtain ⟨u,⟨d,C,hbound⟩,c,D,hc⟩ := projection_poly
  refine ⟨c,D*(C+1),d,?_⟩
  intro place h stream env deck
  let saved := pile 0 stream deck
  have push := Task.fits_prepare 0 (send place) env (pile 0 (send h) saved)
  have packed := fits_pack (send place) (send h) saved 0 env
  have run := hc (place,h) env saved
  have finish := fits_pack (send (projection (place,h))) stream deck 0 env
  have pre := fits_pair (c:=fun _ => .pass) ((push.join (packed.join run)).join finish)
  refine pre.mono ?_
  have hh := hbound (place,h)
  have pos : 1 ≤ (size (place,h)+1)^d := Nat.one_le_pow _ _ (by omega)
  have upper : D*(u (place,h)+1) ≤ D*(C+1)*(size (place,h)+1)^d := by
    rw [Nat.mul_assoc,Nat.add_mul,Nat.one_mul]
    exact Nat.mul_le_mul_left _ (by omega)
  unfold projectTime size at *
  omega

/-- A constant across all radices, extents, slots and templates. -/
noncomputable def projector : Cmd := exists_projector.choose

theorem projector_fits :
    ∃ K d : ℕ, ∀ (place : Location) (h : Header) stream env deck,
      Fits env (selectHeader projector place) (pile 0 (.fork (send h) stream) deck)
        (pile 0 (.fork (send (projection (place,h))) stream) deck) (projectTime K d place h) :=
  exists_projector.choose_spec

def selectAndRun (core kernel : Cmd) (place : Location) : Cmd :=
  (selectHeader core place).join kernel

/-- Each parameter-dependent instruction consists of a literal installation
and two fixed native routines. -/
noncomputable def compiled (place : Location) : Cmd := selectAndRun projector command place

theorem uniform_registers : ∃ R : ℕ, ∀ place, Within R (compiled place) := by
  obtain ⟨R,hR,hp,hm⟩ : ∃ R : ℕ, 0 < R ∧ Within R projector ∧ Within R command := by
    exact ((Filter.eventually_gt_atTop (0 : ℕ)).and ((RegisterSelect.within_eventually projector).and
      (RegisterSelect.within_eventually command))).exists
  exact ⟨R, fun place => ⟨splitRoot_within.mpr ⟨hR,trivial,trivial,
    ⟨⟨(prepare_within _).mpr hR,⟨hR,hp⟩⟩,hR⟩⟩,hm⟩⟩

/-- A location descriptor for the P192 compiler may be supplied completely
numerically, before the input width or any spectator shape is known. -/
def numericLocation (p n : ℕ) (slot : Bool × ℕ) : Location :=
  (slot.1,tally p,tally n,tally slot.2,tally (n-slot.2-1))

theorem location_numeric {J : Type} {n : ℕ} (ord : J ≃ Fin n) (p : ℕ) (s : Spot J) :
    location ord p s = numericLocation p n (s.1,(ord s.2).val) := rfl


theorem effective_select {X : Type} [Primcodable X] {l : X → Location} (hl : Computable l)
    (core kernel : Cmd) : Effective ltr (fun x => selectAndRun core kernel (l x)) := by
  have atom : Effective ltr (fun a : Bool => Task.prepare 0 (send a)) := by
    apply (Computable.cond Computable.id (Computable.const (file ltr (Task.prepare 0 (send true))))
      (Computable.const (file ltr (Task.prepare 0 (send false))))).of_eq
    intro x
    cases x <;> rfl
  have lit := emit_pair (atom.comp (Computable.fst.comp hl)) (emit_cuts.comp (Computable.snd.comp hl))
  have body := (lit.join ((effective_const ltr (pack 0)).join (effective_const ltr core))).join
    (effective_const ltr (pack 0))
  have node : Effective ltr (fun x => selectHeader core (l x)) :=
    (InterchangeROM.computable_nodeFile.comp body).of_eq (fun x => InterchangeROM.nodeFile_file _)
  exact node.join (effective_const ltr kernel)

theorem computable_location {X : Type} [Primcodable X] {p n : X → ℕ} {s : X → Bool × ℕ}
    (hp : Computable p) (hn : Computable n) (hs : Computable s) :
    Computable (fun x => numericLocation (p x) (n x) (s x)) := by
  let k := fun x => (s x).2
  have loc : Computable k := Computable.snd.comp hs
  exact (Computable.fst.comp hs).pair ((computable_tally.comp hp).pair
    ((computable_tally.comp hn).pair ((computable_tally.comp loc).pair
      (computable_tally.comp (Primrec.nat_sub.to_comp.comp (Primrec.nat_sub.to_comp.comp hn loc)
        (Computable.const 1))))))

theorem effective_compiled {X : Type} [Primcodable X] {p n : X → ℕ} {s : X → Bool × ℕ}
    (hp : Computable p) (hn : Computable n) (hs : Computable s) :
    Effective ltr fun x => compiled (numericLocation (p x) (n x) (s x)) :=
  effective_select (computable_location hp hn hs) projector command

/-- The fixed projector and the reversible row segmentation run on the same
input stream, with a single live deck protected beneath both phases. -/
theorem compiled_fits :
    ∃ K d C : ℕ, ∀ {A : Type} {p f : ℕ} [NeZero p] {P S : Tape} {s : Series A}
      (e : Slot s P (line p f) S) (_ : 2 ≤ p) (_ : solid P) (_ : solid S)
      (place : Location) (h : Header)
      (_ : projection (place,h) = (shape P,shape (field p f),shape S))
      (v : A → Tree) env deck base, DeckCap base deck →
      let initial := Tree.fork (send h) (stripe s v)
      let input := Tree.fork (send (shape P,shape (field p f),shape S)) (stripe s v)
      let prep := projectTime K d place h
      let run := C*(input.count+s.count+1)
      BoundedFits env (compiled place) (pile 0 initial deck) (pile 0 (stripe s (v ∘ (e.tune mirror).symm)) deck)
        (prep+run+2) (base+max (initial.count+prep) run) (max (prep+1) run) := by
  obtain ⟨K,d,pre⟩ := projector_fits
  obtain ⟨C,post⟩ := native_command
  refine ⟨K,d,C,?_⟩
  intro A p f inst P S s e hp hP hS place h eq v env deck base hdeck
  let initial := Tree.fork (send h) (stripe s v)
  let input := Tree.fork (send (shape P,shape (field p f),shape S)) (stripe s v)
  let T := projectTime K d place h
  let U := C*(input.count+s.count+1)
  let cap := base+max (initial.count+T) U
  have a := pre place h (stripe s v) env deck
  rw [eq] at a
  have ready : BoundedFits env (selectHeader projector place) (pile 0 initial deck) (pile 0 input deck) T cap T :=
    BoundedFits.of_fits a (fun j => by
      have h := hdeck.pile 0 initial j
      have k : initial.count+T ≤ max (initial.count+T) U := le_max_left ..
      change (letters (pile 0 initial deck) j).length + T ≤ base+max (initial.count+T) U
      omega) le_rfl
  have b := post e hp hP hS v env deck base hdeck
  exact ready.join (b.mono le_rfl (Nat.add_le_add_left (le_max_right ..) base)
    (le_max_right ..)) (le_max_left ..)

private theorem rack_solid (s : Tape) (h : solid s) (k : ℕ) : solid (Loom.Rack s k) := by
  induction k with
  | zero => exact fun _ e => False.elim (List.not_mem_nil e)
  | succ k ih => exact (solid_cat ..).mpr ⟨h,ih⟩

theorem sides_solid {J : Type} {n : ℕ} (ord : J ≃ Fin n) (P G B F : Tape)
    (p : solid P) (g : solid G) (b : solid B) (f : solid F) (slot : Spot J) :
    solid (preamble ord P G F slot) ∧ solid (appendix ord G B F slot) := by
  obtain ⟨s,j⟩ := slot
  cases s <;> simp [leftF,rightF,solid_cat,p,g,b,rack_solid F f]

private theorem field_solid' {p f : ℕ} (h : 2 ≤ p) : solid (field p f) := by
  induction f with
  | zero => exact fun _ e => False.elim (List.not_mem_nil e)
  | succ f ih => exact (solid_cons ..).mpr ⟨h,ih⟩

/-- The two runtime wrappers disappear at a native one-stop projection. -/
theorem compiled_slot :
    ∃ K d C : ℕ, ∀ {J : Type} [DecidableEq J] {n p f : ℕ} [NeZero p]
      (ord : J ≃ Fin n) (slot : Spot J) (P G B : Tape) (_ : solid P) (_ : solid G) (_ : solid B)
      (_ : 2 ≤ p) (v : Keys P G B J (Block p f) → Tree) env deck base, DeckCap base deck →
      let loc := location ord p slot
      let h := header f P G B
      let e := oneStop ord slot (P:=P) (G:=G) (B:=B) (p:=p) (j:=f)
      let rows := arrays ord (line p f) P G B
      let stream := stripe rows v
      let prep := projectTime K d loc h
      let run := C*((Tree.fork (send (projection (loc,h))) stream).count+rows.count+1)
      let original := Tree.fork (send h) stream
      BoundedFits env (compiled loc) (pile 0 original deck)
        (pile 0 (stripe rows (v ∘ (e.tune mirror).symm)) deck)
        (prep+run+2) (base+max (original.count+prep) run) (max (prep+1) run) := by
  obtain ⟨K,d,C,ok⟩ := compiled_fits
  refine ⟨K,d,C,?_⟩
  intro J decid n p f inst ord slot P G B hP hG hB hp v env deck base baseOK
  let eq := projection_correct ord p f P G B slot
  let both := sides_solid ord P G B (field p f) hP hG hB (field_solid' hp) slot
  simpa only [eq] using ok (oneStop ord slot) hp both.1 both.2 _ _ eq v env deck base baseOK

private theorem setup_dom (K d C : ℕ) :
    Dom size (fun z : Location × Header =>
      projectTime K d z.1 z.2 + C*(size (projection z)+2) + size z + 4) := by
  have base : Dom (@size (Location × Header) _) size := Dom.base _
  have loc : Dom size (fun z : Location × Header => size z.1) := base.mono (fun z => by change size z.1 ≤ size z.1 + size z.2 + 1; omega)
  have head := (((Dom.const _ 5).mul loc).add
    ((Dom.const _ K).mul ((base.add (Dom.const _ 1)).pow d))).add (Dom.const _ 20)
  exact ((head.add ((Dom.const _ C).mul (projection_poly.length.add (Dom.const _ 2)))).add base).add
    (Dom.const _ 4)

/-- A single header polynomial and linear scan price cover every selected
field, including changes to the radix, arity, and spectator tapes. -/
theorem compiled_linear :
    ∃ C d : ℕ, ∀ {A : Type} {p f : ℕ} [NeZero p] {P S : Tape} {s : Series A}
      (e : Slot s P (line p f) S) (_ : 2 ≤ p) (_ : solid P) (_ : solid S)
      (place : Location) (h : Header)
      (_ : projection (place,h) = (shape P,shape (field p f),shape S))
      (v : A → Tree) env deck base, DeckCap base deck →
      let stream := stripe s v
      let budget := C*((size (place,h)+1)^d + stream.count + s.count + 1)
      BoundedFits env (compiled place) (pile 0 (.fork (send h) stream) deck)
        (pile 0 (stripe s (v ∘ (e.tune mirror).symm)) deck) budget (base+budget) budget := by
  obtain ⟨K,d,C,ok⟩ := compiled_fits
  obtain ⟨j,E,hE⟩ := setup_dom K d C
  refine ⟨E+C+1,j,?_⟩
  intro A p f inst P S s e hp hP hS place h eq v env deck base hd
  have fit := ok e hp hP hS place h eq v env deck base hd
  rw [← eq] at fit
  let T := projectTime K d place h
  let M := (size (place,h)+1)^j
  let w := (stripe s v).count
  let G := size (projection (place,h))
  have bd := hE (place,h)
  change T + C*(G+2) + size (place,h) + 4 ≤ E*M at bd
  have hh : size h ≤ size (place,h) := by change size h ≤ size place + size h + 1; omega
  change BoundedFits env _ _ _
    (T+C*((G+w+1)+s.count+1)+2)
    (base+max ((size h+w+1)+T) (C*((G+w+1)+s.count+1)))
    (max (T+1) (C*((G+w+1)+s.count+1))) at fit
  let cost := (E+C+1)*(M+w+s.count+1)
  have a : T+C*((G+w+1)+s.count+1)+2 ≤ cost := by
    dsimp only [cost]
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] at bd ⊢
    omega
  have b : size h+w+1+T ≤ cost := by
    dsimp only [cost]
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] at bd ⊢
    omega
  change BoundedFits env _ _ _ cost (base+cost) cost
  exact fit.mono a (Nat.add_le_add_left (max_le b (by omega)) base) (max_le (by omega) (by omega))

end InterchangeROMMirror

end NearSquareRoot
end Computability
end OAI
