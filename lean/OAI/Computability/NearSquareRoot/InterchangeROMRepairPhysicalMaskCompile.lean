import OAI.Computability.NearSquareRoot.InterchangeROMAddressMirrorCompile

/-! # Emitting physical selected-field comparison programs

The machine installs the two field positions and radix as literals, projects the
parent header onto the selected pair, and tail-calls a fixed comparison scanner.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMMaskCompile

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  InterchangeROMAddress Space CommonRegisters RegisterWitness GeneratorSyntax

abbrev Params := Tally × Cuts

def numeric (b n early late : ℕ) : Params :=
  (tally b,tally early,tally (n-early-1),tally late,tally (n-late-1))

def desc (p : Params × Header) : Tally × Header :=
  (p.1.1,one ((p.1.1,p.2),p.1.2))

theorem desc_poly : Poly desc :=
  (by fun_prop : Poly (fun p : Params × Header => p.1.1)).pair
    ((by fun_prop : Poly (fun p : Params × Header => ((p.1.1,p.2),p.1.2))).compose one_poly)

theorem desc_numeric {J : Type} {n : ℕ} (ord : J ≃ Fin n) (P G B : Tape) (b f : ℕ)
    (i j : J) :
    desc (numeric b n (ord i).val (ord j).val,header f P G B) =
      (tally b,header f (preamble ord P G (field b f) (false,i))
        (silence ord G (field b f) (false,i) (true,j))
        (appendix ord G B (field b f) (true,j))) :=
  congrArg (fun h => (tally b,h)) (one_header ord P G B b f i j)

/-- The same projector for all possible physical headers and emitted literals. -/
private theorem projection_code :
    ∃ c : Cmd, ∃ M j : ℕ, ∀ z : Params × Header, ∀ env deck,
      Fits env c (pile 0 (send z) deck) (pile 0 (send (desc z)) deck) (M*(size z+1)^j) := by
  obtain ⟨u,⟨j,C,h⟩,c,D,fit⟩ := desc_poly
  refine ⟨c,D*(C+1),j,?_⟩
  intro z env deck
  apply (fit z env deck).mono
  have p : 1 ≤ (size z+1)^j := Nat.one_le_pow _ _ (by omega)
  have b := h z
  rw [Nat.mul_assoc,Nat.add_mul,Nat.one_mul]
  exact Nat.mul_le_mul_left _ (by omega)

noncomputable def projector : Cmd := projection_code.choose

noncomputable def compiled (kernel : Cmd) (q : Params) : Cmd :=
  (Task.prepare 0 (send q)).join ((pack 0).join (projector.join kernel))

theorem uniform_registers (kernel : Cmd) : ∃ R : ℕ, ∀ q, Within R (compiled kernel q) := by
  obtain ⟨R,hR,hp,hk⟩ := ((Filter.eventually_gt_atTop (0 : ℕ)).and
    ((RegisterSelect.within_eventually projector).and (RegisterSelect.within_eventually kernel))).exists
  exact ⟨R,fun q => ⟨(prepare_within _).mpr hR,⟨hR,⟨hp,hk⟩⟩⟩⟩

theorem computable_numeric {X : Type} [Primcodable X] {b n e l : X → ℕ}
    (hb : Computable b) (hn : Computable n) (he : Computable e) (hl : Computable l) :
    Computable fun x => numeric (b x) (n x) (e x) (l x) := by
  have after {r : X → ℕ} (hr : Computable r) :
      Computable fun x => tally (n x-r x-1) :=
    computable_tally.comp (Primrec.nat_sub.to_comp.comp (Primrec.nat_sub.to_comp.comp hn hr)
      (Computable.const 1))
  exact (computable_tally.comp hb).pair ((computable_tally.comp he).pair
    ((after he).pair ((computable_tally.comp hl).pair (after hl))))

theorem effective_compiled {X : Type} [Primcodable X] {q : X → Params} (kernel : Cmd)
    (hq : Computable q) : Effective ltr fun x => compiled kernel (q x) := by
  have emit := emit_pair (emit_tally.comp (Computable.fst.comp hq))
    (emit_cuts.comp (Computable.snd.comp hq))
  exact emit.join ((effective_const ltr (pack 0)).join
    ((effective_const ltr projector).join (effective_const ltr kernel)))

theorem effective_numeric {X : Type} [Primcodable X] {b n e l : X → ℕ} (kernel : Cmd)
    (hb : Computable b) (hn : Computable n) (he : Computable e) (hl : Computable l) :
    Effective ltr fun x => compiled kernel (numeric (b x) (n x) (e x) (l x)) :=
  effective_compiled kernel (computable_numeric hb hn he hl)

/-- Literal insertion and projection add only a polynomial header setup.
The caller's existing frame is respected by both phases. -/
theorem compiled_bounded (kernel : Cmd) (K d : ℕ) :
    ∃ C D : ℕ, ∀ (q : Params) (h : Header) (v : Tree) (N : ℕ) env deck base,
      DeckCap base deck →
      Fits env kernel (pile 0 (send (desc (q,h))) deck) (pile 0 v deck)
        (K*(N+(size (desc (q,h))+1)^d+1)) →
      let w := C*(N+(size (q,h)+1)^D+1)
      BoundedFits env (compiled kernel q) (pile 0 (send h) deck) (pile 0 v deck)
        w (base+w) w := by
  obtain ⟨M,j,project⟩ := projection_code.choose_spec
  have zsize : Dom (@size (Params × Header) _) size := Dom.base _
  have headerCost : Dom size (fun z : Params × Header =>
      6*size z + M*(size z+1)^j + K*(size (desc z)+1)^d + K + 20) :=
    (((((Dom.const _ 6).mul zsize).add ((Dom.const _ M).mul
      ((zsize.add (Dom.const _ 1)).pow j))).add ((Dom.const _ K).mul
      ((desc_poly.length.add (Dom.const _ 1)).pow d))).add (Dom.const _ K)).add (Dom.const _ 20)
  obtain ⟨D,E,estimate⟩ := headerCost
  refine ⟨E+K,D,?_⟩
  intro q h v N env deck base hd scan
  have emit := Task.fits_prepare 0 (send q) env (pile 0 (send h) deck)
  have pair := fits_pack (send q) (send h) deck 0 env
  have phase := emit.join (pair.join ((project (q,h) env deck).join scan))
  let H := (size (q,h)+1)^D
  let T := 6*size (q,h) + M*(size (q,h)+1)^j + K*(size (desc (q,h))+1)^d + K + 20 + K*N
  have charge := estimate (q,h)
  change _ ≤ E*H at charge
  have total : T ≤ (E+K)*(N+H+1) := by
    simp only [T,Nat.mul_add,Nat.add_mul,Nat.mul_one] at *
    omega
  let U := 5*size q + (1 + (M*(size (q,h)+1)^j + K*(N+(size (desc (q,h))+1)^d+1) + 2) + 2) + 2
  change Fits env (compiled kernel q) _ _ U at phase
  have room : size h + U ≤ T := by
    simp only [U,T,Nat.mul_add,Nat.mul_one,size_prod]
    omega
  have fits : BoundedFits env (compiled kernel q) (pile 0 (send h) deck) (pile 0 v deck)
      U (base+T) T := BoundedFits.of_fits phase (fun k => by
        have hc := hd.pile 0 (send h) k
        change (letters (pile 0 (send h) deck) k).length ≤ base+size h at hc
        omega) (by omega)
  exact fits.mono ((Nat.le_add_left U (size h)).trans (room.trans total)) (Nat.add_le_add_left total base) total

end InterchangeROMMaskCompile

end NearSquareRoot
end Computability
end OAI
