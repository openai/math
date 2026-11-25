import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskCompile
import OAI.Computability.NearSquareRoot.InterchangeROMEffectiveSeries

/-! # Collecting compiled native comparison stripes

One parked copy of the parent header serves every selected pair. The compiled
list of syntactic ranks determines the physical order of the output stripes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMMaskCompile

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROMAddress Space CommonRegisters GeneratorSyntax LoomRegisters

noncomputable def collect (kernel : Cmd) (b n : ℕ) (ranks : List ℕ) : Cmd :=
  seriesCommand (fun j => compiled kernel (numeric b n j j)) ranks

theorem collect_within (kernel : Cmd) : ∃ R, ∀ b n ranks, Within R (collect kernel b n ranks) := by
  obtain ⟨T,ht⟩ := uniform_registers kernel
  exact ⟨max 3 T,fun b n ranks => series_within (le_max_left ..) _ _ (fun j =>
    RegisterSelect.within_mono (le_max_right ..) _ (ht (numeric b n j j)))⟩

theorem effective_collect {X : Type} [Primcodable X] {b n : X → ℕ} {ranks : X → List ℕ}
    (kernel : Cmd) (hb : Computable b) (hn : Computable n) (hr : Computable ranks) :
    Effective ltr fun x => collect kernel (b x) (n x) (ranks x) :=
  InterchangeROM.effective_series (effective_numeric kernel (hb.comp Computable.fst)
    (hn.comp Computable.fst) Computable.snd Computable.snd) hr

def height (b n : ℕ) (h : Header) : ℕ := size (tally b)+4*size (tally n)+size h+5

private theorem height_bound (b n j : ℕ) (h : Header) (hj : j < n) :
    size (numeric b n j j,h) ≤ height b n h := by
  simp only [numeric,height,size_prod,size_tally,tally_length]
  omega

private theorem output_size (q : ℕ → Tree) (l : List ℕ) (cap : ℕ)
    (good : ∀ j ∈ l, (q j).count ≤ cap) : (Task.forest q l).count ≤ (cap+1)*l.length+1 := by
  induction l with
  | nil => simp [Task.forest,Tree.count]
  | cons j l ih =>
    have hc := good j (by simp)
    have hl := ih (fun i hi => good i (by simp [hi]))
    rw [Task.forest_cons,Tree.count,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

private theorem sameClock {A : Type} (v u : ℕ) (l : List A) :
    seriesClock v (fun _ : A => u) l = (45*v+u+7)*l.length+60*v+10 := by
  simp [seriesClock,costSum,List.map_const',Nat.mul_comm]

/-- All field computations have the same input header. A large encoded
header polynomial is paid once per field in time and once total in space. -/
theorem collect_bounded (kernel : Cmd) (K d : ℕ) :
    ∃ C D : ℕ, ∀ b n (ranks : List ℕ) (h : Header) (y : ℕ → Tree) N env deck base,
      DeckCap base deck → (∀ j ∈ ranks, j < n) → (∀ j ∈ ranks, (y j).count ≤ 4*N+1) →
      (∀ j ∈ ranks, ∀ dr,
        let z := desc (numeric b n j j,h)
        Fits env kernel (pile 0 (send z) dr) (pile 0 (y j) dr) (K*(N+(size z+1)^d+1))) →
      let U := C*(N+(height b n h+1)^D+1)
      BoundedFits env (collect kernel b n ranks) (pile 0 (send h) deck)
        (pile 0 (Task.forest y ranks) deck)
        ((45*size h+U+7)*ranks.length+60*size h+10)
        (base+60*size h+(4*N+2)*ranks.length+U+11)
        (60*size h+U+10) := by
  obtain ⟨C,D,child⟩ := compiled_bounded kernel K d
  refine ⟨C,D,?_⟩
  intro b n ranks h y N env deck base hd valid output scan
  let U := C*(N+(height b n h+1)^D+1)
  let op (j : ℕ) := compiled kernel (numeric b n j j)
  let val : {j // j ∈ ranks} → ℕ := Subtype.val
  have runChild (j : {j // j ∈ ranks}) dr s (hs : DeckCap s dr) :
      BoundedFits env (op (val j)) (pile 0 (send h) dr) (pile 0 (y (val j)) dr) U (s+U) U := by
    have run := child (numeric b n j j) h (y j) N env dr s hs (scan j j.property dr)
    have le := height_bound b n j h (valid j j.property)
    have pay : C*(N+(size (numeric b n j j,h)+1)^D+1) ≤ U :=
      Nat.mul_le_mul_left _ (by gcongr)
    exact run.mono pay (Nat.add_le_add_left pay s) pay
  have all := series_bounded_at (op ∘ val) (send h) (y ∘ val) (fun _ => U) U U env runChild
    ranks.attach deck base hd
  have mapRanks : ranks.attach.map val = ranks := by simp [val]
  rw [← InterchangeROM.series_map, mapRanks] at all
  have forestRank : Task.forest (y ∘ val) ranks.attach = Task.forest y ranks := by
    calc
      _ = Task.forest y (ranks.attach.map val) := (Task.forest_map ..).symm
      _ = _ := congrArg (Task.forest y) mapRanks
  rw [forestRank,sameClock,List.length_attach] at all
  have vol := output_size y ranks (4*N+1) output
  change (Task.forest y ranks).count ≤ (4*N+2)*ranks.length+1 at vol
  exact all.mono le_rfl (by change base+60*size h+_+U+10 ≤ _; omega) le_rfl

end InterchangeROMMaskCompile

end NearSquareRoot
end Computability
end OAI
