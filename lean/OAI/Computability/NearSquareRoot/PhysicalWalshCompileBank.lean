import OAI.Computability.NearSquareRoot.PhysicalWalshCompile
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntax
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect

/-! # Effectively generated bank operations

The parallel cut is one fixed scan receiving a unary cut position. The
compiler emits a literal for the cut and places it before the runtime bank.
Thus a single finite set of commands suffices for every template width.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code Space PhysicalWalsh GeneratorSyntax

variable {S T D : Type} [Codec S] [Codec T] [Codec D]

private theorem scans_of_fits {c : Cmd} {f : S → T} (C : ℕ)
    (h : ∀ a env r b, DeckCap b r → Fits env c (pile 0 (send a) r) (pile 0 (send (f a)) r) (C*(size a+1))) :
    Scans c f := by
  refine ⟨C+1,fun a env r b hr => ?_⟩
  apply (BoundedFits.of_fits (h a env r b hr) (cap := b+(C+1)*(size a+1))
    (depth := (C+1)*(size a+1)) _ _).mono _ le_rfl le_rfl
  · intro j
    by_cases hj : j = 0
    · subst j; rw [letters_here,List.length_append,Tree.spell_length]
      have := hr 0
      change size a + _ + _ ≤ _
      rw [Nat.succ_mul]; omega
    · rw [pile_far _ _ (Ne.symm hj)]; have := hr j; rw [Nat.succ_mul]; omega
  all_goals rw [Nat.succ_mul]; omega

/-- A fixed easy stack procedure can be hardwired, together with its bound. -/
theorem exists_scanner {f : S → T} (h : Easy f) : ∃ c : Cmd, Scans c f := by
  obtain ⟨c,C,h⟩ := h
  exact ⟨c,scans_of_fits C (fun a env r _ _ => h a env r)⟩

/-- Attach an operand literal to a stack command. -/
def withLiteral (z : Tree) (c : Cmd) : Cmd := ((Task.prepare 0 z).join (pack 0)).join c

/-- The literal's size is a constant for the chosen program. The input itself
is scanned with a coefficient independent of its length. -/
theorem Scans.withLiteral {c : Cmd} {f : D × S → T} (h : Scans c f) (z : D) :
    Scans (withLiteral (send z) c) (fun a : S => f (z,a)) := by
  obtain ⟨C,r⟩ := h
  let A := 5*size z+5
  let B := size z+3
  apply scans_of_fits (A+C*B)
  intro a env p b hbcap
  let put := (Task.fits_prepare 0 (send z) env (pile 0 (send a) p)).join
    (fits_pack (send z) (send a) p 0 env)
  have body : Fits env c (pile 0 (send (z,a)) p) (pile 0 (send (f (z,a))) p) (C*(size (z,a)+1)) :=
    (r (z,a) env p b hbcap).fits
  apply (put.join body).mono
  have ha : A ≤ A*(size a+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hb : size (z,a)+1 ≤ B*(size a+1) := by
    rw [size_prod]; dsimp only [B]; rw [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega
  have hc := Nat.mul_le_mul_left C hb
  change 5*size z+1+2+C*(size (z,a)+1)+2 ≤ _
  rw [Nat.add_mul,Nat.mul_assoc]
  dsimp only [A] at ha ⊢
  omega

private def dynamicCut {H R : Type} (x : Tally × (H × List R)) :=
  PhysicalWalshBank.split x.1.length x.2

private theorem easy_dynamicCut {H R : Type} [Codec H] [Codec R] : Easy (dynamicCut (H := H) (R := R)) := by
  have cut : Easy (fun a : Tally × (H × List R) => cutLists (a.1,a.2.2)) := by apply easy_cut; fun_prop
  have header : Easy (fun a : Tally × (H × List R) => a.2.1) := by fun_prop
  exact (header.pair (cut.compose Easy.fst)).pair (header.pair (cut.compose Easy.snd))

theorem effective_tally_prepare [Fintype Ltr] : Effective ltr (fun i : ℕ => Task.prepare 0 (send (tally i))) := by
  let root := Task.prepare 0 (send (tally 0))
  let step := (Task.prepare 0 (send ())).join (pack 0)
  have h := Computable.nat_rec (σ := File) Computable.id (Computable.const (file ltr root))
    (primrec_joinFile.to_comp.comp (Computable.snd.comp Computable.snd) (Computable.const (file ltr step))).to₂
  apply h.of_eq
  intro i
  change Nat.rec (file ltr root) (fun _ acc => joinFile acc (file ltr step)) i = file ltr (Task.prepare 0 (send (tally i)))
  induction i with
  | zero => rfl
  | succ i ih =>
    change joinFile _ _ = _
    rw [ih,joinFile_file,tally_succ]
    rfl

/-- Every varying bank cut is emitted by one computable compiler, including
all its sites. Only the three fixed datatype operations are hardwired. -/
theorem effectiveBankRegisters [Fintype Ltr] (H R : Type) [Codec H] [Codec R] :
    ∃ bank : BankCode, BankOK bank H R ∧ Effective ltr bank.split ∧
      ∃ n, 0 < n ∧ (∀ i, CommonRegisters.Within n (bank.split i)) ∧
        CommonRegisters.Within n bank.swap ∧ CommonRegisters.Within n bank.finish := by
  obtain ⟨cut,hcut⟩ := exists_scanner (easy_dynamicCut (H := H) (R := R))
  obtain ⟨swap,hswap⟩ := exists_scanner (Easy.exchange (X := H × List R) (Y := H × List R))
  obtain ⟨finish,hfinish⟩ := exists_scanner <| (Easy.exchange (X := H × List R) (Y := H × List R)).compose PhysicalWalshBank.easy_combine
  refine ⟨⟨fun i => withLiteral (send (tally i)) cut,swap,finish⟩,⟨fun i => ?_,hswap,hfinish⟩,?_,?_⟩
  · simpa only [dynamicCut,tally_length] using hcut.withLiteral (tally i)
  · exact (effective_tally_prepare.join (effective_const ltr (pack 0))).join (effective_const ltr cut)

  · obtain ⟨n, hn, hc, hs, hf⟩ := ((Filter.eventually_gt_atTop 0).and
      ((RegisterSelect.within_eventually cut).and ((RegisterSelect.within_eventually swap).and
        (RegisterSelect.within_eventually finish)))).exists
    exact ⟨n,hn,fun _ => ⟨⟨(RegisterWitness.prepare_within _).mpr hn,hn⟩,hc⟩,hs,hf⟩

theorem effectiveBank [Fintype Ltr] (H R : Type) [Codec H] [Codec R] :
    ∃ bank : BankCode, BankOK bank H R ∧ Effective ltr bank.split := by
  obtain ⟨bank,valid,effective,_⟩ := effectiveBankRegisters H R
  exact ⟨bank,valid,effective⟩

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
