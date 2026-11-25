import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomPayload
import OAI.Computability.NearSquareRoot.InterchangeROMTableSpelling
import OAI.Computability.NearSquareRoot.ScheduleRegisterTable

/-! # Effective resource coefficients for the packed literal-table instructions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code InterchangeROMTable

private def spellingLimit (side : List ℕ × List ℕ → List ℕ) (tab : SpellingTable) :=
  tab.foldr (fun row prior => max (side row).length prior) 0

private theorem primrec_spellingLimit (side : List ℕ × List ℕ → List ℕ) (hs : Primrec side) :
    Primrec (spellingLimit side) :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.list_length.comp (hs.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- The byte lengths of valid tree spellings equal their constructor counts. -/
def spelledLookupFactor (tab : SpellingTable) : ℕ :=
  6 * (spellingLimit Prod.fst tab + spellingLimit Prod.snd tab + 1)

private theorem limit_eq (t : List (Tree × Tree)) :
    spellingLimit Prod.fst (spelledTable t) = RegisterLookup.limit Prod.fst t ∧
    spellingLimit Prod.snd (spelledTable t) = RegisterLookup.limit Prod.snd t := by
  induction t with
  | nil => exact ⟨rfl,rfl⟩
  | cons uv t ih =>
    obtain ⟨hu, hv⟩ := ih
    simp only [spelledTable, List.map_cons, spellingLimit, List.foldr_cons,
      spelling, List.length_map, Tree.spell_length, RegisterLookup.limit] at *
    exact ⟨congrArg (max uv.1.count) hu, congrArg (max uv.2.count) hv⟩

theorem spelledLookupFactor_eq (t : List (Tree × Tree)) :
    spelledLookupFactor (spelledTable t) = lookupFactor t := by
  rw [spelledLookupFactor, lookupFactor, (limit_eq t).1, (limit_eq t).2]

theorem primrec_spelledLookupFactor : Primrec spelledLookupFactor :=
  Primrec.nat_mul.comp (Primrec.const 6) (Primrec.nat_add.comp
    (Primrec.nat_add.comp (primrec_spellingLimit _ Primrec.fst) (primrec_spellingLimit _ Primrec.snd))
    (Primrec.const 1))

open private volumeFactor from OAI.Computability.NearSquareRoot.ScheduleRegisterLoomAlignedCost

theorem primrec_alignedFactor {X : Type} [Primcodable X] {f o C : X → ℕ}
    (hf : Primrec f) (ho : Primrec o) (hc : Primrec C) :
    Primrec (fun x => alignedFactor (f x) (o x) (C x)) := by
  have plus {g : X → ℕ} (hg : Primrec g) (c : ℕ) : Primrec (fun x => g x + c) :=
    Primrec.nat_add.comp hg (Primrec.const c)
  have times {g : X → ℕ} (hg : Primrec g) (c : ℕ) : Primrec (fun x => c * g x) :=
    Primrec.nat_mul.comp (Primrec.const c) hg
  have hv : Primrec (fun x => volumeFactor (f x) (o x) (C x)) :=
    plus (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp hf (plus hc 3))
      (Primrec.nat_mul.comp ho (plus hc 2))) hc) 12
  exact Primrec.nat_mul.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.const 3000) (times (plus hf 1) 401)) (times (plus ho 1) 250))
    (times ho 2)) (plus hv 1)

theorem primrec_packedFactor {X : Type} [Primcodable X] {f o C : X → ℕ}
    (hf : Primrec f) (ho : Primrec o) (hc : Primrec C) :
    Primrec (fun x => packedFactor (f x) (o x) (C x)) :=
  primrec_alignedFactor hf ho (Primrec.nat_add.comp (Primrec.nat_add.comp (primrec_alignedFactor hf ho hc) hc)
    (Primrec.const 2))

/-- The numeric coefficient can be obtained uniformly from a generated table
file and the two layout sizes. -/
theorem computable_payloadFactor {X : Type} [Primcodable X] {f o : X → ℕ} {tab : X → List (Tree × Tree)}
    (hf : Computable f) (ho : Computable o) (ht : Computable (fun x => spelledTable (tab x))) :
    Computable (fun x => payloadFactor (f x) (o x) (tab x)) := by
  have h : Primrec (fun s : ℕ × ℕ × ℕ => packedFactor s.1 s.2.1 s.2.2) :=
    primrec_packedFactor Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  apply (h.to_comp.comp (hf.pair (ho.pair (primrec_spelledLookupFactor.to_comp.comp ht)))).of_eq
  intro x
  change packedFactor _ _ (spelledLookupFactor (spelledTable (tab x))) = _
  rw [spelledLookupFactor_eq]
  rfl

/-- A bound for all comparisons and writes while looking up one tuple. -/
def wordClock (bytes : SpellingTable) : ℕ :=
  bytes.foldr (fun uv c => 50 * (uv.1.length + uv.2.length + 1) + c) 1

theorem primrec_wordClock : Primrec wordClock := by
  unfold wordClock
  exact Primrec.list_foldr Primrec.id (Primrec.const 1) (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 50) (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))) (Primrec.const 1)))
    (Primrec.snd.comp Primrec.snd)).to₂

theorem wordClock_spelledTable (tab : List (Tree × Tree)) :
    wordClock (spelledTable tab) = RegisterTable.cost tab := by
  induction tab with
  | nil => rfl
  | cons uv tab ih =>
    simp only [wordClock, spelledTable, List.map_cons, List.foldr_cons, spelling,
      List.length_map, Tree.spell_length, RegisterTable.cost] at *
    rw [ih]

def romPayloadFactor (n m : ℕ) (bytes : SpellingTable) : ℕ :=
  packedFactor n m (2 * wordClock bytes)

theorem primrec_romPayloadFactor {X : Type} [Primcodable X] {n m : X → ℕ} {bytes : X → SpellingTable}
    (hn : Primrec n) (hm : Primrec m) (hb : Primrec bytes) :
    Primrec (fun x => romPayloadFactor (n x) (m x) (bytes x)) :=
  primrec_packedFactor hn hm (Primrec.nat_mul.comp (Primrec.const 2) (primrec_wordClock.comp hb))

theorem computable_tableCost {X : Type} [Primcodable X] {t : X → List (Tree × Tree)}
    (hb : Computable fun x => spelledTable (t x)) :
    Computable (fun x => RegisterTable.cost (t x)) :=
  (primrec_wordClock.to_comp.comp hb).of_eq (fun x => wordClock_spelledTable (t x))

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
