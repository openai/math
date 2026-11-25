import OAI.Computability.MultitapeWeakETH.SyntaxSort
import OAI.Computability.MultitapeWeakETH.FrameProgram
import OAI.Computability.MultitapeWeakETH.GridProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountDFS

/-! # Compiling the sparse traversal's retained formula into grid input -/

namespace OAI.Computability.MultitapeWeakETH.LeafSyntax

open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse SparseDFSRefinement
open IntegerMultiplication.Code Encoding FormulaRanks
open private cmp cmp_poly cmp_encode from OAI.Computability.MultitapeWeakETH.RankProgram

abbrev Word := List Bool

private def records (bits : Word) := (FrameProgram.read bits).2.1

private theorem records_poly : Poly records :=
  FrameProgram.read_poly.compose (Easy.snd.compose Easy.fst).poly

private theorem records_encode {X : Type} (enc : X → Word) (xs : List X) :
    records (encodeList enc xs) = xs.map enc := by
  have eq : encodeList enc xs = ProgramEncoding.encodeRecords (xs.map enc) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ProgramEncoding.encodeRecords,encodeList,ih]
  simpa [records,eq] using congrArg (fun s => s.2.1) (FrameProgram.read_records (xs.map enc) [])

private def clause (bits : Word) : Key :=
  SyntaxSort.arrange Iter.small ((records bits).map ruler)

private theorem clause_poly : Poly clause :=
  (records_poly.compose (Poly.maps _ (Easy.ruler Easy.identity).poly)).compose
    (SyntaxSort.arrange_poly _ Iter.small_easy.poly)

private theorem clause_eq {n : ℕ} (C : List (SAT.Literal (Fin n))) (hn : C.Nodup) :
    clause (encodeList encodeNat (C.map literalCode)) = encodeKey (clauseNumbers (ExecCNF.clauseSet C)) := by
  let tag := fun a : ℕ => tally (a+1)
  have tags (a : ℕ) : ruler (encodeNat a) = tag a := by
    rw [← recover_tally (ruler _),ruler_length,length_encodeNat]
  have ordered := SyntaxSort.arrange_map Iter.small tag (fun _ => True)
    (fun a b _ _ => by simp [Iter.small,tag]) (C.map literalCode) (by simp) (hn.map literalCode_injective)
  have same : (C.map literalCode).toFinset = (ExecCNF.clauseSet C).image literalCode := by
    ext a
    simp [ExecCNF.clauseSet]
  unfold clause
  rw [records_encode,List.map_map]
  simpa only [Function.comp_def,tags,same,encodeKey,clauseNumbers] using ordered

/-- Both levels of sorting operate on the actual encoded body from the DFS work stack. -/
def body (bits : Word) : List Key :=
  SyntaxSort.arrange (cmp 3) ((records bits).map clause)

theorem body_poly : Poly body :=
  (records_poly.compose (Poly.maps _ clause_poly)).compose (SyntaxSort.arrange_poly _ (cmp_poly 3))

theorem body_eq {n : ℕ} (F : RawCNF n) (valid : Valid 3 F) :
    body (SparseCountProgram.encodeBody F) = (cnfNumbers (ExecCNF.formulaSet F)).map encodeKey := by
  let keys := (F.map ExecCNF.clauseSet).map clauseNumbers
  have lengths : ∀ k ∈ keys, k.length ≤ 3 := by
    intro k hk
    obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hk
    obtain ⟨raw,hr,rfl⟩ := List.mem_map.mp hC
    simpa [ExecCNF.clauseSet,List.toFinset_card_of_nodup (valid.literal_nodup _ hr)] using valid.width raw hr
  have ordered := SyntaxSort.arrange_map (cmp 3) encodeKey (fun k => k.length ≤ 3)
    (fun a b ha hb => by rw [cmp_encode 3 a b ha hb]; by_cases h : a < b <;> simp [h])
    keys lengths (valid.clause_nodup.map clauseNumbers_injective)
  have eq : ((records (SparseCountProgram.encodeBody F)).map clause) = keys.map encodeKey := by
    simp only [SparseCountProgram.encodeBody,records_encode,keys,List.map_map,Function.comp_def]
    exact List.map_congr_left fun C hC => clause_eq C (valid.literal_nodup _ hC)
  unfold body cnfNumbers
  rw [eq,ordered]
  apply congrArg (fun s : Finset (List ℕ) => (s.sort (· ≤ ·)).map encodeKey)
  ext k
  simp [keys,ExecCNF.formulaSet]

abbrev Query := Tally × Tally × Word

/-- Full permutation table compilation starting with the two unary size
fields and the raw clause bytes owned by the leaf. -/
def prepare (b : ℕ) (q : Query) := CNFNetwork.SyntaxProgram.prepare b (q.1,q.2.1,body q.2.2)

theorem prepare_poly (b : ℕ) : Poly (prepare b) :=
  (Easy.fst.poly.pair (((Easy.snd.compose Easy.fst).poly).pair
    ((Easy.snd.compose Easy.snd).poly.compose body_poly))).compose (CNFNetwork.SyntaxProgram.prepare_poly b)

theorem prepare_represents {n b N : ℕ} (hb : 0 < b) (hN : 1 < N) (F : RawCNF n) (valid : Valid 3 F)
    (fit : Fintype.card (CNFNetwork.Site (ExecCNF.formulaSet F)) ≤ 2^(b*DyadicBudget.index b N)) :
    let wd := formulaSet_width_le F valid.width
    NearSquareRoot.Benes.RawRepresents (CNFNetwork.exchange (ExecCNF.formulaSet F) fit wd)
      (prepare b (tally N,tally n,SparseCountProgram.encodeBody F)) := by
  simpa only [prepare,body_eq F valid] using
    CNFNetwork.SyntaxProgram.prepare_represents hb hN (ExecCNF.formulaSet F) (formulaSet_width_le F valid.width) fit

end OAI.Computability.MultitapeWeakETH.LeafSyntax
