import OAI.Computability.MultitapeWeakETH.HistoryVisit
import OAI.Computability.MultitapeWeakETH.WitnessForestCodes

/-! # Exact source and successor cases of the chronological tape visitor -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code WitnessWalk CNFNetwork.SwitchFactor VPVNP CompressorRecords

open private leaf from OAI.Computability.MultitapeWeakETH.HistoryVisit

variable {stages : ℕ} (K : ℕ) (children : HistorySite × Bits.Word → Option ChildResult)
  (shrinking : Fin stages → Kernel) (refresh : RefreshQuery → Option (List Tally))
  (q : LeafSyntax.Query) (log : WriteBytes)

theorem visitor_zero (site : Tally) (packet bits : Bits.Word) :
    visitor K children shrinking refresh (((q,log),(([],site),packet)),bits) =
      (sourceRead K ((q,site,packet),bits)).map (fun tail => (([],tail),[])) := by
  unfold visitor leaf sourceRead
  cases sourceCheck K (q,site,packet) <;> rfl

theorem visitor_succ (i j : ℕ) (packet bits tail : Bits.Word) (jobs : List Job) (labels : List Tally) :
    let point : HistorySite := (((q.1,log),tally i),tally j)
    visitor K children shrinking refresh (((q,log),((tally (i+1),tally j),packet)),bits) = some ((jobs,tail),labels) ↔
      ∃ ids bank rest, children (point,bits) = some ((ids,bank),rest) ∧
        dispatch shrinking (refreshKernel refresh) (tally i,((point,bank,packet),rest)) = some (labels,tail) ∧
        jobs = childJobs (tally i,ids,bank.2) := by
  intro point
  exact passVisit_iff children (fun x => dispatch shrinking (refreshKernel refresh) (x.1.1.1.2,x)) ((point,packet),bits) jobs tail labels

private theorem accepts_nil {D : Type} (visit : Visit D) (ctx : D) (a b : Bits.Word) (ls : List Tally) :
    Accepts visit ctx [] a b ls ↔ a = b ∧ ls = [] := by
  constructor
  · rintro ⟨_,h⟩; cases h; exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩; exact ⟨_,.nil _⟩

theorem visitor_leaf_reads {X : Type} (reader : ChoiceReader X) (site : Tally) (packet : Bits.Word)
    (spec : ∀ bits, (reader.read bits).map Prod.snd = sourceRead K ((q,site,packet),bits)) :
    Reads (visitor K children shrinking refresh) (q,log) [(([],site),packet)] reader.encode (fun _ => []) := by
  intro bits tail labels
  rw [accepts_one]
  have run := visitor_zero K children shrinking refresh q log site packet bits
  rw [← spec] at run
  simp only [Option.map_map] at run
  constructor
  · rintro ⟨js,mid,ls,below,hit,parse,rfl⟩
    rw [run,Option.map_eq_some_iff] at hit
    obtain ⟨⟨x,b⟩,got,eqn⟩ := hit
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := (Prod.mk.inj eqn.symm).imp_left Prod.mk.inj
    obtain ⟨rfl,rfl⟩ := (accepts_nil _ _ _ _ _).mp parse
    exact ⟨x,(reader.read_iff bits x _).mp got,rfl⟩
  · rintro ⟨x,h,rfl⟩
    refine ⟨[],tail,[],[],?_,⟨_,.nil _⟩,rfl⟩
    rw [run,(reader.read_iff bits x tail).mpr h]
    rfl

end OAI.Computability.MultitapeWeakETH.NativeGrid
