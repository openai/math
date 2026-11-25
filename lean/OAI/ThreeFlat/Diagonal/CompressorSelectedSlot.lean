import OAI.ThreeFlat.Diagonal.CompressorRankSlots
import OAI.ThreeFlat.Diagonal.CompressorNativeGraph

namespace OAI
/-! # Reverse mate and payload of the sorted, elected physical edge -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM CompressorRegularize
open scoped Classical Fin.NatCast
variable {w d : ℕ}

def readField (f : Candidate (Word w) → Word w) (id : Word w) : List (Candidate (Word w)) → Word w
  | [] => 0
  | c :: tail => if c.key=id then f c else readField f id tail

theorem electedField (f : Candidate (Word w) → Word w) (k val : Word w) (cs : List (Candidate (Word w)))
    (existsIn : k∈cs.map Candidate.key) (agrees : ∀c∈cs, c.key=k → f c=val) : readField f k cs=val := by
  induction cs with
  | nil => simp at existsIn
  | cons x xs ih =>
    by_cases hits : x.key=k
    · rw [readField,ite_eq_left hits]
      exact agrees x (by simp) hits
    · rw [readField,ite_eq_right hits]
      exact ih (by simpa [Ne.symm hits] using existsIn) (fun c hc => agrees c (by simp [hc]))

def liveQuery (cs : Bool → Word w → List (Candidate (Word w))) (rev : Bool) (b port : Word w) :
    Field → Word w :=
  let localList := cs rev b
  let ids := localList.map Candidate.key
  let id := Rank.chosen ids port ids
  let other := readField Candidate.otherBase id localList
  fun
    | .identifier => id
    | .neighbor => other
    | .delta => readField Candidate.shift id localList
    | .matePort => ((Rank.below ((cs (!rev) other).map Candidate.key) id).card : Word w)

variable {E B : Type*} [Fintype E] [LinearOrder E] [DecidableEq B]
variable (whereAt : Bool → E → B) (equal : ∀ rev b, (incident (whereAt rev) b).card=d)
variable (key : E ↪o Word w) (baseCode : B → Word w) (shift : E → Word w)
variable (cs : Bool → Word w → List (Candidate (Word w)))
variable (complete : ∀rev b, Rank.eligible ((cs rev (baseCode b)).map Candidate.key)=
  (incident (whereAt rev) b).map key.toEmbedding)
variable (payload : ∀ rev b c, c∈cs rev (baseCode b) → ∀e, c.key=key e →
  c.otherBase=baseCode (whereAt (!rev) e) ∧ c.shift=shift e)

include complete payload in
theorem liveQuery_correct (fit : d≤2^w) (rev : Bool) (b : B) (i : Fin d) :
    let e := (numbering (whereAt rev) (equal rev)).symm (b,i)
    liveQuery cs rev (baseCode b) (i.val:Word w) = fun
      | .identifier => key e
      | .neighbor => baseCode (whereAt (!rev) e)
      | .delta => shift e
      | .matePort => ((numbering (whereAt (!rev)) (equal (!rev)) e).2.val : Word w) := by
  let get (r : Bool) (v : B) := (cs r (baseCode v)).map Candidate.key
  let e := (numbering (whereAt rev) (equal rev)).symm (b,i)
  have pick : Rank.chosen (get rev b) (i.val:Word w) (get rev b)=key e :=
    Rank.lookup_local _ _ key (get rev) (complete rev) fit b i
  have hebase : whereAt rev e=b := congrArg Prod.fst ((numbering (whereAt rev) (equal rev)).apply_symm_apply (b,i))
  have support : key e∈Rank.eligible (get rev b) := by
    rw [complete]
    exact Finset.mem_map.mpr ⟨e,by simp [incident,hebase],rfl⟩
  have found : key e ∈ get rev b := by
    exact List.mem_toFinset.mp (Finset.mem_of_mem_erase support)
  have other := electedField Candidate.otherBase (key e) (baseCode (whereAt (!rev) e)) (cs rev (baseCode b)) found
    (fun x hx h => (payload rev b x hx e h).1)
  have delta := electedField Candidate.shift (key e) (shift e) (cs rev (baseCode b)) found
    (fun x hx h => (payload rev b x hx e h).2)
  have mate := Rank.rank_local (whereAt (!rev)) (equal (!rev)) key (get (!rev)) (complete (!rev)) e
  dsimp only [get] at pick mate
  funext f
  cases f <;> simp only [liveQuery,pick,other,delta,mate] <;> rfl

end ThreeFlat.Diagonal.CompressorPacking.Native.Graph

end OAI
