import OAI.Hierarchy.DescentPackedCensusPorts
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Fixed local census lookup from signed physical quantum-port slots -/

namespace Hierarchy.DescentSixParty.PackedCensus
open DescentSIMDLookup DescentColonies StarKeys
open scoped Classical BigOperators Fin.CommRing
noncomputable section

private def pair (a b : ℕ) : Cell a × Cell b ≃ Cell (a+b) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 a b).symm)

def header (b cap : ℕ) :
    (Cell 1 × Cell b) × (Fin cap→Cell 2) ≃ Cell (1+b+2*cap) :=
  ((pair 1 b).prodCongr (encode 2 cap)).trans (pair (1+b) (2*cap))

theorem header_value {b cap : ℕ} (hub : Cell 1) (atoms : Cell b) (slots : Fin cap→Cell 2) :
    (header b cap ((hub,atoms),slots)).val =
      (hub.val*2^b+atoms.val)*2^(2*cap)+(encode 2 cap slots).val := by
  simp [header,pair,finProdFinEquiv_apply_val]
  all_goals ring

/-- Slot 3 denotes an outgoing marked port, slot 1 every other occupied
port. The history field is a residue at the precision of the requested sum. -/
def tags {cap : ℕ} (live paid : Finset (Fin cap)) (j : Fin cap) : Cell 2 :=
  if j∈paid then 3 else if j∈live then 1 else 0

def numLive {cap : ℕ} (t : Fin cap→Cell 2) := (Finset.univ.filter (fun j=>t j≠0)).card
def numPaid {cap : ℕ} (t : Fin cap→Cell 2) := (Finset.univ.filter (fun j=>t j=3)).card

theorem numLive_tags {cap : ℕ} (live paid : Finset (Fin cap)) (sub : paid⊆live) :
    numLive (tags live paid)=live.card := by
  unfold numLive
  apply congrArg Finset.card
  apply Finset.ext
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have three : (3 : Cell 2) ≠ 0 := by decide
  have one : (1 : Cell 2) ≠ 0 := by decide
  by_cases hp : j∈paid
  · simp [tags,hp,sub hp,three]
  · by_cases hl : j∈live <;> simp [tags,hp,hl,one]

theorem numPaid_tags {cap : ℕ} (live paid : Finset (Fin cap)) :
    numPaid (tags live paid)=paid.card := by
  unfold numPaid
  congr 1
  ext j
  by_cases hp : j∈paid <;> by_cases hl : j∈live <;> simp [tags,hp,hl]

/-- The same circuit works for every supplied group, vertex and layout. -/
def evaluate (marked : Bool) (b cap wire β grain hist : ℕ) (raw : Cell (1+b+2*cap)) : Cell b :=
  let t:=(header b cap).symm raw
  if marked then (numPaid t.2:ℕ)
  else ((wire*grain*(if t.1.1.val=0 then 1 else β)*numLive t.2:ℕ):Cell b) + (hist:Cell b)*t.1.2

def lookup (marked : Bool) (b cap k wire β grain hist : ℕ) :
    Cell ((1+b+2*cap)*2^k)→Cell (b*2^k) :=
  fun row=>encode b (2^k) (evaluate marked b cap wire β grain hist ∘ (encode (1+b+2*cap) (2^k)).symm row)

variable {F P V A : Type} [Field F] [Fintype V] [DecidableEq V]
  {d k : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)
  (n : W.graph.Edge→ℕ) (positive : ∀e∈W.core,0<n e)
  (hub : V→Bool) (atoms : W.graph.Site→List A) (b cap : ℕ)
  (order : ∀ v x,Ports W pos ix n v x ↪ Fin cap)

def localCell (v : V) (x : Block k) : Cell (1+b+2*cap) :=
  header b cap ((if hub v then 1 else 0,(histories W pos ix atoms v x:ℕ)),
    tags (Finset.univ.map (order v x))
      (Finset.univ.map ((portOfOut W pos ix n positive v x).trans (order v x))))

def source (v : V) : Cell ((1+b+2*cap)*2^k) :=
  encode (1+b+2*cap) (2^k) (localCell W pos ix n positive hub atoms b cap order v)

omit [Field F] in
theorem source_read (marked : Bool) (wire β grain hist : ℕ) (fit : ∀e,W.graph.width e=n e*grain) (v : V) :
    lookup marked b cap k wire β grain hist (source W pos ix n positive hub atoms b cap order v) =
      encode b (2^k) (fun x : Block k=>((if marked then
        blockMass W.graph pos ix (fun u=>(W.core.filter (fun e=>W.graph.src e=u)).card) v x else
        blockMass W.graph pos ix (W.siteUnits (hub ∘ pos) atoms wire β hist) v x:ℕ):Cell b)) := by
  apply congrArg (encode b (2^k))
  -- Reduce both encoded rows at each independent old block.
  funext x
  let here := order v x
  let picked := portOfOut W pos ix n positive v x
  have sub : Finset.univ.map (picked.trans here) ⊆ Finset.univ.map here := by
    intro j hj
    obtain ⟨e,_,rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_map.mpr ⟨picked e,Finset.mem_univ _,rfl⟩
  change evaluate marked b cap wire β grain hist
    ((encode (1+b+2*cap) (2^k)).symm (source W pos ix n positive hub atoms b cap order v) x)=_
  simp only [source,Equiv.symm_apply_apply,localCell,evaluate]
  have live := numLive_tags (Finset.univ.map here) (Finset.univ.map (picked.trans here)) sub
  have paid := numPaid_tags (Finset.univ.map here) (Finset.univ.map (picked.trans here))
  simp only [Finset.card_map,Finset.card_univ] at live paid
  cases marked
  · rw [units W pos ix n hub atoms wire β hist grain fit v x]
    cases flag : hub v <;> simp [here,picked] at live ⊢ <;> simp [live,Nat.cast_add]
  · simpa [here,picked,out_eq W pos ix v x] using congrArg (fun a : ℕ=>(a:Cell b)) paid

end
end Hierarchy.DescentSixParty.PackedCensus

end OAI
