import OAI.Computability.BorderVNP.TransmissionInputRecords
import OAI.Computability.BorderVNP.TeamTapeInputEntry

/-! # Pinned processor startup from the signed contraction word and empty workspace -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP UniversalMachine BurstRAM RAMSerialization RAMTape TeamTapeInput

/-- Bit count of the tagged row address and bucket capacity. -/
def setupWidth (w n : ℕ) : ℕ := (2*w+1) + (2*Nat.clog 2 (n+1)+1)

/-- Each processor's setup fields have equal length regardless of their encoded values. -/
theorem length_setupBits (w n start H : ℕ) : (Entry.setupBits w n start H).length = setupWidth w n := by
  simp [Entry.setupBits, TeamTapeInput.digits, Evaluator.InputBank.length_fieldBits, setupWidth]

/-- Public record cursor and buffer parameters followed by the remaining arbitrary bits. -/
def entryTail {a : ℕ} (w n start H : ℕ) (free : Fin a → Bool) : Fin (setupWidth w n+a) → Bool :=
  let bits := Entry.setupBits w n start H ++ List.ofFn free
  fun j => bits[j.val]'(by simp [bits, length_setupBits])

/-- Enumerating a site's startup tail gives the precise public parameters and advice bytes. -/
theorem ofFn_entryTail {a : ℕ} (w n start H : ℕ) (free : Fin a → Bool) :
    List.ofFn (entryTail w n start H free) = Entry.setupBits w n start H ++ List.ofFn free := by
  apply List.ext_getElem
  · rw [List.length_ofFn,List.length_append,length_setupBits,List.length_ofFn]
  · intros; simp [entryTail]

/-- Literal width including the program, both input cuts, record parameters and free bits. -/
def entryLiteral (p : UniversalMachine.Program) (w n a : ℕ) : ℕ :=
  (programPrefix p).length + (cutWidth n+(setupWidth w n+a))

/-- The actual distance between starts of adjacent RAM initialization rows. -/
def entryStride (p : UniversalMachine.Program) (w n a R link : ℕ) : ℕ :=
  2*entryLiteral p w n a + R*link

variable {R r a inner : ℕ} {Edge : Type}

/-- Wiring from which the real signed processor reads all four initialization parameters,
including its globally addressed row start. -/
def entryWiring (p : UniversalMachine.Program) (free : Fin (R+1) → Fin r → Fin a → Bool)
    (interior : Fin r → Fin inner → Option Edge) (d link n w H : ℕ)
    (fit : entryStride p w n a R link + inner ≤ n) :
    Wiring R r (cutWidth n + (setupWidth w n + a)) d link inner n Edge :=
  tapeWiring p (fun u j => entryTail w n (j.val*entryStride p w n a R link) H (free u j))
    interior d link n fit

/-- With every workspace stack empty, the real fixed entry table turns the site's
signed input word into its globally addressed record buffer and retains its actual
interior link bits and remaining literal advice. -/
theorem entryWiring_start_full (p : UniversalMachine.Program) (free : Fin (R+1) → Fin r → Fin a → Bool)
    (interior : Fin r → Fin inner → Option Edge) (d link n w H : ℕ) (hw : 2 ≤ w) (hH : H ≤ n)
    (fit : entryStride p w n a R link + inner ≤ n) (u : Fin (R+1)) (j : Fin r)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (int : Edge → Bool)
    (ibase hbase starbase : ℕ) :
    let G := entryWiring p free interior d link n w H fit
    let fields := G.processorFields u pin ext ibase hbase starbase
    let data := fields.row j
    let route := List.ofFn (fun i => (interior j i).elim false int)
    let start := j.val * entryStride p w n a R link
    let pad := List.replicate (n-(entryStride p w n a R link+inner)) false
    2*(start+data.length) ≤ 2^w → 2*data.length ≤ 4*H →
      ∃ k out, k ≤ 46*n+19 + (3*w + 9*Nat.clog 2 (n+1) + 7*H+4) +
          (10*w+20*H+13 + TeamTapeInputEmit.budget w data.length) ∧
        Entry.program.Runs k (Sum.elim (initial (List.ofFn (G.word pin ext int u j))) (fun _ => [])) out ∧
        TeamTapeInputEmit.Ready hw H (start+data.length) [] (TeamTapeInputEmit.records w start data)
          (out ∘ Entry.setupPort ∘ TeamTapeInputEmit.Setup.Port.emit) ∧ out (.inl (.cut .incident)) = route ∧
        out (.inr .start) = BurstRAM.wordBits (TeamTapeInputEmit.word w start) ∧
        out (.inl (.peek .input)) = List.ofFn (free u j) ++ (fields.exterior j).flatten ++ fields.pins j ++ route ++ pad ∧
        out (.inl .bits) = [] ∧ out (.inl .high) = [] ∧ out (.inl .scratch) = [] ∧
        out (.inr .bucket) = List.replicate H true := by
  intro G fields data route start pad room cap
  let width := entryLiteral p w n a
  have he : (fields.exterior j).flatten.length = R*link := by
    simpa only [fields,G,entryWiring,Wiring.pinLayout,tapeWiring,Nat.add_sub_cancel] using fields.exterior_length j
  have hp : (fields.pins j).length = width := fields.pins_length j
  have hr : route.length = inner := List.length_ofFn
  have hs : width+(fields.exterior j).flatten.length+(fields.pins j).length+route.length ≤ n := by
    rw [he,hp,hr]
    change 2*width+R*link+inner ≤ n at fit
    omega
  have hc : (programPrefix p).length+4*Nat.clog 2 (n+1)+2+(Entry.setupBits w n start H ++ List.ofFn (free u j)).length = width := by
    simp [width,entryLiteral,cutWidth,length_setupBits,Nat.add_assoc]
  have run := Entry.runs hw p n width start H (List.ofFn (free u j)) (fields.pins j) route (fields.exterior j) hH hc hs
  have hdata : data = TeamTapeInput.inputData
      (programPrefix p ++ parameters (digits n (2*width+R*link)) (digits n inner) ++
        (Entry.setupBits w n start H ++ List.ofFn (free u j))) (fields.exterior j) (fields.pins j) := by
    change TeamTapeInput.inputData (programPrefix p ++ List.ofFn (cutTail _ _ _ _)) _ _ = _
    rw [ofFn_cutTail, ofFn_entryTail, List.append_assoc]
    rfl
  dsimp only at run
  rw [he,hp,hr,show width+R*link+width = 2*width+R*link by omega,←hdata] at run
  obtain ⟨k,out,hk,read,ready,hroute,hstart,hpeek,hbits,hhigh,hscratch,hbucket⟩ := run room cap
  have raw := G.word_processorFields u j pin ext int ibase hbase starbase
  change List.ofFn (G.word pin ext int u j) = data ++ route ++ pad at raw
  exact ⟨k,out,hk,raw ▸ read,ready,hroute,hstart,hpeek,hbits,hhigh,hscratch,hbucket⟩

/-- The record buffer and two remaining input streams after physical startup. -/
theorem entryWiring_start (p : UniversalMachine.Program) (free : Fin (R+1) → Fin r → Fin a → Bool)
    (interior : Fin r → Fin inner → Option Edge) (d link n w H : ℕ) (hw : 2 ≤ w) (hH : H ≤ n)
    (fit : entryStride p w n a R link + inner ≤ n) (u : Fin (R+1)) (j : Fin r)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (int : Edge → Bool)
    (ibase hbase starbase : ℕ) :
    let G := entryWiring p free interior d link n w H fit
    let fields := G.processorFields u pin ext ibase hbase starbase
    let data := fields.row j
    let route := List.ofFn (fun i => (interior j i).elim false int)
    let start := j.val * entryStride p w n a R link
    let pad := List.replicate (n-(entryStride p w n a R link+inner)) false
    2*(start+data.length) ≤ 2^w → 2*data.length ≤ 4*H →
      ∃ k out, k ≤ 46*n+19 + (3*w + 9*Nat.clog 2 (n+1) + 7*H+4) +
          (10*w+20*H+13 + TeamTapeInputEmit.budget w data.length) ∧
        Entry.program.Runs k (Sum.elim (initial (List.ofFn (G.word pin ext int u j))) (fun _ => [])) out ∧
        TeamTapeInputEmit.Ready hw H (start+data.length) [] (TeamTapeInputEmit.records w start data)
          (out ∘ Entry.setupPort ∘ TeamTapeInputEmit.Setup.Port.emit) ∧ out (.inl (.cut .incident)) = route ∧
        out (.inl (.peek .input)) = List.ofFn (free u j) ++ (fields.exterior j).flatten ++ fields.pins j ++ route ++ pad := by
  intro G fields data route start pad room cap
  obtain ⟨k,out,hk,read,ready,hroute,_,hpeek,_⟩ :=
    entryWiring_start_full p free interior d link n w H hw hH fit u j pin ext int
      ibase hbase starbase room cap
  exact ⟨k,out,hk,read,ready,hroute,hpeek⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
