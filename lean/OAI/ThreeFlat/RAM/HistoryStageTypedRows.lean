import OAI.ThreeFlat.RAM.HistoryStageBody
import OAI.ThreeFlat.Diagonal.HistoryWordLayout

namespace OAI
/-! # Source metadata for the bounded join of a physical history stage -/
namespace ThreeFlat.RAM.HistoryStageRoot.Typed
open Computability.VPVNP.BurstRAM PrivateRAM BitLayout Diagonal.HistoryContraction
open HistoryBoundedBody HistoryBoundedJoin HistoryJoinScan
open scoped BigOperators Fin.CommRing

noncomputable section
variable {F Pins : Type} [CommSemiring F] {S : Shape} {R : Rewrite S F} {t : Fin R.count}
  (L : PortLayout S Pins) (V : PortLayout (R.target t) Pins) (count : (R.target t).Site→ℕ)
  (order : ∀ v,Fin (count v)≃{x // R.owner t x=v}) (v : (R.target t).Site)
  (root : ∀ v,Tree F (L.hidden count order v+V.halfBits v))
  (ok : ∀ v (pin : Fin (L.hidden count order v+V.halfBits v)→Bool) x y,
    (∀ z a j,pin (L.stageOld V count order v z a j)=L.binary a.1.1 (x z a) j) →
    (∀ a j,pin (L.stageNew V count order v a j)=V.binary a.1.1 (y a) j) →
    (root v).compile.eval pin=R.kernel t v x y)
  (forest : Forest F L.form) (T : Input) (raw : ℕ→ℕ)
set_option quotPrecheck false
local notation "next" => L.inherit V count order
local notation "stage" => L.wordsStage V count order root ok
local notation "nets" => fun i=>((stage).tapeFactor forest v i).compile
local notation "links" => (stage).tapePin forest v

/-- Saturation of root/child counts follows from their published S12 ranges.
The six physical copy operands contain the actual S12 pointers and the private
offset after the earlier streams in the chosen child order. -/
def copy {n h p : ℕ} {ar : Fin n→ℕ} (T : Input) (raw : ℕ→ℕ) (N : ∀ i,BitNetwork F (ar i))
    (_ : ∀ i,Fin (ar i)→BitSource h p) (i : Fin n) : Header ℕ :=
  ⟨(atResult raw (ptr T raw i.val)).stream,T.stream+4*Tree.before (fun j=>(N j).cells) i,
    mapPtr T raw i.val,ar i,p,h+Tree.before (fun j=>(N j).internal) i⟩

def mapRow (T : Input) (raw : ℕ→ℕ) (i : ℕ) : Tape.MapRow :=
  let op:=operands T raw i
  ⟨8,T.operand+5*i,op 2,op 3,op 4⟩

theorem out_pins (ports : Ports L V count order v T raw) : outPins T raw=(next).form.width v := by
  rw [outPins,ports.external,ports.fresh];rfl

/-- The opcode-eight map is the true permutation into private incident bits,
new shared half bits or inherited public endpoint positions. -/
theorem map_value {W : ℕ} (ports : Ports L V count order v T raw) (m : Memory W) (i : Fin (count v+1)) :
    ∀ j : Fin ((stage).tapeArity forest v i),
    (mapRow T raw i.val).value m j.val=(sourceAddress (links i j):Word W) := by
  refine Fin.cases ?_ (fun k=>?_) i
  · intro j
    exact congrArg (fun x : ℕ=>(x:Word W)) (Ports.kernel_word L V count order v ports j)
  · intro j
    exact congrArg (fun x : ℕ=>(x:Word W)) (Ports.child_word L V count order v ports k j)

/-- The source streams of the published kernel and the real ordered child caches.
The root has four information words, so its unused endpoint fields are unconstrained. -/
structure Stored {W : ℕ} (tag : ((Fin 3→Bool)→F)→ℕ) (m : Memory W) : Prop where
  rootPins : (atResult raw T.kernel).pins=L.hidden count order v+V.halfBits v
  rootRows : (atResult raw T.kernel).rows=(root v).compile.cells
  rootBits : (atResult raw T.kernel).bits=(root v).compile.internal
  kernel : HistoryCompiledRows.Records tag (root v).compile (atResult raw T.kernel).stream m
  countRows : ∀ i,(atResult raw (childPtr T raw i.val)).rows=(forest (order v i).val).compile.cells
  countBits : ∀ i,(atResult raw (childPtr T raw i.val)).bits=(forest (order v i).val).compile.internal
  children : ∀ i,HistoryCompiledRows.Records tag (forest (order v i).val).compile
    (atResult raw (childPtr T raw i.val)).stream m

variable {W : ℕ} {tag : ((Fin 3→Bool)→F)→ℕ} {m : Memory W}
local notation "saved" => Stored L V count order v root forest T raw tag m
local notation "cp" => copy T raw nets links

theorem child_rows (r : saved) (i : Fin (count v+1)) :
    HistoryCompiledRows.Records tag (nets i) (cp i).source m := by
  refine Fin.cases ?_ (fun k=>?_) i
  · exact r.kernel
  · exact r.children k

def infoAt (T : Input) (raw : ℕ→ℕ) (i : ℕ) : Info :=
  let x:=atResult raw (ptr T raw i)
  ⟨x.stream,x.pins,x.rows,x.bits⟩

theorem info (r : saved) (ports : Ports L V count order v T raw) (i : Fin (count v+1)) :
    infoAt T raw i.val=⟨(cp i).source,(stage).tapeArity forest v i,(nets i).cells,(nets i).internal⟩ := by
  refine Fin.cases ?_ (fun k=>?_) i
  · let a := atResult raw T.kernel
    change Info.mk a.stream a.pins a.rows a.bits =
      Info.mk a.stream (L.hidden count order v+V.halfBits v) (root v).compile.cells (root v).compile.internal
    dsimp only [a]
    rw [r.rootPins,r.rootRows,r.rootBits]
  · let a := atResult raw (childPtr T raw k.val)
    change Info.mk a.stream a.pins a.rows a.bits =
      Info.mk a.stream (L.form.width (order v k).val) (forest (order v k).val).compile.cells
        (forest (order v k).val).compile.internal
    dsimp only [a]
    rw [ports.childArity k,r.countRows k,r.countBits k]

theorem mapPtr_before (r : saved) (ports : Ports L V count order v T raw) (i : Fin (count v+1)) :
    mapPtr T raw i.val=T.maps+Tree.before ((stage).tapeArity forest v) i := by
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [mapPtr,Tree.before]
  · change T.maps+(atResult raw T.kernel).pins+«prefix» T raw j.val Result.pins=
      T.maps+∑ k : Fin (j.val+1),(stage).tapeArity forest v (Fin.castLE j.succ.isLt.le k)
    rw [Fin.sum_univ_succ,r.rootPins,Nat.add_assoc]
    exact congrArg (fun total=>T.maps+((L.hidden count order v+V.halfBits v)+total))
      (prefix_value (T:=T) (m:=raw) Result.pins (fun k:Fin (count v)=>L.form.width (order v k).val)
        ports.childArity j.val j.isLt.le)

/-- The six copy words calculated by the bounded join agree at the physical
post-boot snapshot. Only the actual links and info of the reached children enter. -/
theorem arguments_at (r : saved) (ports : Ports L V count order v T raw) (snapshot : ℕ→ℕ)
    (ld : ∀ i : Fin (count v+1),HistoryBoundedJoin.child (hub T raw) snapshot i.val=link T raw i.val)
    (rd : ∀ i : Fin (count v+1),HistoryBoundedJoin.read (ptr T raw i.val) snapshot=infoAt T raw i.val)
    (i : Fin (count v+1)) (j : Fin 6) :
    arguments (hub T raw) snapshot i.val j.castSucc =
      (![(cp i).source,(cp i).dest,(cp i).pins,(cp i).oldPins,(cp i).newPins,(cp i).offset] j) := by
  have records (k : Fin (count v+1)) :
      HistoryBoundedJoin.read (HistoryBoundedJoin.child (hub T raw) snapshot k.val).node snapshot=
        ⟨(cp k).source,(stage).tapeArity forest v k,(nets k).cells,(nets k).internal⟩ := by
    rw [ld k];exact (rd k).trans (info L V count order v root ok forest T raw r ports k)
  have size (k : Fin (count v+1)) :
      HistoryBoundedJoin.read (HistoryBoundedJoin.child (hub T raw) snapshot k.val).node snapshot=
        ⟨(HistoryBoundedJoin.read (HistoryBoundedJoin.child (hub T raw) snapshot k.val).node snapshot).stream,
          (stage).tapeArity forest v k,(nets k).cells,(nets k).internal⟩ := by rw [records k]
  obtain ⟨dst,off⟩:=HistoryBoundedJoin.moved_eq nets links (hub T raw) snapshot i ports.hidden size
  have parent:=out_pins L V count order v T raw ports
  dsimp only [arguments]
  rw [records i,ld i,dst,off]
  fin_cases j <;> simp [copy,hub,link,parent,Tree.before]

/-- Result rows are the true row and hidden counts after the six-word S13
publication, and parent ext is exactly the ordered sum of inherited endpoint counts. -/
theorem output (r : saved) (ports : Ports L V count order v T raw) :
    result T raw = ![T.stream,(next).form.width v,((stage).assemble forest v).compile.cells,
      ((stage).assemble forest v).compile.internal,T.ext,(next).ext v] := by
  have rows:=prefix_value (T:=T) (m:=raw) Result.rows (fun i=> (forest (order v i).val).compile.cells)
      r.countRows (count v) le_rfl
  have bits:=prefix_value (T:=T) (m:=raw) Result.bits (fun i=> (forest (order v i).val).compile.internal)
      r.countBits (count v) le_rfl
  rw [result,ports.degree,out_pins L V count order v T raw ports,ports.external,ports.hidden,r.rootRows,r.rootBits,rows,bits]
  simp only [Tree.compiled_rows,Tree.compiled_bits,Stage.assemble_rows,Stage.assemble_bits,Nat.add_assoc]
  rfl


end
end ThreeFlat.RAM.HistoryStageRoot.Typed

end OAI
