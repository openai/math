import OAI.Hierarchy.ProbeStageRowNative
import OAI.Hierarchy.ProbeStageMask

namespace OAI
/-! # Computing the allocator's two block numbers and candidate-string row -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

/-- The last two read-only tables index the local offset modulo B².
The first returns this residue; the second multiplies it by the fixed B². -/
structure Endpoints where
  group : Bank
  source : Bank
  target : Bank
  groupBlocks : Bank
  toBlock : Bank
  residue : Bank
  residueBase : Bank

def Endpoints.term (x : Endpoints) : Fin 3 → Expr :=
  let s := rowCell x.source
  let t := rowCell x.target
  let g := Expr.lookup x.groupBlocks (rowCell x.group)
  ![rowAdd g (.lookup x.toBlock s),rowAdd g (.lookup x.toBlock t),
    rowAdd (.lookup x.residueBase s) (.lookup x.residue t)]

def Endpoints.passes (x : Endpoints) (base n : ℕ) := columns n base (List.ofFn x.term)

theorem Endpoints.work (x : Endpoints) (i : Fin 3) : (x.term i).work≤32 := by
  fin_cases i <;> norm_num [Endpoints.term,rowCell,rowAdd,Expr.work]

theorem Endpoints.clock (x : Endpoints) (base n : ℕ) :
    ProtocolRAM.clock (x.passes base n) ≤ 16+204*n := by
  have cal := columns_clock n base 32 (List.ofFn x.term) (by
    intro e member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    exact x.work i)
  exact cal.trans_eq (by rw [List.length_ofFn];ring)

def Endpoints.words {n m B groups : ℕ} {G : Type} (p : Tiles (Fin n) G m) (pos : 0<B)
    (encode : G ↪ Fin groups) (r : Fin n) : Fin 3 → ℕ :=
  ![(finProdFinEquiv (encode (p.group r),(leftBlock p pos r).2)).val,
    (finProdFinEquiv (encode (p.group r),(rightBlock p pos r).2)).val,
    (finProdFinEquiv (maskIndex p pos r)).val]

structure Endpoints.Stored {n m B groups w : ℕ} {G : Type}
    (x : Endpoints) (p : Tiles (Fin n) G m) (pos : 0<B) (encode : G ↪ Fin groups)
    (mem : Memory w) : Prop where
  group : Resident x.group mem (fun r => (encode (p.group r)).val)
  source : Resident x.source mem (fun r => (p.input r).val)
  target : Resident x.target mem (fun r => (p.output r).val)
  groupBlocks : Resident x.groupBlocks mem (fun g : Fin groups => blocks m B*g.val)
  toBlock : Resident x.toBlock mem (fun i : Fin m => (decode m B pos i).1.val)
  residue : Resident x.residue mem (fun i : Fin m => (decode m B pos i).2.val%(B^2))
  residueBase : Resident x.residueBase mem (fun i : Fin m => B^2*((decode m B pos i).2.val%(B^2)))

theorem Endpoints.evaluate {n m B groups w : ℕ} {G : Type} (x : Endpoints)
    (p : Tiles (Fin n) G m) (pos : 0<B) (encode : G ↪ Fin groups) (mem : Memory w)
    (stored : x.Stored p pos encode mem) (r : Fin n) (i : Fin 3) :
    (x.term i).eval mem (r.val : Word w) = (Endpoints.words p pos encode r i : Word w) := by
  have g := stored.group r
  have s := stored.source r
  have t := stored.target r
  have gb := stored.groupBlocks (encode (p.group r))
  have sb := stored.toBlock (p.input r)
  have tb := stored.toBlock (p.output r)
  have sr := stored.residueBase (p.input r)
  have tr := stored.residue (p.output r)
  fin_cases i <;> simp [term,rowCell,rowAdd,Expr.eval,RowOp.opcode,BinaryOp.eval,words,
    maskIndex,leftBlock,rightBlock,finProdFinEquiv,g,s,t,gb,sb,tb,sr,tr,add_comm]

/-- This pass reads the parent geometry before any color has been chosen.
Its output banks feed the single-record chooser in increasing ordinal order. -/
theorem Endpoints.emit {n m B groups w base src : ℕ} {G : Type} (x : Endpoints)
    (p : Tiles (Fin n) G m) (pos : 0<B) (encode : G ↪ Fin groups) (mem : Memory w)
    (stored : x.Stored p pos encode mem) (before : src≤base) (reads : ∀ i,(x.term i).Fits w src)
    (room : base+3*n<2^w) :
    let ps := x.passes base n
    (program w ps).Exec mem (result ps mem) (ProtocolRAM.clock ps) ∧
      ∀ (r : Fin n) (i : Fin 3), result ps mem (base+i.val*n+r.val) =
        (Endpoints.words p pos encode r i : Word w) := by
  have read : ∀ e∈List.ofFn x.term,e.Fits w src := by
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact reads i
  refine ⟨columns_exec _ _ (columns_safe _ before read (by simpa using room)),?_⟩
  intro r i
  have v := columns_read (List.ofFn x.term) mem before read i.val (by simp) r
  simp only [List.getElem_ofFn] at v
  exact v.trans (x.evaluate p pos encode mem stored r i)

end Hierarchy.ProbeStage.Native

end OAI
