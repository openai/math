import OAI.Hierarchy.ProbeRouteOccurrences
import OAI.Hierarchy.ProtocolRAMWeightedScatter
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMControl

namespace OAI
/-! # Native aggregation of final widths on the original priced physical edges -/

namespace Hierarchy.ProtocolRAM.RouteSettlement
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open AdaptiveProbe
open scoped BigOperators Fin.CommRing
noncomputable section

variable {w r edges : ℕ} {I C : Type*} [Fintype I] [Fintype C]

structure Banks where
  width : Bank
  kind : Bank
  index : Bank
  stock : Bank
  reserved : Bank
  used : Bank

/-- The two physical source words are an absolute edge address and its arriving stock.
The route directory tells each odd row which previously computed stock word to read. -/
def words (b : Banks) : Expr :=
  let k := Expr.lookup b.kind .row
  let i := Expr.lookup b.index .row
  .branch .eq k (.lit 0) (.op .add (.lit b.width.base) i)
    (.branch .eq k (.lit 1) (.lookup b.stock i)
      (.op .sub (.lookup b.reserved i) (.lookup b.used i)))

def code (w src n : ℕ) (b : Banks) : Procedure w :=
  (scan w src (2*n) (words b)).seq (ProtocolRAMWeightedScatter.program w src n)

def ticks (n : ℕ) (b : Banks) := (4+2*n*(2*(words b).work+4))+(3+12*n)

theorem words_work (b : Banks) : (words b).work=64 := rfl

theorem ticks_eq (b : Banks) (n : ℕ) : ticks n b=7+276*n := by
  rw [ticks,words_work]
  omega

attribute [local irreducible] CheapCode

theorem cheap (w src n : ℕ) (b : Banks) : CheapCode (code w src n b) := by
  unfold code
  have scatter : CheapCode (ProtocolRAMWeightedScatter.program w src n) := by
    unfold CheapCode
    exact @ProtocolRAMWeightedScatter.cheap w src n
  exact @cheap_seq w (scan w src (2*n) (words b)) (ProtocolRAMWeightedScatter.program w src n)
    (@scan_cheap w src (2*n) (words b)) scatter

variable {core : I → List (Fin edges)} {center : C → List (Fin edges)}

def oddKind : RouteOccurrence core center → ℕ
  | .inl _ => 1
  | .inr _ => 2

def resource (ci : I → ℕ) (cj : C → ℕ) : RouteOccurrence core center → ℕ
  | .inl ⟨i,_⟩ => ci i
  | .inr ⟨c,_⟩ => cj c

structure Directory (b : Banks) (m : Memory w) (enum : Fin r ≃ RouteOccurrence core center)
    (ci : I → ℕ) (cj : C → ℕ) : Prop where
  headKind : ∀ i : Fin r, b.kind.read m ((2*i.val:ℕ):Word w)=0
  headIndex : ∀ i : Fin r,b.index.read m ((2*i.val:ℕ):Word w)=((enum i).edge.val:Word w)
  tailKind : ∀ i : Fin r,b.kind.read m ((2*i.val+1:ℕ):Word w)=(oddKind (enum i):Word w)
  tailIndex : ∀ i : Fin r,b.index.read m ((2*i.val+1:ℕ):Word w)=(resource ci cj (enum i):Word w)

/-- The amount assigned to a core or a catalyst occurrence comes from the actual final words. -/
def actual (bank : Bank) (m : Memory w) (i : ℕ) := (bank.read m (i:Word w)).val

def address (b : Banks) (enum : Fin r ≃ RouteOccurrence core center) (i : Fin r) :=
  b.width.base+(enum i).edge.val

def weight (b : Banks) (m : Memory w) (enum : Fin r ≃ RouteOccurrence core center)
    (ci : I → ℕ) (cj : C → ℕ) (i : Fin r) :=
  (enum i).weight (fun j => actual b.stock m (ci j)) (fun j => actual b.reserved m (cj j))
    (fun j => actual b.used m (cj j))

def output (b : Banks) (src : ℕ) (m : Memory w) (enum : Fin r ≃ RouteOccurrence core center)
    (ci : I → ℕ) (cj : C → ℕ) :=
  ProtocolRAMWeightedScatter.image (address b enum) (weight b m enum ci cj)
    (image src (2*r) (words b) m) r

private theorem head_word (b : Banks) (m : Memory w) (row j : Word w)
    (kind : b.kind.read m row = 0) (index : b.index.read m row = j) :
    (words b).eval m row = (b.width.base : Word w) + j := by
  simp [words, Expr.eval, Comparison.test, kind, index, RowOp.opcode, BinaryOp.eval]

private theorem stock_word (b : Banks) (m : Memory w) (row j : Word w) (one : (1:Word w) ≠ 0)
    (kind : b.kind.read m row = 1) (index : b.index.read m row = j) :
    (words b).eval m row = b.stock.read m j := by
  simp [words, Expr.eval, Comparison.test, kind, index, one]

private theorem return_word (b : Banks) (m : Memory w) (row j : Word w)
    (two : (2:Word w) ≠ 0) (diff : (2:Word w) ≠ 1)
    (kind : b.kind.read m row = 2) (index : b.index.read m row = j) :
    (words b).eval m row = b.reserved.read m j - b.used.read m j := by
  simp [words, Expr.eval, Comparison.test, kind, index, two, diff, RowOp.opcode, BinaryOp.eval]

omit [Fintype I] [Fintype C] in
theorem exec (b : Banks) (src : ℕ) (m : Memory w) (enum : Fin r ≃ RouteOccurrence core center)
    (ci : I → ℕ) (cj : C → ℕ) (directory : Directory b m enum ci cj)
    (fits : (words b).Fits w src) (tape : src+2*r<2^w)
    (space : b.width.base+edges≤ src) (wide : 2<2^w)
    (available : ∀ c,actual b.used m (cj c)≤actual b.reserved m (cj c)) :
    (code w src r b).Exec m (output b src m enum ci cj) (ticks r b) := by
  let mounted := image src (2*r) (words b) m
  have scanRun : (scan w src (2*r) (words b)).Exec m mounted (4+2*r*(2*(words b).work+4)) :=
    scan_exec src (2*r) (words b) m fits tape
  have below (i : Fin r) : address b enum i<src := by
    have := (enum i).edge.isLt
    unfold address
    omega
  have scatterRun := ProtocolRAMWeightedScatter.run src (address b enum) (weight b m enum ci cj) mounted
    tape.le (fun i => by have := below i; omega) (fun i => .inl (below i))
  apply scanRun.then
  apply scatterRun
  intro i
  have lt := i.isLt
  have h0 := ProtocolRAMGeneratedWrite.read_image src (2*r) (words b) m ⟨2*i.val,by omega⟩
  have h1 := ProtocolRAMGeneratedWrite.read_image src (2*r) (words b) m ⟨2*i.val+1,by omega⟩
  constructor
  · rw [show mounted (src+2*i.val)=(words b).eval m ((2*i.val:ℕ):Word w) from h0]
    rw [head_word b m _ _ (directory.headKind i) (directory.headIndex i)]
    exact (Nat.cast_add b.width.base (enum i).edge.val).symm
  · rw [show mounted (src+2*i.val+1)=(words b).eval m ((2*i.val+1:ℕ):Word w) by
      simpa only [Nat.add_assoc] using h1]
    have one : (1:Word w)≠0 := by intro h; have := congrArg Fin.val h; simp [Nat.mod_eq_of_lt (show 1<2^w by omega)] at this
    have two : (2:Word w)≠0 := by intro h; have := congrArg Fin.val h; simp [Nat.mod_eq_of_lt wide] at this
    have diff : (2:Word w)≠1 := by intro h; have := congrArg Fin.val h; simp [Nat.mod_eq_of_lt wide,Nat.mod_eq_of_lt (show 1<2^w by omega)] at this
    cases h : enum i with
    | inl a =>
      rcases a with ⟨j,q⟩
      have kind := directory.tailKind i
      have index := directory.tailIndex i
      rw [h] at kind index
      rw [stock_word b m _ (ci j : Word w) one kind index]
      simp [weight,h,RouteOccurrence.weight,actual]
    | inr a =>
      rcases a with ⟨j,q⟩
      have kind := directory.tailKind i
      have index := directory.tailIndex i
      rw [h] at kind index
      rw [return_word b m _ (cj j : Word w) two diff kind index]
      simp only [weight,h,RouteOccurrence.weight]
      rw [Nat.cast_sub (available j)]
      simp only [actual,Fin.cast_val_eq_self]

/-- This is the equation used for every individual physical edge by `reported_route_price`. -/
theorem width_read (b : Banks) (src : ℕ) (m : Memory w) (enum : Fin r ≃ RouteOccurrence core center)
    (ci : I → ℕ) (cj : C → ℕ) (e : Fin edges) (space : b.width.base+edges≤ src)
    (room : (m (b.width.base+e.val)).val +
      (routeLoad core (fun j => actual b.stock m (ci j)) e +
       routeLoad center (fun j => actual b.reserved m (cj j)-actual b.used m (cj j)) e) < 2^w) :
    (output b src m enum ci cj (b.width.base+e.val)).val = (m (b.width.base+e.val)).val +
      routeLoad core (fun j => actual b.stock m (ci j)) e +
      routeLoad center (fun j => actual b.reserved m (cj j)-actual b.used m (cj j)) e := by
  have seed := ProtocolRAMGeneratedWrite.frame_image src (2*r) (words b) m
    (b.width.base+e.val) (.inl (by have := e.isLt; omega))
  have loads : (∑ i : Fin r,if address b enum i=b.width.base+e.val then weight b m enum ci cj i else 0) =
      routeLoad core (fun j => actual b.stock m (ci j)) e +
      routeLoad center (fun j => actual b.reserved m (cj j)-actual b.used m (cj j)) e := by
    rw [← route_occurrences_sum]
    simpa only [address,weight,Nat.add_right_inj,Fin.val_inj] using
      enum.sum_comp (fun o => if o.edge=e then o.weight (fun j => actual b.stock m (ci j))
        (fun j => actual b.reserved m (cj j)) (fun j => actual b.used m (cj j)) else 0)
  unfold output
  rw [ProtocolRAMWeightedScatter.read_nat,seed,loads,Nat.add_assoc]
  simpa only [seed,loads] using room

/-- Input descriptors retain their other six columns. The width lookup uses the edge
ordinal shared by the cash account, the core route, and the catalyst return route. -/
def fields (b : Banks) (geometry : Fin 7 → Expr) : Fin 7 → Expr :=
  Function.update geometry 4 (.lookup b.width .row)

omit [Fintype I] [Fintype C] in
theorem output_below (b : Banks) (src : ℕ) (m : Memory w)
    (enum : Fin r ≃ RouteOccurrence core center) (ci : I → ℕ) (cj : C → ℕ) (a : ℕ)
    (below : a<b.width.base) (space : b.width.base+edges≤ src) :
    output b src m enum ci cj a=m a := by
  unfold output
  rw [ProtocolRAMWeightedScatter.frame _ _ _ _ _ (by intro i; unfold address; omega)]
  exact ProtocolRAMGeneratedWrite.frame_image src (2*r) (words b) m a (.inl (by omega))

omit [Fintype I] [Fintype C] in
theorem geometry_read (b : Banks) (src : ℕ) (m : Memory w)
    (enum : Fin r ≃ RouteOccurrence core center) (ci : I → ℕ) (cj : C → ℕ)
    (geo : Fin 7 → Expr) (i : Fin edges) (j : Fin 7) (keep : j≠4)
    (fits : (geo j).Fits w b.width.base) (space : b.width.base+edges≤ src) :
    (reportedRows [] (fields b geo) (output b src m enum ci cj) i).field j =
      ((geo j).eval m (i.val:Word w)).val := by
  rw [reportedRows,rowAt_field]
  simp only [fields,Function.update_of_ne keep,result]
  exact congrArg Fin.val (eval_below (geo j) _ m _ fits
    (fun a h => output_below b src m enum ci cj a h space))

theorem reported_width (b : Banks) (src : ℕ) (m : Memory w)
    (enum : Fin r ≃ RouteOccurrence core center) (ci : I → ℕ) (cj : C → ℕ)
    (geo : Fin 7 → Expr) (e : Fin edges) (fit : edges≤b.width.size) (bound : edges≤2^w)
    (space : b.width.base+edges≤ src)
    (room : (m (b.width.base+e.val)).val +
      (routeLoad core (fun j => actual b.stock m (ci j)) e +
       routeLoad center (fun j => actual b.reserved m (cj j)-actual b.used m (cj j)) e)<2^w) :
    (reportedRows [] (fields b geo) (output b src m enum ci cj) e).width =
      (m (b.width.base+e.val)).val + routeLoad core (fun j => actual b.stock m (ci j)) e +
      routeLoad center (fun j => actual b.reserved m (cj j)-actual b.used m (cj j)) e := by
  change (((fields b geo 4).eval (output b src m enum ci cj) (e.val:Word w)).val)=_
  simp only [fields,Function.update_self,Expr.eval,Bank.read,
    Fin.val_cast_of_lt (e.isLt.trans_le bound),Nat.mod_eq_of_lt (e.isLt.trans_le fit)]
  exact width_read b src m enum ci cj e space room

def reporter (w src table dst edges occurrences : ℕ) (b : Banks) (owners : Bank)
    (geometry : Fin 7 → Expr) : Procedure w :=
  (code w src occurrences b).seq (controller w table dst edges owners [] (fields b geometry))

theorem reporter_cheap (w src table dst edges occurrences : ℕ) (b : Banks) (owners : Bank)
    (geo : Fin 7 → Expr) : CheapCode (reporter w src table dst edges occurrences b owners geo) := by
  unfold reporter
  exact @cheap_seq w (code w src occurrences b) (controller w table dst edges owners [] (fields b geo))
    (@cheap w src occurrences b) (@controller_cheap w table dst edges owners [] (fields b geo))

omit [Fintype I] [Fintype C] in
/-- End-to-end, including the original nine-word gather and the immutable edge numbering.
The total scan has one iteration per route occurrence and one per final physical row. -/
theorem reporter_exec (b : Banks) (src table dst : ℕ) (owners : Bank) (geo : Fin 7 → Expr)
    (m : Memory w) (enum : Fin r ≃ RouteOccurrence core center) (ci : I → ℕ) (cj : C → ℕ)
    (directory : Directory b m enum ci cj) (fits : (words b).Fits w src) (tape : src+2*r<2^w)
    (space : b.width.base+edges≤ src) (wide : 3<w)
    (available : ∀ c,actual b.used m (cj c)≤actual b.reserved m (cj c))
    (dir : Owners owners edges (output b src m enum ci cj))
    (inputFits : (packed owners (fields b geo)).Fits w table) (srcFit : table+8*edges<2^w)
    (dstFit : dst+9*edges<2^w) (apart : table+8*edges≤dst ∨ dst+9*edges≤table) :
    (reporter w src table dst edges r b owners geo).Exec m
      (finalMemory table dst edges owners [] (fields b geo) (output b src m enum ci cj))
      (ticks r b + ((clock [] + (report table edges owners (fields b geo)).clock)+(27+117*edges))) := by
  have one : 2<2^w := by
    have pow := Nat.pow_le_pow_right (by decide : 0<2) wide.le
    omega
  apply Procedure.Exec.then (exec b src m enum ci cj directory fits tape space one available)
  intro P R K mach pc reg pub exit installed data cfg start entry same
  exact (controller_exec table dst edges owners [] (fields b geo) (output b src m enum ci cj)
      (by simp) wide dir inputFits srcFit dstFit apart) mach pc reg pub exit installed data cfg start entry same


end
end Hierarchy.ProtocolRAM.RouteSettlement

end OAI
