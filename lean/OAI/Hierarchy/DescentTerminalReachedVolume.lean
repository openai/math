import OAI.Hierarchy.DescentTerminalReachedOrder
import OAI.Hierarchy.DescentTerminalGraphVolume

namespace OAI
/-! # The shared final-degree charge for the real terminal position and cable order -/
namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentHostDegree DescentHostDirectory DescentColonies
open DescentTerminalGraphPositions DescentTerminalCableOrder
open scoped Classical BigOperators
noncomputable section
variable {F P:Type} [Field F] [Fintype P] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits}
    {G:PoweredGadget F} {price ε:ℝ} {S:AtomSchedule} {k age z degree wire hist:ℕ}
    (R:Reached W G price ε S k age z degree wire hist) (p:ℕ) (ext:P↪ℕ)
    (ops:∀v,DescentKernelHistory.Boundary W.graph v↪ℕ)
local notation "O" => R.terminalOrder p ext ops
local notation "H" => S.hostSize age

def hostCode (a:R.V) : Fin H := (R.vertex a).castLE R.valid.host
omit [Fintype P] in
theorem hostCode_injective : Function.Injective R.hostCode := by
  intro u v same
  exact R.vertex.injective (Fin.ext (congrArg (fun i : Fin H => i.val) same))

omit [Fintype P] in
private theorem peer {J : Type} {u v : J × R.V}
    (h : u ∈ DescentHostDirectory.groupedNear R.placement.near v) :
    u.2 ∈ R.placement.near v.2 := by
  obtain ⟨t, mem, eqn⟩ := Finset.mem_map.mp h
  have same : t = u.2 := congrArg (fun x : J × R.V => x.2) eqn
  exact same ▸ mem

private def rowsAt (i:Fin H) : Finset (Option (Fin H)) :=
  if seen:∃a:R.V,R.hostCode a=i then
    insert none ((R.placement.near seen.choose).image (fun b=>some (R.hostCode b)))
  else {none}

theorem groups_le (i:Fin H) : ((O).site i).groups≤degree+1 := by
  let pool:=rowsAt R i
  have contains (g:(O).Group i) : g.val∈pool := by
    rcases g with ⟨j,hj⟩
    rcases hj with ⟨nm,hUse,atPort⟩
    cases j with
    | none=>simp only [pool,rowsAt];split <;> simp
    | some j=>
      rcases nm with ⟨e,b⟩|⟨e,b⟩
      · have edge:(O).between i j (.inl ⟨e,b⟩):=⟨hUse,atPort⟩
        rcases ((O).between_edge i j e b).mp edge with ⟨src,dst⟩|⟨dst,src⟩
        · have hs:R.hostCode (R.placement.pos (W.graph.src e)).2=i:=src
          have hd:R.hostCode (R.placement.pos (W.graph.dst e)).2=j:=dst
          have existsHost:∃u,R.hostCode u=i:=⟨_,hs⟩
          have same:=R.hostCode_injective (existsHost.choose_spec.trans hs.symm)
          simp only [pool,rowsAt,dite_eq_left existsHost,Finset.mem_insert,Option.some_ne_none,false_or]
          rw [same];exact Finset.mem_image.mpr ⟨_,peer R (R.placement.peers e).1,congrArg some hd⟩
        · have hd:R.hostCode (R.placement.pos (W.graph.dst e)).2=i:=dst
          have hs:R.hostCode (R.placement.pos (W.graph.src e)).2=j:=src
          have existsHost:∃u,R.hostCode u=i:=⟨_,hd⟩
          have same:=R.hostCode_injective (existsHost.choose_spec.trans hd.symm)
          simp only [pool,rowsAt,dite_eq_left existsHost,Finset.mem_insert,Option.some_ne_none,false_or]
          rw [same];exact Finset.mem_image.mpr ⟨_,peer R (R.placement.peers e).2,congrArg some hs⟩
      · simp [Order.neighbor] at atPort
  have bound : pool.card≤degree+1 := by
    unfold pool rowsAt
    split
    · rename_i hx
      have a:=Finset.card_insert_le none ((R.placement.near hx.choose).image (fun b=>some (R.hostCode b)))
      have b:=Finset.card_image_le (s:=R.placement.near hx.choose) (f:=fun b=>some (R.hostCode b))
      have c:=R.placement.degreeBound hx.choose
      rw [R.branch] at c
      omega
    · simp
  have size:=Fintype.card_le_of_embedding (⟨fun g:(O).Group i=>⟨g.val,contains g⟩,fun _ _ eq=>Subtype.ext (congrArg (fun z : ↥pool => z.val) eq)⟩ : (O).Group i ↪ ↥pool)
  change Fintype.card ((O).Group i)≤degree+1
  exact (by simpa using size : Fintype.card ((O).Group i)≤pool.card).trans bound

theorem paid_rows {q:ℕ} (positive:0<q) :
    (∑i,((O).site i).rows q)*q≤3*DescentTerminalGraphVolume.bundleBudget (p:=p) W.graph+(degree+3)*H*q := by
  have cost:=DescentTerminalGraphVolume.paid_rows O positive
  have total:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>groups_le R p ext ops i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  have next:(∑i,((O).site i).groups)+2*H≤(degree+3)*H:=by nlinarith only [total]
  exact cost.trans (Nat.add_le_add_left (Nat.mul_le_mul_right q next) _)

end
end Hierarchy.DescentSixParty.Reached

end OAI
