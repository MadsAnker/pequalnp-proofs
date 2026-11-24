import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1735_812
  (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset (Sym2 (Fin n))), NoFourCycle G →
    (∀ e ∈ E, ∃ u v : Fin n, e = s(u, v) ∧ ∃ g < C.gates.length,
      (∃ b : Fin 2, orIn n C (opnd C g b) = {v} ∧ 2 ≤ (orIn n C (n + g)).card ∧
        ∀ w ∈ orIn n C (n + g), G.Adj u w) ∨
      (side C g 0 = {u} ∧ side C g 1 = {v})) → E.card ≤ 3 * C.size)
  (remaining : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
    ((Ustar G C).filter (fun e => ¬ (∃ u v : Fin n, e = s(u, v) ∧ ∃ g < C.gates.length,
      (∃ b : Fin 2, orIn n C (opnd C g b) = {v} ∧ 2 ≤ (orIn n C (n + g)).card ∧
        ∀ w ∈ orIn n C (n + g), G.Adj u w) ∨
      (side C g 0 = {u} ∧ side C g 1 = {v})))).card ≤ c * (C.size + 1)) :
∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [_x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c, bound⟩ := remaining
  refine ⟨3 + c, ?_⟩
  intro n G _ girth edge C least top
  classical
  have noFour : NoFourCycle G := by
    intro a b hab
    by_contra! tooMany
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp tooMany
    obtain ⟨_, hax, hbx⟩ := Finset.mem_filter.mp hx
    obtain ⟨_, hay, hby⟩ := Finset.mem_filter.mp hy
    have ax := G.ne_of_adj hax
    have xb := G.ne_of_adj hbx.symm
    have by' := G.ne_of_adj hby
    have ya := G.ne_of_adj hay.symm
    have cycle : (SimpleGraph.Walk.cons hax (SimpleGraph.Walk.cons hbx.symm
        (SimpleGraph.Walk.cons hby (SimpleGraph.Walk.cons hay.symm SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      constructor
      · simp [SimpleGraph.Walk.cons_isPath_iff, xb, by', ya, hxy, Ne.symm ax, Ne.symm hab]
      · simp [ax, xb, hab, hxy, Ne.symm ax, Ne.symm ya]
    have impossible := girth a _ cycle
    simp at impossible
  let good (e : Sym2 (Fin n)) : Prop :=
    ∃ u v : Fin n, e = s(u, v) ∧ ∃ g < C.gates.length,
      (∃ b : Fin 2, orIn n C (opnd C g b) = {v} ∧ 2 ≤ (orIn n C (n + g)).card ∧
        ∀ w ∈ orIn n C (n + g), G.Adj u w) ∨
      (side C g 0 = {u} ∧ side C g 1 = {v})
  have hGood : ((Ustar G C).filter good).card ≤ 3 * C.size :=
    charge n G C _ noFour (fun e he => (Finset.mem_filter.mp he).2)
  have hRest : ((Ustar G C).filter (fun e => ¬ good e)).card ≤ c * (C.size + 1) :=
    bound n G girth edge C least top
  have hSplit := Finset.card_filter_add_card_filter_not (s := Ustar G C) good
  rw [Nat.add_mul]
  omega
