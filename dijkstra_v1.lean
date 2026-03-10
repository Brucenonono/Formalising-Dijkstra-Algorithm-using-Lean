import Mathlib

/-
# 1. set up environment and algorithm components
-/
-- V is our finite vertex set
variable {V : Type} [Fintype V] [DecidableEq V]

structure WeightedGraph (V : Type) [Fintype V] [DecidableEq V] where
  G : SimpleGraph V
  -- define weight function on extended real, let be ⊤ if not reachable
  weight : V → V → ENNReal
  no_edge : ∀ u v, ¬G.Adj u v → weight u v = ⊤
  source : V

structure DijkstraState (V : Type) where
  visited   : Finset V
  distances : V → ENNReal

namespace WeightedGraph

/-
# 2. the algorithm
-/
-- Add a new vertex into our state, greedy step
def choose_next (state : DijkstraState V) : V :=
  -- In a formal proof, you'd use 'argmin' over the set (univ \ state.visited)
  ⊓ (p : List V) ()

-- The relaxation step: updating neighbors
noncomputable def relax (inst : WeightedGraph V)
(state : DijkstraState V) (u : V) : V → ENNReal :=
  λ v => min (state.distances v) (state.distances u + inst.weight u v)

-- Recursive loop
noncomputable def run_loop (inst : WeightedGraph V) (state : DijkstraState V) : DijkstraState V :=
  if h : state.visited.card < Fintype.card V then
    let u := inst.choose_next state

    -- 1. We must 'prove' u is not already visited to satisfy the compiler
    have h_u : u ∉ state.visited := by
      -- This proof depends on your choose_next implementation
      -- Logically: choose_next picks from (univ \ visited)
      sorry

    let next_state : DijkstraState V := {
      visited := insert u state.visited, -- Using insert is cleaner than ∪ {u}
      distances := inst.relax state u
    }

    run_loop inst next_state
  else
    state
termination_by Fintype.card V - state.visited.card
decreasing_by
  -- 2. This block proves the termination measure strictly decreases
  simp_wf
  apply Nat.sub_lt_sub_left h
  apply Finset.card_lt_insert h_u

-- Actual shortest path
def is_path_weight (inst : WeightedGraph V) (u v : V) (p : List V) : ENNReal :=
  -- Sum of weights along the list of vertices
  sorry

-- finding such infimum is noncomputable
noncomputable def shortest_path_dist (inst : WeightedGraph V) (v : V) : ENNReal :=
  ⨅ (p : List V) (h : inst.G.IsPath inst.source v p), is_path_weight inst inst.source v p


/-
# 2. The Formal Theorem
The output of `run_loop` matches the mathematical infimum `shortest_path_dist`.
-/

/-
### 3. The Logical Bridge (Correctness Proof Flow)
We define the invariant and the lemmas required to prove the theorem.
-/

/--
  The Loop Invariant:
  For visited nodes, the distance is the absolute shortest path.
  For unvisited nodes, the distance is the shortest 'restricted' path.
-/
def is_invariant (inst : WeightedGraph V) (state : DijkstraState V) : Prop :=
  (∀ v ∈ state.visited, state.distances v = inst.shortest_path_dist v) ∧
  (∀ v ∉ state.visited, state.distances v =
    ⨅ (p : List V) (h_path : inst.G.IsPath inst.source v p)
      (h_int : ∀ x ∈ p.init, x ∈ state.visited), path_weight inst p)

-- Lemma 1: The starting state satisfies the invariant.
lemma init_invariant (inst : WeightedGraph V) :
  is_invariant inst (inst.initial_state) := by sorry

-- Lemma 2: Selecting the minimum distance unvisited node preserves optimality (Greedy Choice).
lemma greedy_choice_correct (inst : WeightedGraph V) (state : DijkstraState V) (u : V) :
  is_invariant inst state →
  u = inst.choose_next state →
  u ∉ state.visited →
  state.distances u = inst.shortest_path_dist u := by sorry

-- Lemma 3: Relaxing edges updates the frontier correctly.
lemma relax_preserves_invariant (inst : WeightedGraph V) (state : DijkstraState V) (u : V) :
  is_invariant inst state →
  u = inst.choose_next state →
  is_invariant inst ({ visited := state.visited ∪ {u}, distances := inst.relax state u }) := by sorry

-- Lemma 4: The final state of run_loop has all vertices visited.
lemma run_loop_visits_all (inst : WeightedGraph V) (state : DijkstraState V) :
  (inst.run_loop state).visited = Finset.univ := by sorry

/-!
### 4. The Final Theorem
Combining the lemmas to show the algorithm is correct.
-/
theorem dijkstra_correct (inst : WeightedGraph V) :
  let final_state := inst.run_loop (inst.initial_state)
  ∀ v, final_state.distances v = inst.shortest_path_dist v :=
by
  intro v
  let final := inst.run_loop (inst.initial_state)

  -- 1. Show the invariant holds through the entire loop
  have h_inv : is_invariant inst final := by
    -- Proof by induction on run_loop using relax_preserves_invariant
    sorry

  -- 2. Show that at the end, every vertex is in the visited set
  have h_all : v ∈ final.visited := by
    rw [run_loop_visits_all]
    apply Finset.mem_univ

  -- 3. Use the first part of the invariant to conclude distances are correct
  exact h_inv.1 v h_all



def initial_state (s : V): DijkstraState V := {
  visited := ∅
  distances := (λ v => if v = s then 0 else ⊤)
}

theorem Dijkstra (inst : WeightedGraph V) :
  let final_state := inst.run_loop (initial_state inst.source)
  ∀ v, final_state.distances v = inst.shortest_path_dist v :=
by
  -- The proof would proceed by induction on the size of the 'visited' set
  sorry



end WeightedGraph
