import combinatorics.simple_graph.coloring


--OUTPUT 1
theorem graph_2_colorable {G : Type*} [graph G] : (∃ c : G → ℤ, c G = 2) ↔ ∃ V1 V2 : set G, bipartite_graph G V1 V2 :=
begin
  -- ...
end

--OUTPUT 2
theorem bipartite_graph_two_colorable {G : Type} [graph G] : 2-colorable G ↔ bipartite G :=
begin
  -- $G$ is 2-colorable, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color.
  have h1 : 2-colorable G → ∃ (R : set G) (B : set G), ∀ v : G, v ∈ R ∨ v ∈ B ∧ ∀ e : edge G, (e.1 ∈ R ∧ e.2 ∈ B) ∨ (e.1 ∈ B ∧ e.2 ∈ R), from by auto [two_colorable_def],

  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
  have h2 : 2-colorable G → ∃ (A : set G) (B : set G), ∀ v : G, v ∈ A ∨ v ∈ B ∧ ∀ e : edge G, (e.1 ∈ A ∧ e.2 ∈ B) ∨ (e.1 ∈ B ∧ e.2 ∈ A), from by auto [two_colorable_def, h1],

  -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
  have h3 : 2-colorable G → ∃ (A : set G) (B : set G), ∀ v : G, v ∈ A ∨ v ∈ B ∧ ∀ e : edge G, (e.1 ∈ A ∧ e.2 ∈ B) ∨ (e.1 ∈ B ∧ e.2 ∈ A) ∧ ∀ e : edge G, e.1 ∉ A ∨ e.2 ∉ A ∧ e.1 ∉ B ∨ e.2 ∉ B, from by auto [h2, two_colorable_def],

  -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  have h4 : 2-colorable G → bipartite G, from by auto [h3, bipartite_def],

  show 2-colorable G ↔ bipartite G, from by auto [h4, two_colorable_def, bipartite_def],
end

--OUTPUT 3
theorem bipartite_graph_is_two_colorable (G : Type*) [graph G] : ∀ A B : set G,
  is_bipartite_graph_aux G A B ↔ is_two_colorable_graph_aux G A B :=
begin
  -- Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color. Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue. Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$. This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  assume (A : set G) (B : set G),
  split,
    -- Suppose $G$ is 2-colorable, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color.
    assume h1 : is_two_colorable_graph_aux G A B,
    -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
    -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
    have h2 : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ E x y, from by auto [h1.2],
    have h3 : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ¬ E x y, from by auto [h1.3],
    -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
    have h4 : ∀ x ∈ A, ∀ y ∈ B, x ≠ y → E x y, from by auto [h1.1],

    show is_bipartite_graph_aux G A B, from by auto [is_bipartite_graph_aux, h2, h3, h4],

    -- Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$. Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable.
    assume h1 : is_bipartite_graph_aux G A B,
    -- Suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$.
    -- Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable.
    -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
    have h2 : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ E x y, from by auto [h1.1],
    have h3 : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ¬ E x y, from by auto [h1.2],
    -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
    have h4 : ∀ x ∈ A, ∀ y ∈ B, x ≠ y → E x y, from by auto [h1.3],

    show is_two_colorable_graph_aux G A B, from by auto [is_two_colorable_graph_aux, h2, h3, h4],
end

--OUTPUT 4
theorem bipartite_graph_two_colorable {G : Type*} : G.two_colorable ↔ G.bipartite :=
begin
  -- Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue,
  -- and no edge will have both endpoints colored the same color.
  assume h1 : G.two_colorable,
  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
  have h2 : ∃ A B : set G.V, (∀ v : G.V, v ∈ A ∨ v ∈ B) ∧ (∀ v : G.V, v ∈ A → ¬ (v ∈ B)) ∧ (∀ v : G.V, v ∈ B → ¬ (v ∈ A)) ∧ (∀ v w : G.V, (v ≠ w) → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A)), from by auto using [h1, two_colorable.def],
  -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
  have h3 : ∀ v w : G.V, v ∈ A → w ∈ A → (v, w) ∉ G.E, from by auto using [h2],
  have h4 : ∀ v w : G.V, v ∈ B → w ∈ B → (v, w) ∉ G.E, from by auto using [h2],
  -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  have h5 : ∀ v w : G.V, (v, w) ∈ G.E → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A), from by auto using [h2, h3, h4],
  show G.bipartite, from by auto using [bipartite.def, h2, h5],
  -- Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$
  -- every edge has one endpoint in $V_{1}$ and the other in $V_{2}$.
  assume h1 : G.bipartite,
  have h2 : ∃ A B : set G.V, (∀ v : G.V, v ∈ A ∨ v ∈ B) ∧ (∀ v : G.V, v ∈ A → ¬ (v ∈ B)) ∧ (∀ v : G.V, v ∈ B → ¬ (v ∈ A)) ∧ (∀ v w : G.V, (v ≠ w) → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A)), from by auto using [h1, bipartite.def],
  -- Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring,
  have h3 : ∀ v : G.V, v ∈ A → (∀ w : G.V, (v, w) ∈ G.E → w ∉ A), from by auto using [h2],
  have h4 : ∀ v : G.V, v ∈ B → (∀ w : G.V, (v, w) ∈ G.E → w ∉ B), from by auto using [h2],
  -- so $G$ is 2-colorable.
  show G.two_colorable, from by auto using [two_colorable.def, h2, h3, h4],
end

--OUTPUT 5
theorem bipartite_if_two_colorable {G : Type*} [graph G] (h1 : is_bipartite G) : is_two_colorable G :=
begin
  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
  have h2 : ∃ A B : set G, is_coloring G A B, from by auto [h1],
  obtain A B h3, from h2,
  -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
  have h4 : ∀ (u v : G), u ∈ A → v ∈ A → ¬ edge G u v, from by auto [h3],
  have h5 : ∀ (u v : G), u ∈ B → v ∈ B → ¬ edge G u v, from by auto [h3],
  -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  show is_bipartite G, from by auto [h1, h3, h4, h5],
end

--OUTPUT 6
theorem bipartite_iff_two_colorable (G : Type*) [graph G] : bipartite G ↔ two_colorable G :=
begin
  -- There exists a subset $A$ of vertices of $G$ such that there are no edges within $A$ and all edges with one endpoint in $A$ have the other endpoint in $B$
  have h1 : bipartite G → ∃ A : set G, no_edges_in A ∧ (∀ (a : G) (b : G), a ∈ A ∧ (a,b) ∈ E G → b ∈ B G), from by auto [bipartite],
  -- There exists a subset $B$ of vertices of $G$ such that there are no edges within $B$ and all edges with one endpoint in $B$ have the other endpoint in $A$
  have h2 : bipartite G → ∃ B : set G, no_edges_in B ∧ (∀ (a : G) (b : G), a ∈ B ∧ (a,b) ∈ E G → b ∈ A G), from by auto [bipartite],

  -- If $G$ is 2-colorable, then we can color every vertex either red or blue, and no edge will have both endpoints colored the same color
  have h3 : two_colorable G → ∃ (r : set G) (b : set G), no_edges_in r ∧ no_edges_in b ∧ (∀ (a : G) (b : G), a ∈ r ∧ b ∈ r → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ b ∧ b ∈ b → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ r ∧ b ∈ b → (a,b) ∈ E G), from by auto [two_colorable],

  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue
  have h4 : two_colorable G → ∀ (r : set G) (b : set G), no_edges_in r ∧ no_edges_in b ∧ (∀ (a : G) (b : G), a ∈ r ∧ b ∈ r → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ b ∧ b ∈ b → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ r ∧ b ∈ b → (a,b) ∈ E G) → ∃ A : set G, no_edges_in A ∧ (∀ (a : G) (b : G), a ∈ A ∧ (a,b) ∈ E G → b ∈ B G), from by auto [h3],

  -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$
  have h5 : two_colorable G → ∀ (r : set G) (b : set G), no_edges_in r ∧ no_edges_in b ∧ (∀ (a : G) (b : G), a ∈ r ∧ b ∈ r → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ b ∧ b ∈ b → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ r ∧ b ∈ b → (a,b) ∈ E G) → ∃ B : set G, no_edges_in B ∧ (∀ (a : G) (b : G), a ∈ B ∧ (a,b) ∈ E G → b ∈ A G), from by auto [h3],
  -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite
  have h6 : two_colorable G → ∀ (r : set G) (b : set G), no_edges_in r ∧ no_edges_in b ∧ (∀ (a : G) (b : G), a ∈ r ∧ b ∈ r → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ b ∧ b ∈ b → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ r ∧ b ∈ b → (a,b) ∈ E G) → bipartite G, from by auto [h3],

  -- Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$
  have h7 : bipartite G → ∃ (A : set G) (B : set G), no_edges_in A ∧ no_edges_in B ∧ (∀ (a : G) (b : G), a ∈ A ∧ b ∈ A → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ B ∧ b ∈ B → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ A ∧ b ∈ B → (a,b) ∈ E G), from by auto [h1, h2],
  -- Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable
  have h8 : bipartite G → ∀ (A : set G) (B : set G), no_edges_in A ∧ no_edges_in B ∧ (∀ (a : G) (b : G), a ∈ A ∧ b ∈ A → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ B ∧ b ∈ B → (a,b) ∉ E G) ∧ (∀ (a : G) (b : G), a ∈ A ∧ b ∈ B → (a,b) ∈ E G) → two_colorable G, from by auto [h7],

  show bipartite G ↔ two_colorable G, from by auto [h3, h7],
end

--OUTPUT 7
theorem graph_bipartite_two_colorable (G : Type*) [graph G] : two_colorable G ↔ bipartite G :=
begin
  -- $G$ is 2-colorable graph
  assume h1 : two_colorable G,

  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
  have h2 : ∃ A B : set G, ∀ v : G, (v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A), from by auto [h1],
  cases h2 with A h2,
  cases h2 with B h2,

  -- Since all vertices of $A$ are red, there are no edges within $A$
  have h3 : ∀ a b : G, (a ∈ A ∧ b ∈ A) → (a,b) ∉ E, from by auto [h2],

  -- Similarly for $B$
  have h4 : ∀ a b : G, (a ∈ B ∧ b ∈ B) → (a,b) ∉ E, from by auto [h2],

  -- This implies that every edge has one endpoint in $A$ and the other in $B$
  have h5 : ∀ a b : G, (a,b) ∈ E → ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)), from by auto [h3, h4],

  -- which means $G$ is bipartite.
  have h6 : bipartite G, from by auto [h2, h5],

  show two_colorable G ↔ bipartite G, from by auto [h6] using [iff_def],
end

--OUTPUT 8
theorem bipartite_graph_two_colorable {G : Type*} : bipartite G ↔ two_colorable G :=
begin
  -- $G$ is 2-colorable, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color.
  have h1 : two_colorable G → ∃ A B : set G, (∀ a : G, a ∈ A ∨ a ∈ B) ∧ (∀ a : G, (a ∈ A ∧ a ∈ B) → false) ∧ (∀ a b : G, (a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)), from by auto using [two_colorable.def, two_colorable.def],

  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
  have h2 : two_colorable G → ∃ A B : set G, (∀ a : G, a ∈ A ∨ a ∈ B) ∧ (∀ a : G, (a ∈ A ∧ a ∈ B) → false) ∧ (∀ a b : G, (a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) ∧ (∀ a : G, a ∈ A ∨ a ∈ B) ∧ (∀ a : G, (a ∈ A ∧ a ∈ B) → false) ∧ (∀ a b : G, (a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)), from by auto [h1],

  -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
  have h3 : two_colorable G → ∃ A B : set G, (∀ a : G, a ∈ A ∨ a ∈ B) ∧ (∀ a : G, (a ∈ A ∧ a ∈ B) → false) ∧ (∀ a b : G, (a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) ∧ (∀ a : G, a ∈ A ∨ a ∈ B) ∧ (∀ a : G, (a ∈ A ∧ a ∈ B) → false) ∧ (∀ a b : G, (a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) ∧ (∀ a b : G, (a ∈ A ∧ a ∈ A) ∨ (b ∈ B ∧ b ∈ B) → false), from by auto using [h2],

  -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  have h4 : two_colorable G → ∃ A B : set G, (∀ a : G, a ∈ A ∨ a ∈ B) ∧ (∀ a : G, (a ∈ A ∧ a ∈ B) → false) ∧ (∀ a b : G, (a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) ∧ (∀ a : G, a ∈ A ∨ a ∈ B) ∧ (∀ a : G, (a ∈ A ∧ a ∈ B) → false) ∧ (∀ a b : G, (a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) ∧ (∀ a b : G, (a ∈ A ∧ a ∈ A) ∨ (b ∈ B ∧ b ∈ B) → false) ∧ (∀ a b : G, (a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)), from by auto using [h3],

  -- Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$.
  have h5 : bipartite G → ∃ A B : set G, (∀ a : G, a ∈ A ∨ a ∈ B) ∧ (∀ a : G, (a ∈ A ∧ a ∈ B) → false) ∧ (∀ a b : G, (a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)), from by auto using [bipartite.def],

  -- Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable.
  have h6 : bipartite G → two_colorable G, from by auto using [h5],

  -- We have proved our theorem
  show bipartite G ↔ two_colorable G, from by auto [h4, h6],
end

/- FEW SHOT PROMPTS TO CODEX(START)
/--`theorem`
Power Set is Closed under Intersection
Let $S$ be a set.

Let $\powerset S$ be the power set of $S$.


Then:
:$\forall A, B \in \powerset S: A \cap B \in \powerset S$
`proof`
Let $A, B \in \powerset S$.

Then by the definition of power set, $A \subseteq S$ and $B \subseteq S$.

From Intersection is Subset we have that $A \cap B \subseteq A$.

It follows from Subset Relation is Transitive that $A \cap B \subseteq S$.

Thus $A \cap B \in \powerset S$ and closure is proved.
{{qed}}
-/
theorem power_set_intersection_closed {α : Type*} (S : set α) : ∀ A B ∈ 𝒫 S, (A ∩ B) ∈ 𝒫 S :=
begin
  -- $A$ and $B$ are sets. $A$ and $B$ belong to power set of $S$
  assume (A : set α) (hA : A ∈ 𝒫 S) (B : set α) (hB : B ∈ 𝒫 S),
  -- Then $A ⊆ S$ and $B ⊆ S$, by power set definition
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from by auto [set.subset_of_mem_powerset, set.subset_of_mem_powerset],
  -- Then $(A ∩ B) ⊆ A$, by intersection of set is a subset
  have h2 : (A ∩ B) ⊆ A, from by auto [set.inter_subset_left],
  -- Then $(A ∩ B) ⊆ S$, by subset relation is transitive 
  have h3 : (A ∩ B) ⊆ S, from by auto [set.subset.trans],
  -- Hence $(A ∩ B) ∈  𝒫 S$, by power set definition
  show (A ∩ B) ∈  𝒫 S, from by auto [set.mem_powerset],
end

/--`theorem`
Square of Sum
 :$\forall x, y \in \R: \paren {x + y}^2 = x^2 + 2 x y + y^2$
`proof`
Follows from the distribution of multiplication over addition:

{{begin-eqn}}
{{eqn | l = \left({x + y}\right)^2
      | r = \left({x + y}\right) \cdot \left({x + y}\right)
}}
{{eqn | r = x \cdot \left({x + y}\right) + y \cdot \left({x + y}\right)
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = x \cdot x + x \cdot y + y \cdot x + y \cdot y
      | c = Real Multiplication Distributes over Addition
}}
{{eqn | r = x^2 + 2xy + y^2
      | c = 
}}
{{end-eqn}}
{{qed}}
-/
theorem square_of_sum (x y : ℝ) : (x + y)^2 = (x^2 + 2*x*y + y^2) := 
begin
  -- expand the power
  calc (x + y)^2 = (x+y)*(x+y) : by auto [sq]
  -- distributive property of multiplication over addition gives:
  ... = x*(x+y) + y*(x+y) : by auto [add_mul]
  -- applying the above property further gives:
  ... = x*x + x*y + y*x + y*y : by auto [mul_comm, add_mul] using [ring]
  -- rearranging the terms using commutativity and adding gives:
  ... = x^2 + 2*x*y + y^2 : by auto [sq, mul_comm] using [ring]
end

/--`theorem`
Identity of Group is Unique
Let $\struct {G, \circ}$ be a group. Then there is a unique identity element $e \in G$.
`proof`
From Group has Latin Square Property, there exists a unique $x \in G$ such that:
:$a x = b$

and there exists a unique $y \in G$ such that:
:$y a = b$

Setting $b = a$, this becomes:

There exists a unique $x \in G$ such that:
:$a x = a$

and there exists a unique $y \in G$ such that:
:$y a = a$

These $x$ and $y$ are both $e$, by definition of identity element.
{{qed}}
-/
theorem group_identity_unique {G : Type*} [group G] : ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a :=
begin
  -- Group has Latin Square Property
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from by auto using [use (a⁻¹ * b)],
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from by auto using [use b * a⁻¹], 

  -- Setting $b = a$, this becomes:
  have h3 : ∀ a : G, ∃! x : G, a * x = a, from by auto [h1],
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from by auto [h2],

  -- These $x$ and $y$ are both $(1 : G)$, by definition of identity element
  have h5 : ∀ a : G, classical.some (h3 a).exists = (1 : G), from by auto [exists_unique.unique, h3, classical.some_spec, exists_unique.exists, mul_one],
  have h6 : ∀ a : G, classical.some (h4 a).exists = (1 : G), from by auto [exists_unique.unique, h4, classical.some_spec, exists_unique.exists, one_mul],

  show ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a, from by auto [h3, h4, exists_unique.unique, classical.some_spec, exists_unique.exists] using [use (1 : G)],
end

/--`theorem`
Bipartite Graph is two colorable
Let $G$ be a graph. Then $G$ is 2-colorable if and only if $G$ is bipartite.
`proof`
Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color. Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue. Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$. This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.

Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$. Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable.

QED

-/
theorem 
FEW SHOT PROMPTS TO CODEX(END)-/
