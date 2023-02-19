import combinatorics.simple_graph.coloring


--OUTPUT 1
theorem bipartite_graph_two_colorable (G : Type*) [graph G] : two_colorable G ↔ bipartite G :=
begin
  -- Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color. Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue. Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$. This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  assume h1 : two_colorable G,
  have h2 : ∃ (A B : set G), ∀ (v : G), v ∈ A ∨ v ∈ B ∧ (∀ (v1 v2 : G), v1 ∈ A ∧ v2 ∈ B → v1 -- v2 ∈ G), from by auto [h1],
  have h3 : ∀ (v1 v2 : G), v1 ∈ A ∧ v2 ∈ B → v1 -- v2 ∈ G, from by auto [h2],
  have h4 : ∀ (v1 v2 : G), v1 ∈ A ∧ v2 ∈ A → v1 -- v2 ∉ G, from by auto [h2],
  have h5 : ∀ (v1 v2 : G), v1 ∈ B ∧ v2 ∈ B → v1 -- v2 ∉ G, from by auto [h2],
  have h6 : ∀ (v1 v2 : G), v1 ∈ A ∧ v2 ∈ A → v1 -- v2 ∉ G, from by auto [h2],
  have h7 : bipartite G, from by auto [h2, h3, h4, h5, h6],

  -- Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$. Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable.
  assume h8 : bipartite G,
  have h9 : ∃ (A B : set G), ∀ (v : G), v ∈ A ∨ v ∈ B ∧ (∀ (v1 v2 : G), v1 ∈ A ∧ v2 ∈ B → v1 -- v2 ∈ G), from by auto [h8],
  have h10 : ∀ (v1 v2 : G), v1 ∈ A ∧ v2 ∈ B → v1 -- v2 ∈ G, from by auto [h9],
  have h11 : ∀ (v1 v2 : G), v1 ∈ A ∧ v2 ∈ A → v1 -- v2 ∉ G, from by auto [h9],
  have h12 : ∀ (v1 v2 : G), v1 ∈ B ∧ v2 ∈ B → v1 -- v2 ∉ G, from by auto [h9],
  have h13 : ∀ (v1 v2 : G), v1 ∈ A ∧ v2 ∈ A → v1 -- v2 ∉ G, from by auto [h9],
  have h14 : two_colorable G, from by auto [h9, h10, h11, h12, h13],

  show two_colorable G ↔ bipartite G, from by auto [h7, h14] using [iff.intro, iff.mpr],
end

--OUTPUT 2
theorem graph_2_colorable_iff_bipartite (G : Type*) [graph G] : two_colorable G ↔ bipartite G :=
begin
  -- $G$ is 2-colorable, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color.
  assume h1 : two_colorable G,
  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
  have h2 : ∃ A B : set G, ∀ v : G, (v ∈ A ∨ v ∈ B) ∧ (∀ w : G, (v, w) ∈ E G → v ∈ A → w ∈ B) ∧ (∀ w : G, (v, w) ∈ E G → v ∈ B → w ∈ A), from by auto [h1],
  -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
  have h3 : ∀ v w : G, v ∈ A ∧ w ∈ A → (v, w) ∉ E G, from by auto [h2],
  have h4 : ∀ v w : G, v ∈ B ∧ w ∈ B → (v, w) ∉ E G, from by auto [h2],
  -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  have h5 : ∀ v w : G, (v, w) ∈ E G → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A), from by auto [h2, h3, h4],
  show two_colorable G ↔ bipartite G, from by auto [two_colorable, bipartite, h2, h5],
end

--OUTPUT 3
theorem bipartite_graph_is_two_colorable {G : Type*} [graph G] : is_bipartite G ↔ is_two_colorable G :=
begin
  -- Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color.
  assume h1 : is_two_colorable G,
  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
  have h2 : ∃ A B : set (vertex G), is_red_set A ∧ is_blue_set B, from by auto using [h1],
  -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
  have h3 : ∀ a b : vertex G, a ∈ A ∧ b ∈ A → ¬ edge a b, from by auto using [h2],
  have h4 : ∀ a b : vertex G, a ∈ B ∧ b ∈ B → ¬ edge a b, from by auto using [h2],
  -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  have h5 : is_bipartite G, from by auto using [h2, h3, h4],
  show is_bipartite G ↔ is_two_colorable G, from by auto using [h1, h5],
end

--OUTPUT 4
theorem bipartite_graph_two_colorable (G : Type*) [graph G] : ∃ A B : set G, ∀ a b : G, a ∈ A ∧ b ∈ B → (a, b) ∈ G.edges :=
begin
  -- Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color.
  have h1 : ∃ (f : G → bool), ∀ a b : G, f a = tt ∧ f b = tt → (a, b) ∉ G.edges, from by auto [two_colorable],
  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
  have h2 : ∃ A : set G, ∀ a : G, a ∈ A ↔ f a = tt, from by auto [set_of_function],
  have h3 : ∃ B : set G, ∀ b : G, b ∈ B ↔ f b = ff, from by auto [set_of_function],
  -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
  have h4 : ∀ a b : G, a ∈ A ∧ b ∈ A → (a, b) ∉ G.edges, from by auto [h1, h2],
  have h5 : ∀ a b : G, a ∈ B ∧ b ∈ B → (a, b) ∉ G.edges, from by auto [h1, h3],
  -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  show ∃ A B : set G, ∀ a b : G, a ∈ A ∧ b ∈ B → (a, b) ∈ G.edges, from by auto using [h2, h3, h4, h5]
end

--OUTPUT 5
theorem two_colorable_bipartite {G : Type*} [graph G] : two_colorable G ↔ bipartite G :=
begin
  -- Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color.
  assume h1 : two_colorable G,
  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
  let A : set G := {x | color x = red},
  let B : set G := {x | color x = blue},
  -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
  have h2 : ∀ x y : G, x ∈ A ∧ y ∈ A → x ≠ y → ¬ edge x y, from by auto [h1],
  have h3 : ∀ x y : G, x ∈ B ∧ y ∈ B → x ≠ y → ¬ edge x y, from by auto [h1],
  -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  have h4 : ∀ x y : G, edge x y → (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A), from by auto [h1],
  have h5 : bipartite G, from by auto [h4],
  show two_colorable G ↔ bipartite G, from by auto [h5],

  -- Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$.
  assume h6 : bipartite G,
  -- Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable.
  have h7 : two_colorable G, from by auto [h6],
  show two_colorable G ↔ bipartite G, from by auto [h7],
end

--OUTPUT 6
theorem bipartite_graph_two_colorable {G : Type*} [graph G] : (∃ A B : set G, ∀ a : G, (a ∈ A) ∨ (a ∈ B)) ↔ (∀ a b : G, a ∈ A ∧ b ∈ B → ¬ (a -- b)) :=
begin
  -- Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color.
  have h1 : ∀ A B : set G, ∀ a : G, a ∈ A ∨ a ∈ B → (∀ b : G, b ∈ A → ¬ (a -- b)) ∧ (∀ b : G, b ∈ B → ¬ (a -- b)), from by auto using [graph.no_edge_same_color],

  -- Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue.
  have h2 : ∀ A B : set G, ∀ a : G, a ∈ A ∨ a ∈ B → ∀ b : G, b ∈ A ∧ b ∈ B → ¬ (a -- b), from by auto [h1],

  -- Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$.
  have h3 : ∀ A B : set G, ∀ a : G, a ∈ A ∨ a ∈ B → ∀ b : G, b ∈ A ∧ b ∈ B → ¬ (a -- b), from by auto [h2],

  -- This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.
  have h4 : ∀ A B : set G, ∀ a : G, a ∈ A ∨ a ∈ B → ∀ b : G, b ∈ A ∧ b ∈ B → ¬ (a -- b), from by auto [h3],

  -- Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$.
  have h5 : ∀ A B : set G, ∀ a : G, a ∈ A ∨ a ∈ B → ∀ b : G, b ∈ A ∧ b ∈ B → ¬ (a -- b), from by auto [h4],

  -- Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable.
  have h6 : ∀ A B : set G, ∀ a : G, a ∈ A ∨ a ∈ B → ∀ b : G, b ∈ A ∧ b ∈ B → ¬ (a -- b), from by auto [h5],

  -- QED
  show (∃ A B : set G, ∀ a : G, (a ∈ A) ∨ (a ∈ B)) ↔ (∀ a b : G, a ∈ A ∧ b ∈ B → ¬ (a -- b)), from by auto [h6],
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
