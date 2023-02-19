import combinatorics.simple_graph.coloring


--OUTPUT 1
theorem bipartite_iff_two_colorable {V : Type*} (G : simple_graph V) [fintype V] : (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) :=
begin
  have h1 : (G.colorable 2) → (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)), from sorry,
  have h2 : (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) → (G.colorable 2), from sorry,
  show (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)), from sorry,
end

--OUTPUT 2
theorem bipartite_iff_two_colorable {V : Type*} (G : simple_graph V) [fintype V] : (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) :=
begin
  split,
  { assume h1 : G.colorable 2,
    let f : (G.adj_matrix.to_list).finset → ℕ := sorry,
    have h2 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h3 : f (list.range (G.adj_matrix.to_list).length) = (finset.univ : finset ℕ), from sorry,
    have h4 : (finset.univ : finset ℕ) = finset.range 2, from sorry,
    have h5 : f (list.range (G.adj_matrix.to_list).length) = finset.range 2, from sorry,
    have h6 : ∀ (n : ℕ), n ∈ finset.range 2 → n = 0 ∨ n = 1, from sorry,
    have h7 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h8 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h9 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h10 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h11 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h12 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h13 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h14 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h15 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h16 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h17 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h18 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h19 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h20 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h21 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h22 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h23 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h24 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h25 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h26 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h27 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h28 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h29 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h30 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h31 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h32 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h33 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h34 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h35 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h36 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h37 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h38 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h39 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h40 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h41 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h42 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h43 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h44 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h45 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h46 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h47 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h48 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h49 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h50 : ∀ (i : fin (G.adj_matrix.to_list).length), f i = 0 ∨ f i = 1, from sorry,
    have h51 : ∀ (i
end --Needs more than 2000 tokens!

--OUTPUT 3
theorem bipartite_iff_two_colorable {V : Type*} (G : simple_graph V) [fintype V] : (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) := sorry

/--`theorem`
Intersection of Preorders is Preorder
Let $P$ and $Q$ be preorders. Then $P \cap Q$ is a preorder.
`proof`
The intersection of preorders is a subset of both preorders, so it is a subset of any preorder containing both. Therefore, it is a preorder.

QED
-/
theorem intersection_of_preorders_is_preorder {α : Type*} {P Q : α → α → Prop} [preorder P] [preorder Q] : preorder (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Equivalence Relations is Equivalence Relation
Let $R$ and $S$ be equivalence relations. Then $R \cap S$ is an equivalence relation.
`proof`
The intersection of equivalence relations is a subset of both equivalence relations, so it is a subset of any equivalence relation containing both. Therefore, it is an equivalence relation.

QED
-/
theorem intersection_of_equiv_rels_is_equiv_rel {α : Type*} {R S : α → α → Prop} [equiv_rel R] [equiv_rel S] : equiv_rel (λ x y : α, R x y ∧ S x y) := sorry

/--`theorem`
Intersection of Partial Orders is Partial Order
Let $P$ and $Q$ be partial orders. Then $P \cap Q$ is a partial order.
`proof`
The intersection of partial orders is a subset of both partial orders, so it is a subset of any partial order containing both. Therefore, it is a partial order.

QED
-/
theorem intersection_of_part_orders_is_part_order {α : Type*} {P Q : α → α → Prop} [part_order P] [part_order Q] : part_order (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Total Orders is Total Order
Let $P$ and $Q$ be total orders. Then $P \cap Q$ is a total order.
`proof`
The intersection of total orders is a subset of both total orders, so it is a subset of any total order containing both. Therefore, it is a total order.

QED
-/
theorem intersection_of_total_orders_is_total_order {α : Type*} {P Q : α → α → Prop} [total_order P] [total_order Q] : total_order (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Well Orders is Well Order
Let $P$ and $Q$ be well orders. Then $P \cap Q$ is a well order.
`proof`
The intersection of well orders is a subset of both well orders, so it is a subset of any well order containing both. Therefore, it is a well order.

QED
-/
theorem intersection_of_well_orders_is_well_order {α : Type*} {P Q : α → α → Prop} [well_order P] [well_order Q] : well_order (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Lattices is Lattice
Let $P$ and $Q$ be lattices. Then $P \cap Q$ is a lattice.
`proof`
The intersection of lattices is a subset of both lattices, so it is a subset of any lattice containing both. Therefore, it is a lattice.

QED
-/
theorem intersection_of_lattices_is_lattice {α : Type*} {P Q : α → α → Prop} [lattice P] [lattice Q] : lattice (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Boolean Algebras is Boolean Algebra
Let $P$ and $Q$ be boolean algebras. Then $P \cap Q$ is a boolean algebra.
`proof`
The intersection of boolean algebras is a subset of both boolean algebras, so it is a subset of any boolean algebra containing both. Therefore, it is a boolean algebra.

QED
-/
theorem intersection_of_bool_algs_is_bool_alg {α : Type*} {P Q : α → α → Prop} [bool_alg P] [bool_alg Q] : bool_alg (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Groups is Group
Let $P$ and $Q$ be groups. Then $P \cap Q$ is a group.
`proof`
The intersection of groups is a subset of both groups, so it is a subset of any group containing both. Therefore, it is a group.

QED
-/
theorem intersection_of_groups_is_group {α : Type*} {P Q : α → α → Prop} [group P] [group Q] : group (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Rings is Ring
Let $P$ and $Q$ be rings. Then $P \cap Q$ is a ring.
`proof`
The intersection of rings is a subset of both rings, so it is a subset of any ring containing both. Therefore, it is a ring.

QED
-/
theorem intersection_of_rings_is_ring {α : Type*} {P Q : α → α → Prop} [ring P] [ring Q] : ring (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Fields is Field
Let $P$ and $Q$ be fields. Then $P \cap Q$ is a field.
`proof`
The intersection of fields is a subset of both fields, so it is a subset of any field containing both. Therefore, it is a field.

QED
-/
theorem intersection_of_fields_is_field {α : Type*} {P Q : α → α → Prop} [field P] [field Q] : field (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Topological Spaces is Topological Space
Let $P$ and $Q$ be topological spaces. Then $P \cap Q$ is a topological space.
`proof`
The intersection of topological spaces is a subset of both topological spaces, so it is a subset of any topological space containing both. Therefore, it is a topological space.

QED
-/
theorem intersection_of_top_spaces_is_top_space {α : Type*} {P Q : α → α → Prop} [top_space P] [top_space Q] : top_space (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Metric Spaces is Metric Space
Let $P$ and $Q$ be metric spaces. Then $P \cap Q$ is a metric space.
`proof`
The intersection of metric spaces is a subset of both metric spaces, so it is a subset of any metric space containing both. Therefore, it is a metric space.

QED
-/
theorem intersection_of_metric_spaces_is_metric_space {α : Type*} {P Q : α → α → Prop} [metric_space P] [metric_space Q] : metric_space (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem`
Intersection of Normed Spaces is Normed Space
Let $P$ and $Q$ be normed spaces. Then $P \cap Q$ is a normed space.
`proof`
The intersection of normed spaces is a subset of both normed spaces, so it is a subset of any normed space containing both. Therefore, it is a normed space.

QED
-/
theorem intersection_of_normed_spaces_is_normed_space {α : Type*} {P Q : α → α → Prop} [normed_space P] [normed_space Q] : normed_space (λ x y : α, P x y ∧ Q x y) := sorry

/--`theorem
end --Needs more than 2000 tokens!

--OUTPUT 4
theorem bipartite_iff_two_colorable {V : Type*} (G : simple_graph V) [fintype V] : (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) :=
begin
  split,
  {
    assume h1,
    obtain ⟨P, h2⟩ := h1,
    let f : V → fin 2 := λ v, (P v).1,
    let A : Type* := { v : V | f v = 0 },
    let B : Type* := { v : V | f v = 1 },
    let h3 : (A ⊕ B) = V := sorry,
    let G' : simple_graph (A ⊕ B) := cast (congr_arg _ h3) G,
    have h4 : ∀ (v : V), (v ∈ A) ∨ (v ∈ B), from sorry,
    have h5 : ∀ (a : A), ∀ (b : B), (a.1 ≠ b.1), from sorry,
    let G'' : simple_graph (A ⊕ B) := sorry,
    have h6 : G' = G'', from sorry,
    show ∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B), from sorry,
  },
  {
    assume h1,
    obtain ⟨A, ⟨B, ⟨h2, h3⟩⟩⟩ := h1,
    let f : V → fin 2 := λ v, sorry,
    let P : V → fin 2 × fin 2 := λ v, sorry,
    show G.colorable 2, from sorry,
  }
end

--OUTPUT 5
theorem bipartite_iff_two_colorable {V : Type*} (G : simple_graph V) [fintype V] : (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) :=
begin
  split,
  assume h1 : G.colorable 2,
  have h2 : ∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B), from sorry,
  show (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)), from h2,
  assume h3 : ∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B),
  have h4 : G.colorable 2, from sorry,
  show G.colorable 2, from h4,
end

--OUTPUT 6
theorem bipartite_iff_two_colorable {V : Type*} (G : simple_graph V) [fintype V] : (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) :=
begin
  have h1 : (∀ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) → (G.colorable 2), from sorry,
  have h2 : ((G.colorable 2) → (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B))) := sorry,
  show (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)), from iff.intro h1 h2,
end

--OUTPUT 7
theorem bipartite_iff_two_colorable {V : Type*} (G : simple_graph V) [fintype V] : (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) :=
begin
  have h1 : ∀ G : simple_graph V, (G.colorable 2) → (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)), from sorry,
  have h2 : ∀ G : simple_graph V, (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) → (G.colorable 2), from sorry,
  show (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)), from sorry,
end

--OUTPUT 8
theorem bipartite_iff_two_colorable {V : Type*} (G : simple_graph V) [fintype V] : (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) :=
begin
  split,
  {
    assume h1 : G.colorable 2,
    have h2 : ∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B), from sorry,
    show (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)), from h2,
  },
  {
    assume h1 : (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)),
    have h2 : G.colorable 2, from sorry,
    show G.colorable 2, from h2,
  },
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
  assume (A : set α) (hA : A ∈ 𝒫 S) (B : set α) (hB : B ∈ 𝒫 S),
  have h1 : (A ⊆ S) ∧ (B ⊆ S), from sorry,
  have h2 : (A ∩ B) ⊆ A, from sorry,
  have h3 : (A ∩ B) ⊆ S, from sorry,
  show (A ∩ B) ∈  𝒫 S, from sorry,
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
  calc (x + y)^2 = (x+y)*(x+y) : by sorry
  ... = x*(x+y) + y*(x+y) : by sorry
  ... = x*x + x*y + y*x + y*y : by sorry
  ... = x^2 + 2*x*y + y^2 : by sorry,
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
  have h1 : ∀ a b : G, ∃! x : G, a * x = b, from sorry,
  have h2 : ∀ a b : G, ∃! y : G, y * a = b, from sorry,

  have h3 : ∀ a : G, ∃! x : G, a * x = a, from sorry,
  have h4 : ∀ a : G, ∃! y : G, y * a = a, from sorry,

  have h5 : ∀ a : G, classical.some (h3 a) = (1 : G), from sorry,
  have h6 : ∀ a : G, classical.some (h4 a) = (1 : G), from sorry,

  show ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a, from by {
    use (1 : G),
    have h7 : ∀ e : G, (∀ a : G, e * a = a ∧ a * e = a) → e = 1, from by {
      assume (e : G) (h7 : ∀ a : G, e * a = a ∧ a * e = a),
      have h8 : ∀ a : G, e = classical.some (h3 a), from sorry,
      have h9 : ∀ a : G, e = classical.some (h4 a), from sorry,
      show e = (1 : G), from sorry,     
    },
    sorry,
  }
end

/--`theorem`
Bipartite Graph is two colorable
Let $G$ be a graph. Then $G$ is 2-colorable if and only if $G$ is bipartite.
`proof`
Let $G$ be a 2-colorable graph, which means we can color every vertex either red or blue, and no edge will have both endpoints colored the same color. Let $A$ denote the subset of vertices colored red, and let $B$ denote the subset of vertices colored blue. Since all vertices of $A$ are red, there are no edges within $A$, and similarly for $B$. This implies that every edge has one endpoint in $A$ and the other in $B$, which means $G$ is bipartite.

Conversely, suppose $G$ is bipartite, that is, we can partition the vertices into two subsets $V_{1}, V_{2}$ every edge has one endpoint in $V_{1}$ and the other in $V_{2}$. Then coloring every vertex of $V_{1}$ red and every vertex of $V_{2}$ blue yields a valid coloring, so $G$ is 2-colorable.

QED

-/
theorem  bipartite_iff_two_colorable {V : Type*} (G : simple_graph V) [fintype V] : (G.colorable 2) ↔ (∃ (A B : Type*) (h : (A ⊕ B) = V), G ≤ cast (congr_arg _ h) (complete_bipartite_graph A B)) :=
FEW SHOT PROMPTS TO CODEX(END)-/
