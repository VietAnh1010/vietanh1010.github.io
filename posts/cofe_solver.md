---
title: COFE solver
date: 2026-05-13
---

We present a didactic version of the COFE solver presented in Iris.

### Assumptions

We assume extensionality of functions.

We assume the existence of a relation `dist` between two elements `x` and `y` of the same type, parameterized by a level (a natural number). This relation captures the notion of approximate equality: `x` and `y` may not be exactly equal, but they may be "approximately equal" at level `n`. The higher the level is, the more precise the approximation.

We write `x ={n}= y` to mean that `x` is related to `y` in the `dist` relation at level `n`. We assume the following properties of `dist`:
- `dist`, instantiated with a type `A` and a level `n`, is an equivalence relation:

```rocq
Instance dist_Equivalence A (n : nat) : Equivalence (@dist A n).
```

- `dist` is downward closed. If `x` is approximately equal to `y` at some high level `n`, then they should also be approximately equal at some lower level `m`. Intuitively, the approximation at level `m` is less precise than the approximation at level `n`, thus approximate equality at level `m` is less able to "distinguish" two elements:

```rocq
Axiom dist_le : forall {A} (n m : nat) (x y : A), m <= n -> x ={n}= y -> x ={m}= y.
```

- At the limit, `dist` and standard equality agree:

```rocq
Axiom eq_dist : forall {A} (x y : A), x = y <-> forall n, x ={n}= y.
```

- Extensionality of `dist`:

```rocq
Axiom dist_ext : forall {A B} (n : nat) (f g : A -> B), f ={n}= g <-> forall x, f x ={n}= g x.
```

With the relation `dist`, we define two properties on functions:
- A *non-expansive* function maps inputs that are approximately equal at some level `n` to outputs that are still approximately equal at level `n`:

```rocq
Class NonExpansive {A B} (f : A -> B) : Prop :=
  f_ne (n : nat) (x y : A) : x ={n}= y -> f x ={n}= f y.
```

- A *contractive* function maps inputs that are approximately equal at some level `n` to outputs that are approximately equal at level `S n`. For the exceptional case where the outputs are checked at level `0`, we stipulate that they are approximately equal, regardless of the inputs (there is no level before `0`):

```rocq
Class Contractive {A B} (f : A -> B) : Prop :=
  f_contractive : forall (n : nat) (x y : A), (forall m, m < n -> x ={m}= y) -> f x ={n}= f y.
```

Generalizing non-expansive and contractive to functions that accept multiple inputs (`NonExpansive2`, `NonExpansive3`, `Contractive2`) is straightforward: apply the property point-wise on each input.

Next, we assume the existence of a **profunctor** `F` that takes two types as inputs, and returns a type as output. This profunctor comes with an associated function `dimap` that lifts functions on the input types to functions on the output types:

```
Parameter F : Type -> Type -> Type.
Parameter dimap : forall {A1 A2 B1 B2}, (A2 -> A1) -> (B1 -> B2) -> F A1 B1 -> F A2 B2.
```

Note that the profunctor `F` is contravariant in its first input type, and covariant in its second input type. We can think of an object of type `F A B` as a function that consumes an `A` and produces a `B`. We further assume that `dimap` is lawful:

- `dimap` preserves identity functions:

```rocq
Axiom dimap_id : forall {A B} (m : F A B), dimap (fun x => x) (fun x => x) m = m.
```

- `dimap` preserves composition of functions:

```rocq
Axiom dimap_comp :
  forall {A1 A2 A3 B1 B2 B3}
         (f : A3 -> A2)
         (g : A2 -> A1)
         (h : B1 -> B2)
         (k : B2 -> B3)
         (m : F A1 B1),
    dimap (fun x => g (f x)) (fun x => k (h x)) m =
    dimap f k (dimap g h m).
```

We also assume that `dimap` interacts nicely with `dist`:

- `dimap` is non-expansive in all three arguments:

```rocq
Axiom dimap_NonExpansive3 : forall {A1 A2 B1 B2}, NonExpansive3 (@dimap A1 A2 B1 B2).
```

- `dimap` is contractive in the first two arguments:

```rocq
Axiom dimap_Contractive2 : forall {A1 A2 B1 B2}, Contractive2 (@dimap A1 A2 B1 B2).
```

We further assume the existence of an inhabitant of the type `F unit unit`, which will be used as a "default value" in later constructions:

```rocq
Parameter inhabitant : F unit unit.
```

### Objective

We want to find a type `T` such that `T` is isomorphic to `F T T`.

### A hierarchy of approximations

First, we build a hierarchy of types, indexed by a natural number. We start with the trivial type `unit`, and in each step, we "stack" one more layer of `F` over the current approximating type:

```rocq
Fixpoint approx (n : nat) : Type :=
  match n with
  | O => unit
  | S n' => let A := approx n' in F A A
  end.
```

This hierarchy represents a sequence of increasingly precise approximations of the solution type. The solution type is the limit of this hierarchy, which can be understood as the type of sequences in which each element lies at some approximation level and the sequence becomes increasingly precise.

### Moving up and down between approximation levels

To describe an object in the solution type, we consider a sequence `x_n : approx n`, together with a coherence condition relating consecutive levels (to ensure that the sequence becomes increasingly precise). This coherence is captured by the ability to move objects between approximation levels. Intuitively, moving up lifts an object to a higher approximation level without adding new information, while moving down brings an object to a lower approximation level and may forget some information.

Given an object `x` at some approximation level `k` (i.e., `x : approx k`), we can lift it up to the next level `S k` using the `up` function. Conversely, given an object at level `S k`, we can bring it down to the previous level `k` using the `down` function:

```rocq
Fixpoint up (k : nat) : approx k -> approx (S k) :=
  match k with
  | O => fun _ => inhabitant
  | S k' => dimap (down k') (up k')
  end
with down (k : nat) : approx (S k) -> approx k :=
  match k with
  | O => fun _ => tt
  | S k' => dimap (up k') (down k')
  end.
```

The two functions `up` and `down` are mutually recursive:
- When `k = 0`, `up` returns an object of type `approx 1 = F unit unit`. We rely on the assumption that there is an `inhabitant` of this type - we return that `inhabitant` (if we do not assume this, then we cannot return an object of type `F unit unit` and we are stuck).
- When `k = 0`, `down` must return an object of type `approx 0 = unit`. The only inhabitant of that type is `tt`.
- When `k = S k'`, `up` takes an object `x` of type `approx (S k') = F (approx k') (approx k')` and returns an object of type `approx (S (S k')) = F (approx (S k')) (approx (S k'))`. We use `dimap` with `down k'` in the first argument to adapt an `approx (S k')` into an `approx k'`, letting `x` consume it. `x` produces an `approx k'`, which we adapt back to `approx (S k')` using `dimap` with `up k'` in the second argument.

```
approx (S k') ---+----- F (approx (S k')) (approx (S k')) -----+--- approx (S k')
                  \                                           /
                   \ down k'                                 / up k'
                    \                                       /
                     +----- F (approx k') (approx k') -----+
```

- When `k = S k'`, `down` takes an object of type `approx (S (S k')) = F (approx (S k')) (approx (S k'))` and returns an object of type `approx (S k') = F (approx k') (approx k')`. We follow a similar strategy as above, *mutatis mutandis*.

```
                 +--- F (approx (S k')) (approx (S k')) ---+
                /                                           \
               / up k'                                       \ down k'
              /                                               \
approx k' ---+----------- F (approx k') (approx k') -----------+--- approx k'
```

Moving up and then moving down does not lose information, whereas moving down and then moving up again only recovers the original object approximately, up to a lower level:

```rocq
Lemma down_up (k : nat) : forall (x : approx k), down k (up k x) = x.
Lemma up_down (k : nat) : forall (x : approx (S (S k))), up (S k) (down (S k) x) ={k}= x.
```

The loss of information is reflected in the approximate equality: after a down-up trip, the resulting object is only approximately equal to the original object at a lower level `k`, compared to the original level `S (S k)`.

By iterating `up` (or `down`) `n` times, we can move an object up (or down) `n` levels:

```rocq
Fixpoint up_iter (n k : nat) (x : approx k) : approx (n + k) :=
  match n with
  | O => x
  | S n' => up (n' + k) (up_iter n' k x)
  end.

Fixpoint down_iter (n k : nat) : approx (n + k) -> approx k :=
  match n with
  | O => fun x => x
  | S n' => fun x => down_iter n' k (down (n' + k) x)
  end.
```

### Moving between arbitrary approximation levels

With `up_iter` and `down_iter`, we can move an object between arbitrary approximation levels. Given `x : approx m` and a target level `n`, we define a `shift` operation as follows:
- If `m <= n`, we move `x` up by `n - m` levels.
- Otherwise, `n < m`, and we move `x` down by `m - n` levels.

An initial attempt to define `shift` is as follows:

```rocq
Definition shift (m n : nat) (x : approx m) : approx n :=
  match le_lt_dec m n with
  | left H_le => up_iter (n - m) m x
  | right H_lt => down_iter (m - n) n x
  end.
```

If we try this, we get the following error message:

```rocq
The term "up_iter (n - m) m x" has type "approx (n - m + m)" while it is expected to have type "approx n".
```

Even though `n - m + m` and `n` are *provably equal* when `m <= n`, they are not *definitionally equal*, and thus we cannot use `up_iter (n - m) m x` as an object of type `approx n`. The same problem also happens in the second branch of the match. Therefore, we need to define a `cast` function that can cast an object of type `approx m` to an object of type `approx n` given a proof that `m = n`:

```rocq
Definition cast (m n : nat) (H_eq : m = n) (x : approx m) : approx n :=
  let 'eq_refl := H_eq in x.
```

With the `cast` function, we can fix the type error in the intended definition of `shift`. However, we need to prove some obligations about the casts, which are essentially arithmetic properties of `nat`:

```rocq
Lemma shift_obligation_1 : forall (m n : nat), m <= n -> n - m + m = n.
Lemma shift_obligation_2 (m n : nat) (H_lt : n < m) : m = m - n + n.

Definition shift (m n : nat) (x : approx m) : approx n :=
  match le_lt_dec m n with
  | left H_le => cast (n - m + m) n (shift_obligation_1 m n H_le) (up_iter (n - m) m x)
  | right H_lt => down_iter (m - n) n (cast m (m - n + n) (shift_obligation_2 m n H_lt) x)
  end.
```

### The solution type

We can now define the solution type. Let's call it `tower`:

```rocq
Record tower : Type :=
  { tower_car (k : nat) : approx k;
    down_tower (k : nat) : down k (tower_car (S k)) = tower_car k }.

Coercion tower_car : tower >-> Funclass.
```

This type formalizes our intuitions about the solution type in the previous sections: it represents a type of sequences in which each element lies at some approximation level and the sequence becomes increasingly precise, represented by the `down_tower` obligation.

Equality and approximate equality on the solution type are *defined* extensionally, point-wise on the sequence of approximations:

```rocq
Axiom tower_eq : forall (s t : tower), s = t <-> forall k, s k = t k.
Axiom tower_dist : forall (n : nat) (s t : tower), s ={n}= t <-> forall k, s k ={n}= t k.
```

The `down_tower` obligation, together with properties of `up`, `down`, `up_iter`, `down_iter`, `cast`, and `shift`, implies that any tower `t` interacts coherently with all of these functions. Intuitively, these lemmas say that moving a tower element between levels and then reading it back gives approximately the same result as reading directly at the target level:

```rocq
Lemma up_tower (t : tower) (k : nat) : up (S k) (t (S k)) ={k}= t (S (S k)).
Lemma up_iter_tower (t : tower) (n k : nat) : up_iter n (S k) (t (S k)) ={k}= t (n + S k).
Lemma down_iter_tower (t : tower) (n k : nat) : down_iter n k (t (n + k)) = t k.
Lemma cast_tower (t : tower) (m n : nat) (H_eq : m = n) : cast m n H_eq (t m) = t n.
Lemma shift_tower (t : tower) (m n : nat) : shift (S m) n (t (S m)) ={m}= t n.
```

The `down_iter_tower` and `cast_tower` lemmas are exact equalities, since moving downward and casting never add information. The `up_tower`, `up_iter_tower`, and `shift_tower` lemmas are only approximate equalities, because moving upward may not exactly recover the higher-level element.

### Operations on the solution type

With the solution type `tower` and the functions between concrete approximation levels, we define operations on objects of the `tower` type. We can embed an object at `x : approx k` (for any arbitrary `k`) into the `tower` type:

```rocq
Lemma embed_obligation (k : nat) (x : approx k) (i : nat) : down i (shift k (S i) x) = shift k i x.

Definition embed (k : nat) (x : approx k) : tower :=
  {| tower_car (i : nat) := shift k i x; down_tower := embed_obligation k x |}.
```

Given an object `t : tower`, we can project it to an object at any arbitrary approximation level `k`:

```rocq
Definition proj (k : nat) (t : tower) : approx k := t k.
```

These functions `embed` and `proj` allow us to move between the solution type `tower` and the approximation types `approx k`. They satisfy some properties that we will use later:

```rocq
Lemma embed_up (k : nat) (x : approx k) : embed (S k) (up k x) = embed k x.
Lemma down_proj (k : nat) (t : tower) : down k (proj (S k) t) = proj k t.
Lemma embed_proj (k : nat) (t : tower) : embed (S k) (proj (S k) t) ={k}= t.
```

### The `roll` function

Given `embed` and `proj`, the `roll` function is not difficult to define. Given an object `m : F tower tower`, we build a tower as a sequence in which for each index `k`, we use `dimap`, `embed` and `proj` to transform `m` into an object of type `F (approx k) (approx k) = approx (S k)`, and then we apply `down` on that object to obtain an approximation at level `k`.

```rocq
Lemma roll_obligation (m : F tower tower) (k : nat) :
  down k (down (S k) (dimap (embed (S k)) (proj (S k)) m)) =
  down k (dimap (embed k) (proj k) m).

Definition roll (m : F tower tower) : tower :=
  {| tower_car (k : nat) := down k (dimap (embed k) (proj k) m); down_tower := roll_obligation m |}.
```

A single `approx k` produced by the `roll` function can be visualized as follows:

```
                +----------- F tower tower -----------+
               /                                       \
              / embed k                                 \ proj k
             /                                           \
approx k ---+---------- F (approx k) (approx k) ----------+--- approx k
                                    |
                                    | down k
                                    v
                                 approx k
```

### The `unroll` function

Like `roll`, the `unroll` function is also defined using `embed` and `proj`. However, defining `unroll` is more complex than `roll`, requiring additional machinery. First, we present a simple but incorrect definition to illustrate the problem. Then, we introduce the concepts of chains and completeness to solve it, and finally provide a correct definition of `unroll` using these concepts.

#### A simple but incorrect definition

The `unroll` function is harder to define. At first glance, one might attempt to define it as follows:

```rocq
(* This is a placeholder, we will later see that the choice of `n` does not matter *)
Definition n : nat := 10.

Definition unroll (t : tower) : F tower tower :=
  dimap (proj n) (embed n) (t (S n)).
```

This definition passes the type checker, but it is semantically incorrect because it loses information. Intuitively, this version of `unroll` produces an object of type `F tower tower` that takes a tower, projects it to some approximation level `n`, operates at that level, and then embeds the result back into a tower. However, if the input tower contains information at levels higher than `n`, `proj n` discards it, leading to information loss. Regardless of the chosen `n`, this approach is unsatisfactory, as it always loses information at levels `S n` and above.

#### Toward a correct definition: chains and completeness

We need more machinery to define the `unroll` function. We introduce the concepts of `chain` and `Complete`. A `chain` of type `A` is a sequence of elements of `A` that become increasingly precise as the index increases, which is captured by the `cauchy` obligation:

```rocq
Record chain (A : Type) : Type :=
  { chain_car : nat -> A;
    cauchy (n i : nat) : n <= i -> chain_car i ={n}= chain_car n }.
```

Even though elements in a chain become increasingly precise, they may not converge to a limit. A type `A` is *complete* if every chain of type `A` has a limit. The limit of a chain `c` is approximately equal to every element `c n` in the chain at level `n`, which is captured by the `compl_conv` obligation:

```rocq
Class Complete A : Type :=
  { compl : chain A -> A;
    compl_conv (n : nat) (c : chain A) : compl c ={n}= c n }.
```

As an example, a chain on `unit` is complete, because there is only one inhabitant of `unit`, namely `tt`, so the limit of any chain on `unit` is just `tt`:

```rocq
Lemma unit_Complete_obligation (n : nat) (c : chain unit) : tt ={n}= c n.

Instance unit_Complete : Complete unit :=
  {| compl _ := tt; compl_conv := unit_Complete_obligation |}.
```

With chains and completeness, the idea is to first generate a chain of `F tower tower` from a given tower, then take its limit. This avoids information loss: rather than projecting the tower to a predetermined approximation level, we generate a chain of `F tower tower`, where each element approximates the desired result. The limit of this chain will be the result we expect, with no information lost, since it captures information from all approximation levels.

#### An extra assumption

Since `tower` is defined using `approx`, which is defined using `F`, we need properties of `F` regarding `Complete` to conclude that `tower` and `F tower tower` are complete. We must assume that `F` preserves completeness:

```rocq
Parameter F_Complete : forall A, Complete A -> Complete (F A A).
Existing Instance F_Complete.
```

Without this assumption, we have no way to show that the `tower` type is complete, so we cannot define `unroll` using the limit of a chain of `F tower tower`.

#### A correct definition

With the assumption `F_Complete`, we can first show that each approximation level `approx n` is complete, by structural induction on `n`:

```rocq
Fixpoint approx_Complete (k : nat) : Complete (approx k) :=
  match k with
  | O => unit_Complete
  | S k' => F_Complete (approx k') (approx_Complete k')
  end.

Existing Instance approx_Complete.
```

We then show that `tower` is complete using the completeness of each approximation level. Given a chain `c : chain tower`, we can construct a limit tower. At each approximation level `k`, we form a chain of `approx k` by projecting each tower in the original chain `c` to that level:

```rocq
Lemma tower_chain_obligation (c : chain tower) (k n i : nat) (H_le : n <= i) : c i k ={n}= c n k.
Proof. exact (proj1 (tower_dist n (c i) (c n)) (cauchy c n i H_le) k). Qed.

Definition tower_chain (c : chain tower) (k : nat) : chain (approx k) :=
  {| chain_car (n : nat) := c n k; cauchy := tower_chain_obligation c k |}.
```

Then, we can take the limit of the chain of `approx k` to get an object of type `approx k` for each `k`, to construct a tower:

```rocq
Lemma tower_compl_obligation (c : chain tower) (k : nat) :
  down k (compl (tower_chain c (S k))) = compl (tower_chain c k).

Definition tower_compl (c : chain tower) : tower :=
  {| tower_car (k : nat) := compl (tower_chain c k); down_tower := tower_compl_obligation c |}.
```

We show that `tower_compl` is indeed the limit of the original chain `c`:

```rocq
Lemma tower_Complete_obligation (n : nat) (c : chain tower) : tower_compl c ={n}= c n.

Instance tower_Complete : Complete tower :=
  {| compl := tower_compl; compl_conv := tower_Complete_obligation |}.
```

By `tower_Complete` and the assumption `F_Complete`, we have that `F tower tower` is also complete. Now, the missing piece is to generate a chain of `F tower tower` from a given tower. Each element in the chain can be generated just like the incorrect definition of `unroll`, but instead of projecting to some predetermined approximation level, we project to the current index `i` in the chain:

```rocq
Lemma unroll_chain_obligation (t : tower) (n : nat) :
  forall (i : nat), n <= i -> dimap (proj i) (embed i) (t (S i)) ={n}= dimap (proj n) (embed n) (t (S n)).

Definition unroll_chain (t : tower) : chain (F tower tower) :=
  {| chain_car (n : nat) := dimap (proj n) (embed n) (t (S n)); cauchy := unroll_chain_obligation t |}.
```

We can now define `unroll` by taking the limit of the chain generated by `unroll_chain`:

```rocq
Definition unroll (t : tower) : F tower tower :=
  compl (unroll_chain t).
```

### Proving that `roll` and `unroll` form an isomorphism

For `roll` and `unroll` to form an isomorphism between `tower` and `F tower tower`, they must satisfy two equations.

#### The first equation

The first equation is that `roll` followed by `unroll` is the identity function on `F tower tower`:

```rocq
Lemma unroll_roll (m : F tower tower) : unroll (roll m) = m.
```

By applying `eq_dist` and unfolding `unroll`, we get:

```rocq
compl (unroll_chain (roll m)) ={n}= m
```

We replace the LHS with the `n`-th chain element using `compl_conv`, then simplify, then fuse the `dimap` applications using `dimap_comp`. We also rewrite the RHS using `dimap_id` to replace `m` with `dimap (fun x => x) (fun x => x) m`. Since both sides now share the same last argument `m`, we apply `dist_ext` to remove it. After these steps, the goal reduces to:

```rocq
dimap (fun x => embed (S n) (up n (proj n x))) (fun x => embed n (down n (proj (S n) x))) ={n}=
dimap (fun x => x) (fun x => x).
```

This goal is discharged by contractivity of `dimap`:
- If `n = 0`, the goal is trivial because at level `0`, the LHS is approximately equal to the RHS regardless of the functions involved.
- If `n = S n'`, the goal reduces to showing that `(fun x => embed (S (S n')) (up (S n') (proj (S n') x))) ={n'}= (fun x => x)` and `(fun x => embed (S n') (down (S n') (proj (S (S n')) x))) ={n'}= (fun x => x)`. Both goals follow from `dist_ext`, `embed_up`, `down_proj`, and `embed_proj`.

The original proof in Iris is slightly different: it uses `compl_conv` and `cauchy` to replace the LHS with the `S n`-th chain element instead, and then uses non-expansiveness of `dimap` to discharge the goal. That approach also works, though replacing the LHS with the `S n`-th element is a less natural first step compared to using the `n`-th element as we do here.

#### The second equation

The second equation is that `unroll` followed by `roll` is the identity function on `tower`:

```rocq
Lemma roll_unroll (t : tower) : roll (unroll t) = t.
```

By applying `eq_dist`, `tower_dist`, and unfolding `unroll`, we get:

```rocq
down k (dimap (embed k) (proj k) (compl (unroll_chain t))) ={n}= t k
```

As before, we use `compl_conv` to replace `compl (unroll_chain t)` with its `n`-th chain element `unroll_chain t n`, then simplify and fuse the `dimap` applications to obtain:

```rocq
down k (dimap (fun x => shift k n x) (fun x => shift n k x) (t (S n))) ={n}= t k
```

At this point, we need to pause and derive the following key lemma before we can continue. The lemma relates a `dimap` with `shift` arguments to a single `shift` at the next level:

```rocq
Lemma dimap_shift_shift (m n : nat) (x : approx (S n)) :
  dimap (shift m n) (shift n m) x ={n}= shift (S n) (S m) x.
```

Using this lemma, we replace the `dimap` expression with `shift (S n) (S k) (t (S n))`. The goal then follows from `shift_tower`, which replaces this with `t (S k)`, and `down_tower`, which finally gives `t k`.

#### The `dimap_shift_shift` lemma

We now look at the `dimap_shift_shift` lemma in more detail. The lemma states that applying `dimap` with `shift m n` and `shift n m` to an object `x` of type `approx (S n)` is approximately equal to applying a single `shift (S n) (S m)` to `x`. This lemma expresses the compatibility of `dimap` with the `shift` operation, and it has two main cases, depending on whether we are moving up or down (the mechanized proof has more cases, but those cases are trivial):

- If `m < n` (moving down), we need to prove that:

```rocq
dimap
  (fun x => cast (n - m + m) n (...) (up_iter (n - m) m x))
  (fun x => down_iter (n - m) m (cast n (n - m + m) (...) x)) x ={n}=
down_iter (n - m) (S m) (cast (S n) (n - m + S m) (...) x)
```

Using `dimap_comp`, we can decompose the LHS into two `dimap` applications: the outer one moves, and the inner one casts:

```rocq
dimap (up_iter (n - m) m) (down_iter (n - m) m)
  (dimap (cast (n - m + m) n (...)) (cast n (n - m + m) (...)) x) ={n}=
down_iter (n - m) (S m) (cast (S n) (n - m + S m) (...) x)
```

The outer `dimap` for moving can be simplified using the following auxiliary lemma, which states that `dimap` with `up_iter` and `down_iter` is equal to a single `down_iter` at the next level:

```rocq
Lemma dimap_up_iter_down_iter (n k : nat) :
  forall (H_eq : S (n + k) = n + S k)
         (x : approx (S (n + k))),
    dimap (up_iter n k) (down_iter n k) x =
    down_iter n (S k) (cast (S (n + k)) (n + S k) H_eq x).
```

We can illustrate this lemma with a diagram. The LHS applies `dimap` to descend into the content of `x`, then moves the content down using `up_iter`/`down_iter` on the `n + k` levels below. The RHS instead moves down `n` levels directly from the top of `x` (after a cast). Both sides end up at the same level `S k`, with the exact same result.

```
+---------+   +---------+                 <- approx (S (n + k)) ~ approx (n + S k)
|         |   |   ///   |                               |               |
+---------+   +---------+                 <- approx (n + k)             |
|   ///   |   |   ///   |                     |         |               | down_iter n (S k)
+---------+   +---------+                     +- dimap -+               |
|   ///   |   |   ///   |                     |         v               |
+---------+   +---------+   +---------+   <- approx (S k) <-------------+
|   ///   |   |         |   |         |       v
+---------+   +---------+   +---------+   <- approx k
|         |   |         |   |         |
|   ...   |   |   ...   |   |   ...   |
    LHS           RHS          output
```

The second application of `dimap` for casting can be simplified using the following auxiliary lemma, which states that `dimap` with `cast` in both arguments is equal to a single `cast` at the next level:

```rocq
Lemma dimap_cast_cast (m n : nat) (H_eq1 : m = n) (H_eq2 : n = m) (H_eq3 : S n = S m) (x : approx (S n)) :
  dimap (cast m n H_eq1) (cast n m H_eq2) x = cast (S n) (S m) H_eq3 x.
```

- If `n < m` (moving up), we need to prove that:

```rocq
dimap
  (fun x => down_iter (m - n) n (cast m (m - n + n) (...) x))
  (fun x => cast (m - n + n) m (...) (up_iter (m - n) n x)) x ={n}=
cast (m - n + S n) (S m) (...) (up_iter (m - n) (S n) x)
```

Using `dimap_comp`, we can decompose the LHS into two `dimap` applications: the outer one casts, and the inner one moves (rather than the other way around as in the previous case):

```rocq
dimap (cast m (m - n + n) (...)) (cast (m - n + n) m (...))
  (dimap (down_iter (m - n) n) (up_iter (m - n) n) x) ={n}=
cast (m - n + S n) (S m) (...) (up_iter (m - n) (S n) x)
```

The outer `dimap` for casting can be simplified using the `dimap_cast_cast` lemma above. We simplify the inner `dimap` for moving using another auxiliary lemma, which states that `dimap` with `down_iter` and `up_iter` is approximately equal to a single `up_iter` at the next level:

```rocq
Lemma dimap_down_iter_up_iter (n k : nat) (H_eq : n + S k = S (n + k)) (x : approx (S k)) :
  dimap (down_iter n k) (up_iter n k) x ={k}=
  cast (n + S k) (S (n + k)) H_eq (up_iter n (S k) x).
```

We again illustrate this lemma with a diagram. The LHS applies `dimap` to descend into the content of `x`, then moves the content up using `down_iter`/`up_iter` on the `k` levels below. The RHS instead moves up `n` levels directly from the top of `x`, then casts the result to avoid the type mismatch. Both sides end up at the same level `S (n + k)`, with the exact same content but only up to approximation level `k`.

```
              +---------+   +---------+   <- approx (S (n + k)) ~ approx (n + S k)
              |         |   |   ***   |                 ^               ^
              +---------+   +---------+   <- approx (n + k)             |
              |   ***   |   |   ***   |       ^         |               | up_iter n (S k)
              +---------+   +---------+       +- dimap -+               |
              |   ***   |   |   ***   |       |         |               |
+---------+   +---------+   +---------+   <- approx (S k) --------------+
|         |   |   ***   |   |         |       |
+---------+   +---------+   +---------+   <- approx k
|         |   |         |   |         |
|   ...   |   |   ...   |   |   ...   |
   input          LHS           RHS
```

### A deeper look: category theory and type theory

#### A categorical perspective on `cast`

The `cast` function was originally introduced as a technical device to fix type mismatches: given a proof that `m = n`, it coerces an element of `approx m` into an element of `approx n`. But a closer look at `cast` reveals a surprisingly elegant categorical structure, with connections to **homotopy type theory (HoTT)**.

The key insight is to think in terms of two categories:

- The **category of paths**, whose objects are natural numbers and whose morphisms from `m` to `n` are proofs of equality `m = n`. The name *paths* comes from HoTT, where equalities are interpreted as paths in a space.
- The **category of types**, whose objects are types and whose morphisms are functions between them.

Given `f g : nat -> nat`, the assignments `fun i => approx (f i)` and `fun i => approx (g i)` are functors from the category of paths to the category of types: they send each object `i` (a natural number) to a type, and they send each morphism `H_eq : m = n` to a function between types via `cast` - specifically, `cast (f m) (f n) (f_equal f H_eq)` for the functor `fun i => approx (f i)`, and similarly for `g`. This is exactly the role `cast` plays when composed with `f_equal`: it lifts a morphism in the category of paths to a morphism in the category of types.

A family `eta : forall i, approx (f i) -> approx (g i)` is then a natural transformation between the two functors, with `eta i` being the component at object `i`. Naturality says that `eta` commutes with the action of the functors on morphisms, i.e., lifting a path `H_eq : m = n` before or after applying `eta` gives the same result:

```rocq
Lemma cast_natural (f g : nat -> nat) (eta : forall i, approx (f i) -> approx (g i))
  (m n : nat) (H_eq : m = n) (x : approx (f m)) :
  cast (g m) (g n) (f_equal g H_eq) (eta m x) = eta n (cast (f m) (f n) (f_equal f H_eq) x).
```

Functions like `up` and `down` are natural transformations in this sense, and their interactions with `cast` are all instances of this naturality square.

#### UIP on `nat`

Several proofs in this development involve functions that take equality proofs of `nat` as explicit arguments: `cast` and `shift`. When reasoning equationally about such functions, one frequently needs to replace one proof with another. This is justified by the **uniqueness of identity proofs (UIP)** for `nat`:

```rocq
UIP_nat : forall (m n : nat) (H1 H2 : m = n), H1 = H2
```

In Rocq, proof irrelevance does not hold for arbitrary propositions. However, equality on `nat` is decidable, and decidable equality implies UIP (by the **Hedberg theorem**). UIP lets us treat any two proofs of the same equality `m = n` as interchangeable, so equational reasoning about `cast` and `shift` goes through without getting stuck on proof-term mismatches.

Connecting back to the previous section: the morphisms in the category of paths over `nat` are proofs of equality, and UIP says there is at most one such proof between any two natural numbers. In HoTT terms, this means `nat` is a **set** - a type whose path spaces are all mere propositions, also known as a type of **h-level 2** (where h-level 0 is a contractible type, h-level 1 is a mere proposition, and h-level 2 is a set). In categorical terms, this makes the category of paths over `nat` a **thin category** - a category where there is at most one morphism between any two objects. Readers interested in the deeper connections between type theory and category theory are encouraged to explore these concepts further.

### Resources

[The Rocq mechanization of this post](/rocq/cofe_solver.v).
