Module Type Sets.

Parameter set : Type.

Axiom excluded_middle : forall (P : Prop), P \/ ~P.

Parameter elem : set -> set -> Prop.

Definition subset (x y : set) := forall (z : set), elem z x -> elem z y.

Inductive formula : Type :=
  | Eq : set -> set -> formula
  | In : set -> set -> formula
  | Neg : formula -> formula
  | And : formula -> formula -> formula
  | Or : formula -> formula -> formula
  | Forall : (set -> formula) -> formula
  | Exists : (set -> formula) -> formula.

Notation "x 'is' 'a' 'subset' 'of' y" := (subset x y) (at level 70).
Notation "x 'is' 'in' y" := (elem x y) (at level 30, no associativity).
Notation "'there' 'is' 'some' s 'so' 'that' P" := (exists (s : set), P) (at level 60).
Notation "'for' 'any' s 'holds' P" := (forall (s : set), P) (at level 60).

Notation "'there' 'is' 'some' s 'in' x 'so' 'that' P" := (exists (s : set), s is in x /\ P) (at level 60).
Notation "'for' 'any' s 'in' x 'holds' P" := (forall (s : set), s is in x -> P) (at level 60).

Lemma iff_forward : 
  forall {P1 P2 : Prop}, (P1 <-> P2) -> P1 -> P2.
Proof.
intuition.
Qed.

Lemma iff_backward :
  forall {P1 P2 : Prop}, (P1 <-> P2) -> P2 -> P1.
Proof.
intuition.
Qed.

Ltac prove := 
  intuition;
  try congruence;
  intuition.

Tactic Notation "iff" uconstr(expr) "forward" "given" uconstr(H) :=
  pose proof iff_forward expr H.

Tactic Notation "iff" uconstr(expr) "backward" "given" uconstr(H) :=
  pose proof iff_backward expr H.

Tactic Notation "iff" uconstr(expr) "given" uconstr(H) :=
  iff expr forward given H ||
  iff expr backward given H.

Tactic Notation "iff" uconstr(expr) :=
  match goal with
  | H : _ |- _ => iff expr given H (* Try every hypothesis to see if we can generate additional facts *)
  end.

Tactic Notation "follows" "from" tactic(tac) :=
  tac; prove.

Tactic Notation "disjunc" tactic(tac) :=
  (left; tac; prove) || (right; tac; prove).

Tactic Notation "sufficient" "to" "show" constr(expr) "because" tactic(tac) :=
  cut expr; only 1 : (prove; tac; prove).

Tactic Notation "sufficient" "to" "show" constr(expr) :=
  sufficient to show expr because idtac.

Parameter existence : set.
Parameter extensionality :
  forall (a b : set),
    ( forall (z : set), z is in a <-> z is in b ) <-> a = b.
Parameter pairing : set -> set -> set.

Notation "{ a , b }" := (pairing a b).

Parameter pairing_prop :
  forall (a b : set),
    forall (w : set), w is in {a,b} <-> (w = a \/ w = b).

Lemma left_in_pairing :
  forall (a b : set), a is in {a,b}.
Proof.
intros a b.
follows from (pose proof pairing_prop a b a).
Qed.

Lemma right_in_pairing :
  forall (a b : set), b is in {a,b}.
Proof.
intros a b.
follows from (pose proof pairing_prop a b b).
Qed.

Parameter union : set -> set.
Parameter union_prop : 
  forall (c : set),
    forall (x : set), (x is in union c <-> (there is some s so that (s is in c /\ x is in s))).
Parameter powerset : set -> set.
Parameter powerset_prop :
  forall (x : set), forall (y : set), y is in powerset x <-> y is a subset of x.
Parameter comprehension : forall (x : set) (P : set -> Prop), set.

Notation "'for' x 'in' y , P" := (forall (x : set), x is in y -> P) (at level 70).
Notation "{ x ; P }" := (comprehension x P) (no associativity).
Notation "{ y 'in' x ; P }" := (comprehension x (fun y => P)).

Parameter comprehension_prop :
  forall (P : set -> Prop),
    forall (x z : set), z is in { x ; P } <-> (z is in x /\ P z).

Definition emptyset : set := { x in existence ; x <> x }.

Lemma elem_comprehension : 
  forall {P : set -> Prop} {x z : set}, z is in { x ; P } -> P z.
Proof.
intros.
follows from (iff (comprehension_prop P x z) given H).
Qed.

Tactic Notation "use" "comprehension" "for" uconstr(v) :=
  pose proof elem_comprehension v.

Tactic Notation "contradiction" "by" tactic(tac) :=
  tac; prove; contradiction.

Lemma emptyset_is_empty : forall (z : set), ~(z is in emptyset).
Proof.
intros z zinemptyset.
contradiction by (use comprehension for zinemptyset).
Qed.

Notation "'U' C" := (union C) (at level 70).

(* Note: The following are both useful helpers and also proofs that such sets exist *)
Definition pair_union (a b : set) : set := U {a,b}.
Definition singleton (a : set) : set := {a,a}.

Notation "a 'U' b" := (pair_union a b) (at level 80).

Lemma in_pair_union_forward :
  forall (a b c : set), c is in (a U b) -> c is in a \/ c is in b.
Proof.
intros.
unfold pair_union.
iff (union_prop (pairing a b) c).
destruct H0; destruct H0.
iff (pairing_prop a b x).
inversion H2.
follows from (left; rewrite <- H3).
follows from (right; rewrite <- H3).
Qed.

Lemma in_pair_union_backward :
  forall (a b c : set), c is in a \/ c is in b -> c is in (a U b).
Proof.
intros.
unfold pair_union.
intros.

cut (there is some s so that (s is in pairing a b /\ c is in s)).
intro.
follows from (iff (union_prop (pairing a b) c)).

inversion H.
- follows from (exists a; split; apply left_in_pairing || intuition).
- follows from (exists b; split; apply right_in_pairing || intuition).
Qed.

Lemma pair_union_prop :
  forall {a b c : set}, c is in (a U b) <-> c is in a \/ c is in b.
Proof.
intros.
follows from (split; apply in_pair_union_forward || apply in_pair_union_backward).
Qed.

Lemma in_singleton : forall (x : set), x is in singleton x.
Proof.
intros.
follows from (unfold singleton; apply pairing_prop).
Qed.

Lemma singleton_contains_unique : forall {x y : set}, x is in singleton y <-> x = y.
Proof.
intros.
split.
- follows from (intros; iff (pairing_prop y y x)).
- follows from (intro Eq; rewrite Eq; pose proof pairing_prop y y y).
Qed.

Lemma singleton_eq : forall {x y : set}, singleton x = singleton y <-> x = y.
Proof.
intros.
split.
- intros.
follows from (apply singleton_contains_unique; rewrite <- H; apply in_singleton).
- intros. 
follows from (rewrite H).
Qed.

Definition successor (x : set) := x U (singleton x).

Parameter infinity : set.
Parameter infinity_prop :
  elem emptyset infinity /\ (forall (n : set), successor n is in infinity).

Lemma both_include_eq : 
  forall (x y : set), x is a subset of y -> y is a subset of x -> x = y.
Proof.
intros x y x_sub_y y_sub_x.
apply extensionality.
split.
- apply x_sub_y.
- apply y_sub_x.
Qed.

Definition nonempty (x : set) := there is some y so that y is in x.

Parameter foundation :
  forall (x : set),
    nonempty x ->
      there is some y so that (y is in x /\ ~(there is some z so that (z is in x /\ z is in y))).

Notation "'there' 'is' 'unique' s 'so' 'that' P" := (
  there is some s so that (P s /\ forall (x : set), P x -> x = s)) (at level 70).

Definition function_formula (x : set) (P : set -> set -> Prop) :=
  forall (z : set), z is in x -> (there is unique y so that P z).

Parameter replacement : set -> (set -> set -> Prop) -> set.
Parameter replacement_prop :
  forall (x : set) (P : set -> set -> Prop), 
    function_formula x P -> 
        forall (z : set), z is in x -> (
          there is some w so that (w is in (replacement x P) /\ P z w)).

Definition intersection (c : set) : set := { y in U c ; for s in c, y is in s }.

Definition ordered_pair (x y : set) := {singleton x, {x, y}}.

Notation "( x , y )" := (ordered_pair x y) (no associativity).

Lemma elem_dif_set_dif :
  forall (x y : set), 
    (there is some z so that (z is in x /\ ~(z is in y))) -> x <> y.
Proof.
intros.
destruct H; destruct H.
intros x_eq_y.
iff (extensionality x y) given x_eq_y.
contradiction by (pose proof H1 x0).
Qed.

Lemma singleton_in_ordered_pair :
  forall {x y : set}, singleton x is in (x, y).
Proof.
intros.
follows from (apply left_in_pairing).
Qed.

Lemma pairing_in_ordered_pair :
  forall {x y : set}, {x, y} is in (x, y).
Proof.
intros.
follows from (apply right_in_pairing).
Qed.

Lemma pairing_is_singleton_eq :
  forall {x y : set}, singleton x = {x,y} <-> x = y.
Proof.
intros.
split.
- intros.
pose proof right_in_pairing x y as y_in_pairing.
follows from (rewrite <- H in y_in_pairing; pose proof (@singleton_contains_unique y x)).
- intros.
follows from (rewrite H).
Qed.

Lemma pairing_commutes :
  forall {x y : set}, {x,y} = {y,x}.
Proof.
intros x y.
apply extensionality.
intros z.
split; intros H; follows from (apply pairing_prop; apply pairing_prop in H).
Qed.

Lemma singleton_is_pair_then_pair_same :
  forall (x y z : set), singleton x = {y,z} <-> x = y /\ y = z.
Proof.
intros.
split.
- intros.
pose proof in_singleton x as is_in_sing_x.
rewrite H in is_in_sing_x.
apply pairing_prop in is_in_sing_x.
inversion is_in_sing_x.
rewrite H0 in H; follows from (iff (@pairing_is_singleton_eq y z)).
rewrite H0, pairing_commutes in H; follows from (iff (@pairing_is_singleton_eq z y)).
- intros.
intuition.
follows from (rewrite H0, H1; apply pairing_is_singleton_eq).
Qed.

Lemma ordered_pair_unique_pairing :
  forall (a b c d : set), {a,b} is in (c, d) -> a = b \/ {a,b} = {c,d}.
Proof.
intros.
apply pairing_prop in H.
inversion H.
left.
follows from (symmetry in H0; iff (singleton_is_pair_then_pair_same c a b)).
follows from right.
Qed.

Lemma in_in_col_in_union :
  forall (a b c : set), a is in b -> b is in c -> a is in U c.
Proof.
intros a b c a_in_b b_in_c.
pose proof union_prop c a.
sufficient to show (there is some s so that (s is in c /\ a is in s)).
follows from (exists b).
Qed.

Lemma in_col_is_subset_of_union :
  forall (a c : set), a is in c -> a is a subset of U c.
Proof.
intros.
unfold subset.
intros.
follows from (apply (in_in_col_in_union z a c)).
Qed.

Lemma singleton_subset_is_elem :
  forall (a b : set), singleton a is a subset of b -> a is in b.
Proof.
intros.
follows from (pose proof H a (in_singleton a)).
Qed.

Lemma ordered_pair_contains_one_singleton :
  forall (x y z : set), singleton x is in (y,z) -> x = y.
Proof.
intros.
apply pairing_prop in H.
inversion H.
- follows from (iff singleton_eq given H0).
- sufficient to show (singleton x = singleton y) because 
    (repeat (follows from (iff (@singleton_eq x y)))).
follows from (apply singleton_is_pair_then_pair_same in H0).
Qed.

Lemma ordered_pair_is_ordered :
  forall {x y : set}, (x, y) = (y, x) -> x = y.
Proof.
intros x y pair_eq.
iff (extensionality (x,y) (y,x)) given pair_eq.

iff (H (singleton x)) given (left_in_pairing (singleton x) (pairing x y)).
apply pairing_prop in H0.

destruct H0.
- follows from (apply singleton_eq).
- follows from (apply pairing_is_singleton_eq; rewrite pairing_commutes).
Qed.

Lemma ordered_pair_same :
  forall {a : set}, (a, a) = singleton (singleton a).
Proof.
intuition.
Qed.

Lemma pairing_eq :
  forall (a b c d : set), {a,b} = {c,d} -> (a = c /\ b = d) \/ (a = d /\ b = c).
Proof.
intros.
pose proof left_in_pairing a b.
pose proof right_in_pairing a b.
rewrite H in H0, H1.
apply pairing_prop in H0.
apply pairing_prop in H1.

inversion H0.

inversion H1.
left.
prove.
rewrite H2, H3 in H.
follows from (iff (@pairing_is_singleton_eq c d)).

prove.

inversion H1.
right. prove.
rewrite H2, H3, (@pairing_commutes c d) in H.
follows from (right; iff (@pairing_is_singleton_eq d c)).
Qed.

Lemma ordered_pair_equality :
  forall (a b c d : set), (a, b) = (c, d) -> a = c /\ b = d.
Proof.
intros.
pose proof iff_backward (extensionality (a,b) (c,d)) H.
split.
-
pose proof iff_forward (H0 (singleton a)) singleton_in_ordered_pair as sing_a_in_cd.
pose proof in_col_is_subset_of_union (singleton a) (c,d) sing_a_in_cd.
apply singleton_subset_is_elem, pair_union_prop in H1.
inversion H1.
follows from (apply singleton_contains_unique in H2).
apply pairing_prop in H2.
inversion H2.
prove.
rewrite H3 in sing_a_in_cd.
apply pairing_prop in sing_a_in_cd.
inversion sing_a_in_cd.
follows from (iff singleton_eq given H4).
rewrite pairing_commutes in H4.
follows from (iff pairing_is_singleton_eq given H4).
-
pose proof iff_forward (H0 (pairing a b)) pairing_in_ordered_pair.
apply ordered_pair_unique_pairing in H1.
inversion H1.
rewrite H2, ordered_pair_same in H.
pose proof @singleton_in_ordered_pair c d.
rewrite <- H in H3.
apply singleton_contains_unique in H3.
iff singleton_eq given H3.
pose proof @pairing_in_ordered_pair c d.
rewrite <- H in H5.
apply pairing_prop in H5.
inversion H5; pose proof singleton_is_pair_then_pair_same b c d; follows from (symmetry in H6).
apply pairing_eq in H2.
inversion H2; prove.
rewrite H2, H6 in H.
apply ordered_pair_is_ordered in H.
prove.
Qed.

Definition cart_prod_formula (X Y : set) (p : set) : Prop := 
  there is some x in X so that (there is some y in Y so that (p = (x,y))).
Definition cart_prod (X Y : set) : set :=
  { p in powerset (powerset (X U Y)) ; cart_prod_formula X Y p}.

Lemma cart_prod_base_set_prop :
  forall {X Y x y : set}, x is in X -> y is in Y -> (x,y) is in powerset (powerset (X U Y)).
Proof.
intros X Y x y x_in_X y_in_Y.
apply powerset_prop.
unfold subset.
intros z z_in_pair.
apply powerset_prop.
unfold subset.
intros w w_in_z.
apply pair_union_prop.

apply pairing_prop in z_in_pair.
inversion z_in_pair.
- rewrite H in w_in_z.
follows from (left; iff singleton_contains_unique given w_in_z).

- rewrite H in w_in_z.
apply pairing_prop in w_in_z.
inversion w_in_z.
follows from left.
follows from right.
Qed.

Lemma cart_prod_formula_holds :
  forall {X Y x y : set}, x is in X -> y is in Y -> cart_prod_formula X Y (x,y).
Proof.
intros X Y x y x_in_X y_in_Y.
exists x; prove.
exists y; prove.
Qed.

Tactic Notation "use" "both" tactic(tac1) "and" tactic(tac2) :=
  progress (split; ((tac1; prove) || (tac2; prove))).

Lemma cart_prod_prop_subset :
  forall {X Y x y : set}, x is in X -> y is in Y -> (x,y) is in cart_prod X Y.
Proof.
intros X Y x y x_in_X y_in_Y.
sufficient to show (cart_prod_formula X Y (x,y)) because (
  apply comprehension_prop;
  use both (apply cart_prod_base_set_prop) and (apply cart_prod_formula_holds)
).
follows from (apply cart_prod_formula_holds).
Qed.

Tactic Notation "follows" "by" uconstr(expr) "in" ident(H) :=
  follows from (apply expr in H).

Tactic Notation "follows" "by" uconstr(expr) :=
  follows from (apply expr) ||
  match goal with
  | H : _ |- _ => follows by expr in H
  end.

Lemma cart_prod_prop_supset :
  forall {X Y x y : set}, (x,y) is in cart_prod X Y -> x is in X /\ y is in Y.
Proof.
intros X Y x y xy_in_prod.
use comprehension for xy_in_prod; simpl in H.
repeat destruct H; repeat destruct H0.
follows by ordered_pair_equality.
Qed.

Lemma cart_prod_set :
  forall {X Y x y : set}, (x,y) is in cart_prod X Y <-> x is in X /\ y is in Y.
Proof.
intros.
split.
- apply cart_prod_prop_supset.
- intros; follows by cart_prod_prop_subset.
Qed.

End Sets.
