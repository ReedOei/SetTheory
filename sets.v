Module Type Sets.

Parameter set : Type.

Axiom excluded_middle : forall (P : Prop), P \/ ~P.

Parameter elem : set -> set -> Prop.

Definition subset (x y : set) := forall (z : set), elem z x -> elem z y.

Notation "x 'is' 'a' 'subset' 'of' y" := (subset x y) (at level 70).
Notation "x 'is' 'in' y" := (elem x y) (at level 30, no associativity).
Notation "'there' 'is' 'some' s 'so' 'that' P" := (exists (s : set), P) (at level 60).
Notation "'for' 'any' s 'holds' P" := (forall (s : set), P) (at level 60).

Definition iff_forward : 
  forall {P1 P2 : Prop}, (P1 <-> P2) -> P1 -> P2.
intuition.
Defined.

Definition iff_backward :
  forall {P1 P2 : Prop}, (P1 <-> P2) -> P2 -> P1.
intuition.
Defined.

Tactic Notation "iff" uconstr(expr) "forward" "given" uconstr(H) :=
  pose proof iff_forward expr H.

Tactic Notation "iff" uconstr(expr) "backward" "given" uconstr(H) :=
  pose proof iff_backward expr H.

Tactic Notation "iff" uconstr(expr) "given" uconstr(H) :=
  (pose proof iff_forward expr H) ||
  (pose proof iff_backward expr H).

Tactic Notation "iff" uconstr(expr) :=
  match goal with
  | H : _ |- _ => iff expr given H
  end.

Tactic Notation "follows" "from" tactic(tac) :=
  tac; intuition.

Tactic Notation "disjunc" tactic(tac) :=
  (left; tac) || (right; tac).

Parameter existence : set.
Parameter extensionality :
  forall (a b : set),
    ( forall (z : set), z is in a <-> z is in b ) <-> a = b.
Parameter pairing : set -> set -> set.
Parameter pairing_prop :
  forall (a b : set),
    forall (w : set), w is in (pairing a b) <-> (w = a \/ w = b).

Lemma left_in_pairing :
  forall (a b : set), a is in pairing a b.
Proof.
intros a b.
follows from (pose proof pairing_prop a b a).
Qed.

Lemma right_in_pairing :
  forall (a b : set), b is in pairing a b.
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

Notation "{ x ; P }" := (comprehension x P) (no associativity).

Parameter comprehension_prop :
  forall (P : set -> Prop),
    forall (x z : set), z is in { x ; P } <-> (z is in x /\ P z).

Definition emptyset : set := { existence ; fun x => x <> x }.

Lemma elem_comprehension : 
  forall {P : set -> Prop} {x z : set}, z is in { x ; P } -> P z.
Proof.
intros.
follows from (iff (comprehension_prop P x z) given H).
Qed.

Tactic Notation "use" "comprehension" "for" uconstr(v) :=
  pose proof elem_comprehension v.

Tactic Notation "contradiction" "by" tactic(tac) :=
  tac; intuition; contradiction.

Lemma emptyset_is_empty : forall (z : set), ~(z is in emptyset).
Proof.
intros z zinemptyset.
contradiction by (use comprehension for zinemptyset).
Qed.

(* Note: The following are both useful helpers and also proofs that such sets exist *)
Definition pair_union (a b : set) : set := union (pairing a b).
Definition singleton (a : set) : set := pairing a a.

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

Lemma in_pair_union :
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

Lemma singleton_contains_unique : forall (x y : set), x is in singleton y <-> x = y.
Proof.
intros.
split.
- follows from (intros; iff (pairing_prop y y x)).
- follows from (intro Eq; rewrite Eq; pose proof pairing_prop y y y).
Qed.

Lemma singleton_eq : forall (x y : set), singleton x = singleton y <-> x = y.
Proof.
intros.
split.
- intros.
follows from (apply singleton_contains_unique; rewrite <- H; apply in_singleton).
- intros. 
follows from (rewrite H).
Qed.

Definition successor (x : set) := pair_union x (singleton x).

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

Definition function (x : set) (P : set -> set -> Prop) :=
  forall (z : set), z is in x -> (there is unique y so that P z).

Parameter replacement : set -> (set -> set -> Prop) -> set.
Parameter replacement_prop :
  forall (x : set) (P : set -> set -> Prop), 
    function x P -> 
        forall (z : set), z is in x -> (
          there is some w so that (w is in (replacement x P) /\ P z w)).

Notation "'for' x 'in' y , P" := (forall (x : set), x is in y -> P) (at level 70).
Notation "{ y 'in' x ; P }" := (comprehension x (fun y => P)).

Definition intersection (c : set) : set := { y in (union c) ; for s in c, y is in s }.

Definition ordered_pair (x y : set) := pairing (singleton x) (pairing x y).

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
  forall (x y : set), singleton x is in (x, y).
Proof.
intros.
follows from (apply left_in_pairing).
Qed.

Lemma pairing_is_singleton_eq :
  forall (x y : set), singleton x = pairing x y <-> x = y.
Proof.
intros.
split.
- intros.
pose proof right_in_pairing x y as y_in_pairing.
follows from (rewrite <- H in y_in_pairing; pose proof (singleton_contains_unique y x)).
- intros.
follows from (rewrite H).
Qed.

Lemma pairing_commutes :
  forall (x y : set), pairing x y = pairing y x.
Proof.
intros x y.
apply extensionality.
intros z.
split; intros H; follows from (apply pairing_prop; apply pairing_prop in H).
Qed.

Lemma ordered_pair_is_ordered :
  forall (x y : set), (x, y) = (y, x) -> x = y.
Proof.
intros x y pair_eq.
iff (extensionality (x,y) (y,x)) given pair_eq.

iff (H (singleton x)) given (left_in_pairing (singleton x) (pairing x y)).
apply pairing_prop in H0.

destruct H0.
- follows from (apply singleton_eq).
- follows from (apply pairing_is_singleton_eq; rewrite pairing_commutes).
Qed.

End Sets.
